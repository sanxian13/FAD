package com.example;

import org.neo4j.driver.*;
import java.io.File;
import java.io.IOException;
import java.util.List;

public class Connect implements AutoCloseable {
    private final Driver driver;

    public Connect(String uri, String user, String password) {
        driver = GraphDatabase.driver(uri, AuthTokens.basic(user, password));
    }

    @Override
    public void close() {
        driver.close();
    }

    public void runCppAndImportData() throws IOException, InterruptedException {
        System.out.println(">>> Step 1: Running fad.cpp ...");

        // Step 1. 编译并运行 C++ 程序
        ProcessBuilder pb = new ProcessBuilder("cmd.exe", "/c", "g++ fad.cpp -o fad && fad.exe");
        pb.directory(new File("E:\\code\\neo4j-connect\\demo\\src"));
        pb.inheritIO();
        Process process = pb.start();
        int exitCode = process.waitFor();
        if (exitCode != 0) {
            System.err.println("C++ 程序执行失败，退出码：" + exitCode);
            return;
        }
        System.out.println("C++ 程序执行完毕。");

        // Step 2. 连接 Neo4j 并执行 Cypher 脚本
        try (Session session = driver.session()) {

            // ============ Step 2.1 导入 edges.csv 创建基础图 ============
            System.out.println(">>> Step 2.1: Loading edges.csv ...");
            session.run("""
                        LOAD CSV WITH HEADERS FROM 'file:///edges.csv' AS row
                        WITH toInteger(row.id1) AS src, toInteger(row.id2) AS dst
                        MERGE (u:Node {id: src})
                        MERGE (v:Node {id: dst})
                        MERGE (u)-[:LINK]->(v)
                    """);

            // ============ Step 2.2 显示整个图 ============
            System.out.println(">>> Step 2.2: Displaying all nodes and links ...");
            session.run("""
                        MATCH (n:Node)
                        OPTIONAL MATCH (n)-[r:LINK]->(m:Node)
                        RETURN n, r, m
                    """);

            // ============ Step 2.3 创建节点的 (k,l) 属性 ============
            System.out.println(">>> Step 2.3: Loading coreness.csv ...");
            session.run("""
                        LOAD CSV WITH HEADERS FROM 'file:///coreness.csv' AS row
                        WITH row
                        WHERE row.k IS NOT NULL AND row.l IS NOT NULL
                        MERGE (n:Node {id: toInteger(row.id)})
                        SET n.kl = coalesce(n.kl, []) + [trim(toString(row.k)) + "_" + trim(toString(row.l))]
                    """);

            // ============ Step 2.4 载入 AF.csv 并设置 anchor/follower ============
            System.out.println(">>> Step 2.4: Processing AF.csv ...");
            session.run("""
                        LOAD CSV WITH HEADERS FROM 'file:///AF.csv' AS row
                        WITH row
                        WHERE row.type CONTAINS 'anchor' OR row.type CONTAINS 'follower'
                        WITH collect(CASE WHEN row.type CONTAINS 'anchor' THEN row.id_list END)[0] AS anchorId,
                             collect(CASE WHEN row.type CONTAINS 'follower' THEN row.id_list END)[0] AS followerList
                        WITH toInteger(anchorId) AS anchorId, split(followerList, ' ') AS followers
                        MATCH (a:Node {id: anchorId})
                        SET a.role = 'anchor',
                            a.color = '#FF0000'
                        WITH a, followers
                        UNWIND followers AS fid
                        MATCH (f:Node {id: toInteger(fid)})
                        SET f.role = 'follower',
                            f.color = '#0000FF'
                        MERGE (a)-[:FOLLOW]->(f)
                        RETURN a.id AS anchor, collect(f.id) AS followers
                    """);

            // ============ Step 2.5 验证 FOLLOW 关系 ============
            System.out.println(">>> Step 2.5: Verifying FOLLOW relationships ...");
            session.run("""
                        MATCH (a:Node {role: 'anchor'})-[r:FOLLOW]->(f:Node {role: 'follower'})
                        RETURN a.id AS anchor, collect(f.id) AS followers
                    """);

            // ============ Step 2.6 查询 (1,4)-core 节点及 anchor/follower ============
            System.out.println(">>> Step 2.6: Querying 1_4-core and anchor/follower regions ...");
            Result result = session.run("""
                    MATCH (n:Node)-[r:LINK]->(m:Node)
                    WHERE "1_4" IN n.kl AND "1_4" IN m.kl
                    OR ((n.role = 'anchor' OR n.role = 'follower')
                    OR (m.role = 'anchor' OR m.role = 'follower'))
                    RETURN n.id AS source, m.id AS target
                    """);

            System.out.println(">>> Query Results:");
            while (result.hasNext()) {
                org.neo4j.driver.Record record = result.next();
                System.out.printf("(%d) -> (%d)%n",
                        record.get("source").asInt(),
                        record.get("target").asInt());
            }
            // Result result = session.run("MATCH (a:Anchor)-[:FOLLOW]->(f:Follower) RETURN
            // a.id AS A, f.id AS F");
            // List<org.neo4j.driver.Record> records = result.list();

            // System.out.println(">>> Number of Anchor-Follower relationships: " +
            // records.size());
            // for (org.neo4j.driver.Record r : records) {
            // System.out.println("Anchor " + r.get("A").asString() + " -> Follower " +
            // r.get("F").asString());
            // }

        }
    }

    public static void main(String[] args) {
        try (Connect app = new Connect("bolt://localhost:7687", "neo4j", "hhyy@hhyy")) {
            app.runCppAndImportData();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
