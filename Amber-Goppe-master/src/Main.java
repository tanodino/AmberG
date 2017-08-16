import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

import org.apache.jena.query.QueryExecution;
import org.apache.jena.query.QueryExecutionFactory;
import org.apache.jena.query.QueryFactory;
import org.apache.jena.query.QuerySolution;
import org.apache.jena.query.ResultSet;
import org.apache.jena.query.Syntax;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.util.FileManager;
import org.apache.log4j.Logger;
import org.apache.log4j.varia.NullAppender;

import data.GraphDatabase;
import query.Query;

public class Main {

	public static void main(String[] args) throws IOException {

		Logger.getRootLogger().removeAllAppenders();
		Logger.getRootLogger().addAppender(new NullAppender());

		// String databasePath = "examples/graph_pp.nt";
		// String queryPath = "examples/query_example.txt";
		String databasePath = "examples/dbpedia.nt";
		String queryPath = "examples/query4.txt";

		jenaQuery(databasePath, queryPath);
		System.out.println("======");
		testQuery(databasePath, queryPath);

	}

	public static void testQuery(String databasePath, String queryPath) throws IOException {
		GraphDatabase g = new GraphDatabase(databasePath);

		Query q = new Query(g, queryPath);

		long start = System.nanoTime();
		g.query(q);
		System.out.println("Query time : " + (System.nanoTime() - start) / 1000000 + " ms");

		// System.out.println(q.formatResults());

		System.out.println("results size: " + q.getResults().size());
	}

	public static void jenaQuery(String databasePath, String queryPath) throws IOException {

		System.out.println("\nStarting Jena Evaluation.");
		Model model = FileManager.get().loadModel(databasePath, null, "N-TRIPLES");
		String queryString = new String(Files.readAllBytes(Paths.get(queryPath)));
		org.apache.jena.query.Query query = QueryFactory.create(queryString, Syntax.syntaxARQ);
		System.out.println(query);
		long start = System.nanoTime();
		try (QueryExecution qexec = QueryExecutionFactory.create(query, model)) {
			// Planning execution, not solving
			ResultSet results = qexec.execSelect();
			for (; results.hasNext();) {
				QuerySolution soln = results.nextSolution();
				// System.out.println(soln);

			}
			long end = System.nanoTime();
			System.out.println("Jena execution time : " + (end - start) / 1000000 + " ms");
			System.out.println("Jena # results :  " + results.getRowNumber());
		}

	}

}
