package catdata.cql;

import java.io.File;
import java.io.FileReader;
import java.util.*;

import catdata.Program;
import catdata.Util;
import catdata.cql.exp.*;

/**
 * Dumps CQL instance data in a deterministic, comparable format.
 * Output: one line per entity row with sorted attributes.
 */
public class CqlDump {

    public static void main(String... args) {
        try {
            String path = args[0];
            String s = Util.readFile(new FileReader(new File(path)));
            Program<Exp<?>> program = AqlParserFactory.getParser().parseProgram(s);
            AqlEnv env = new AqlEnv(program);
            env.typing = new AqlTyping(program, false);
            AqlMultiDriver d = new AqlMultiDriver(program, env);
            d.start();

            if (env.exn != null) {
                System.err.println("ERROR: " + env.exn.getMessage());
                System.exit(1);
            }
            env = d.env;

            for (String name : program.order) {
                Exp<?> exp = program.exps.get(name);
                if (!exp.kind().equals(Kind.INSTANCE)) continue;

                Object val = env.get(exp.kind(), name);
                if (val == null) continue;
                Instance<?,?,?,?,?,?,?,?,?> inst = (Instance<?,?,?,?,?,?,?,?,?>) val;

                System.out.println("INSTANCE " + name);
                dumpInstance(inst);
                System.out.println();
            }
        } catch (Exception ex) {
            ex.printStackTrace();
            System.exit(1);
        }
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    private static void dumpInstance(Instance inst) {
        Schema sch = inst.schema();
        Algebra alg = inst.algebra();

        for (Object enObj : new TreeSet<>(sch.ens)) {
            String en = enObj.toString();
            int size = alg.size(enObj);
            System.out.println("  ENTITY " + en + " (" + size + " rows)");

            // Collect rows as sorted attribute-value strings
            List<String> rows = new ArrayList<>();
            for (Object x : alg.en(enObj)) {
                TreeMap<String, String> vals = new TreeMap<>();

                for (Object fkObj : sch.fksFrom(enObj)) {
                    Object target = alg.fk(fkObj, x);
                    vals.put(fkObj.toString(), target.toString());
                }
                for (Object attObj : sch.attsFrom(enObj)) {
                    Object val = alg.att(attObj, x);
                    vals.put(attObj.toString(), val.toString());
                }

                StringBuilder sb = new StringBuilder();
                for (Map.Entry<String, String> e : vals.entrySet()) {
                    if (sb.length() > 0) sb.append(", ");
                    sb.append(e.getKey()).append("=").append(e.getValue());
                }
                rows.add(sb.toString());
            }
            Collections.sort(rows);
            for (String row : rows) {
                System.out.println("    " + row);
            }
        }
    }
}
