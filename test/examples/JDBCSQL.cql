options
	jdbc_quote_char = "" 
	always_reload = true 
	#jdbc_default_string = "jdbc:postgresql://localhost:5432/postgres?user=postgres&password=password"
	#docker run --rm --name cql-fun -p 5432:5432 -e POSTGRES_PASSWORD=password -d postgres 
	#to try postgres, be sure to replace the jdbcURL for the load command directly below
	
#create some example data in a local temporary sql database. (close delay keeps H2 database alive across connections)
command load = exec_jdbc "jdbc:h2:mem:db1;DB_CLOSE_DELAY=-1" { 
"DROP TABLE IF EXISTS Employee CASCADE;
 DROP TABLE IF EXISTS Department CASCADE;
 DROP TABLE IF EXISTS ExportedEmployee CASCADE;
 DROP TABLE IF EXISTS ExportedDepartment CASCADE;
 DROP TABLE IF EXISTS ExportedTransEmployee CASCADE;
 DROP TABLE IF EXISTS ExportedTransDepartment CASCADE;" 

#multiple statements can be used, but many SQL engines (such as H2, CQL's internal engine) will only print the output of the first statement, and some require ?allowMultiQueries=true in the jdbc string 

"CREATE TABLE Employee(
 id INT PRIMARY KEY,
 name VARCHAR(255),
 manager INT, 
 worksIn INT)"

"CREATE TABLE Department(
 id INT PRIMARY KEY,
 name VARCHAR(255),
 secretary INT)"
 
"INSERT INTO Employee VALUES 
 (101, 'Alan', 103, 10), 
 (102, 'Camille', 102, 2), 
 (103, 'Andrey', 103, 10)"

"INSERT INTO Department VALUES
 (10, 'Applied Math', 101),
 (2, 'Pure Math', 102)"

"ALTER TABLE Employee ADD CONSTRAINT e1
 FOREIGN KEY (manager) REFERENCES Employee (id)"

"ALTER TABLE Employee ADD CONSTRAINT e2 
 FOREIGN KEY (worksIn) REFERENCES Department (id)"

"ALTER TABLE Department ADD CONSTRAINT d1
 FOREIGN KEY (secretary) REFERENCES Employee (id)"

# options always_reload = true #true forces pragmas to not be cached between runs (i.e., always run)
}  
 
# When the JDBC class name and string are left blank, CQL uses the value of the option
#    jdbc_default_string.  These can be set globally by placing,
#   at the beginning of the file, for example:
#   
#  options
#   
#   jdbc_default_string = "jdbc:h2:mem:db1;DB_CLOSE_DELAY=-1"
#
#look at the example data
command view0 = exec_jdbc "" {  #see note above!!!
"SELECT * FROM Department"
"SELECT * FROM Employee"
}

####################################################

schema S = literal : sql {
	entities
		Employee 
		Department
  	attributes
  		id : Employee -> Varchar
  		id : Department -> Varchar
  		first last manager worksIn : Employee -> Varchar
     	age	: Employee -> Integer
     	name secretary : Department -> Varchar
 }

#import an instance by providing queries for each entity
instance J = import_jdbc ""  : sql {
 #use name as first name
  #use null as last name
  #use id as age	
	Employee -> "SELECT id, manager, worksIn, name AS first, 'lname' as last, id AS age FROM Employee"
	Department -> "SELECT id, secretary, name FROM Department"

	options
		#aql by default prepends the entity to each imported ID, to get uniqueness across entities.
		#to import the IDs verbatim, set the option below to false
		prepend_entity_on_ids = false
}


#export the instance to SQL
command store1 = export_jdbc_instance J ""  "Exported"
{ options start_ids_at = 100 }

#view exported SQL instance
command view1 = exec_jdbc ""  { 
	"SELECT * FROM ExportedEmployee"
	"SELECT * FROM ExportedDepartment"
}



##########
#direct method to land sql data

schema S_direct2 = import_jdbc_all "" {
 options allow_sql_import_all_unsafe=true
}

schema S_direct = literal : sql {
	entities
		Employee 
		Department
  	attributes
		manager  name : Employee -> Other
		worksIn   : Employee -> Other
		secretary : Department -> Other
  		name 	  : Department -> Other
 }

instance I = import_jdbc_direct "" "ROW_NUMBER() OVER ()" : S_direct 
instance J2 = import_jdbc_direct "" "ROW_NUMBER() OVER ()" : S_direct2 
##############################
#
#execute command line actions as follows
#pragma cmdline1 = exec_cmdline  { 
#"ls -ltr"
#"echo hi"
#}
#
#execute actions as follows
#pragma js1 = exec_js  { 
#"javax.swing.JOptionPane.showMessageDialog(null, \"hello1\")"
#"javax.swing.JOptionPane.showMessageDialog(null, \"hello2\")"
#}
