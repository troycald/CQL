package catdata.cql.gui;

import catdata.cql.gui.WarehouseUI.Example;

public class EHRExample extends Example {

		@Override
		public String getName() {
			return "EHR";
		}

		@Override
		public String getSources() {
			return """
					
typeside Ty = literal {
	external_types
		Integer -> "java.lang.Integer"
		Float -> "java.math.BigDecimal"
		String -> "java.lang.String"
	external_parsers 
		Float -> "x => java.math.BigDecimal.valueOf(java.lang.Double.parseDouble(x))"
		Integer -> "x => java.lang.Integer.parseInt(x)"
		String -> "x => x"
	external_functions
		"+" : Float,Float->Float = "(x, y) => x.add(y)"	
		"*" : Float,Float->Float = "(x, y) => x.multiply(y)"	
		"-" : Float,Float->Float = "(x, y) => x.subtract(y)"	
		"/" : Float,Float->Float = "(x, y) => x.divide(y)"	
		"MAX" : Float,Float->Float = "(x, y) => x.max(y)"
		"MIN" : Float,Float->Float = "(x, y) => x.min(y)"		
	equations
		
}		

schema Olog1 = literal : Ty {
	entity Patient
	attributes ID first_name last_name birthdate create_date : String

	entity Visit
	attributes ID patient_id visit_date : String

	entity Observation
	attributes ID visit_id clinician_id obs_type observation : String
}
constraints Olog1Constraints = literal : Olog1 {
	forall x y : Observation where x.ID = y.ID -> where x = y
	forall x y : Visit where x.ID = y.ID -> where x = y
	forall x y : Patient where x.ID = y.ID -> where x = y
	forall x : Observation -> exists y : Visit where x.visit_id = y.ID
	forall x : Visit -> exists y : Patient where x.patient_id = y.ID
}
schema Olog2 = literal : Ty {
	entity Prescription
	attributes ID patient_id date details : String

	entity Patient 
	attributes ID fname lname dob : String

	entity Observation
	attributes ID patient_id clinician_id obs_type obs_date observation : String
}
constraints Olog2Constraints = literal : Olog2 {
	forall x y : Observation where x.ID = y.ID -> where x = y
	forall x y : Prescription where x.ID = y.ID -> where x = y
	forall x y : Patient where x.ID = y.ID -> where x = y
	forall x : Prescription -> exists y : Patient where x.patient_id = y.ID
	forall x : Observation -> exists y : Patient where x.patient_id = y.ID
}
#instance O1 = importJdbc <url>
instance Olog1Instance = literal : Olog1 {
	generators
		p1 p2 p3 : Patient
		v1 v2 v3 : Visit
		o1 o2 o3 : Observation
	equations
		p1.ID = 937189 p1.first_name = john p1.last_name = doe 
		p1.birthdate = 340465020 p1.create_date = 1187438212 	
		p2.ID = 937190 p2.first_name = amrit p2.last_name = kumar 
		p2.birthdate = 246222505 p2.create_date = 1187444008
		p3.ID = 937191 p3.first_name = alexandra p3.last_name = grant 
		p3.birthdate = 121408849 p3.create_date = 1187445155 	

		v1.ID = 1237827 v1.patient_id = 937189 v1.visit_date = 1187438212
		v2.ID = 1237828 v2.patient_id = 937190 v2.visit_date = 1187444008
		v3.ID = 1237829 v3.patient_id = 937191 v3.visit_date = 1187445155

		o1.ID = 487298329 o1.visit_id = 1237827 o1.clinician_id = 562 
		o1.obs_type = HR o1.observation = 114
		o2.ID = 487298330 o2.visit_id = 1237827 o2.clinician_id = 562 
		o2.obs_type = WT o2.observation = 180
		o3.ID = 487298331 o3.visit_id = 1237827 o3.clinician_id = 562 
		o3.obs_type = BP o3.observation = "130/82"
}

instance Olog2Instance = literal : Olog2 {
generators
		p1 p2 p3 : Patient
		v1 v2 v3 : Prescription
		o1 o2 o3 : Observation
	equations
		p1.ID = 25234 p1.fname = alexandra p1.lname = grant 
		p1.dob = 121408849
		p2.ID = 25235 p2.fname = vincent p2.lname = "von hoff" 
		p2.dob = 409235232
		p3.ID = 25236 p3.fname = brian p3.lname = tsai 
		p3.dob = 380665171 	

		v1.ID = 675345 v1.patient_id = 25234 v1.date = 1639676732
		v1.details = Enalapril
		v2.ID = 675346 v2.patient_id = 25234 v2.date = 1639696544
		v2.details = chlorothiazide
		v3.ID = 675347 v3.patient_id = 25235 v3.date = 1639704522
		v3.details = lisinopril

		o1.ID = 154298449 o1.patient_id = 25234 o1.clinician_id = 132 
		o1.obs_type = HR o1.obs_date = 1639676732 o1.observation=116
		o2.ID = 154298450 o2.patient_id = 25234 o2.clinician_id = 132 
		o2.obs_type = WT o2.obs_date = 1639676732 o2.observation=220
		o3.ID = 154298451 o3.patient_id = 25234 o3.clinician_id = 132 
		o3.obs_type = BP o3.obs_date = 1639676732 o3.observation="132/82"

}
command check1 = check Olog1Constraints Olog1Instance
command check2 = check Olog2Constraints Olog2Instance

										""";
		}

		@Override
		public String getLinks() {
			return """
entity_isomorphisms
	p : Olog1.Patient -> Olog2.Patient
	o : Olog1.Observation -> Olog2.Observation
		
equations
	eq1: forall x:Olog1.Patient,  x.first_name = x.p.fname 
	eq2: forall x:Olog1.Patient,     x.last_name = x.p.lname 
	eq3: forall x:Olog1.Patient,     x.birthdate = x.p.dob 
	eq4: forall x:Olog1.Observation,     x.ID = x.o.ID
	eq5: forall x:Olog1.Observation,     x.observation = x.o.observation
	eq6: forall x:Olog1.Observation,     x.clinician_id = x.o.clinician_id  
	eq7: forall x:Olog1.Observation,     x.obs_type = x.o.obs_type		
				
constraints
	rule1: forall x y : Olog1_Patient where x.first_name=y.first_name x.last_name=y.last_name 
	-> where x=y

	rule2: forall x y : Olog2_Observation where x.obs_date = y.obs_date 
	 -> where x.o_inv.visit_id = y.o_inv.visit_id

	rule3: forall x y : Olog1_Observation where x.visit_id = y.visit_id
	 -> where x.o.patient_id = y.o.patient_id

	rule4: forall x : Olog1_Observation y : Olog1_Visit z : Olog1_Patient z2 : Olog2_Patient 
					where x.visit_id = y.ID z.ID = y.patient_id  x.o.patient_id = z2.ID 
	 -> where z = z2.p_inv

	rule5: forall x y : Olog1_Observation where x.visit_id = y.visit_id 
	-> where x.o.obs_date = y.o.obs_date 

	rule6: forall x : Olog1_Observation y : Olog1_Visit where x.visit_id = y.ID 
	-> where y.visit_date = x.o.obs_date
							""";
		}

		@Override
		public String getTargets() {
			return "";
		}

	}