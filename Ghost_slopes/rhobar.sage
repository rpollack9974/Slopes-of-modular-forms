import warnings

class rbdata(SageObject):
	"""This file defines a class for a rbar which contains information on the dimensions of rbar and all its cyclotomic twists. 
	
		We assume from the start that rbar arises in the following form: there is 1 <= b <= p-1 such that
	
			rbar|_I is an extension of w^b by 1 (maybe split), or 
			rbar|_I is w_2^b + w_2^{pb}.
			
			Thus det(rbar) = w^b on interia.
		
		Parameters:
			p: prime
			 
			krbar: integer k in [2,p] such that det(rbar)|_I = w^(k-1). This is *not* the "Serre" weight.
			
			red_type: 	Different options are...
								(i) Global conditions
								- "Eis" for Eisenstein.
								- "E2" is for the Eisenstein series E2.
								(ii) Local conditions
								- "Irred" for locally irreducible.
								- "Non-split generic" for locally reducible, non-split on inertia. This case **includes** any peu ramifee classes.
								- "Tres ramifee" for locally reducible and non-split but a tres ramifee extension.
								- "Split" for locally split on inertia
								
			eis: Number. (Default 0.) Represents the generic multiplicity of rbar in the Eisenstein space. Thus eis = dim E_{krbar}(rbar) if krbar > 2 and otherwise it equals dim E_{p+1}(rbar) if krbar = 2.			
			new: Boolean.	(Default: False.) True or false depending on whether only newforms count. (This only impacts the Eisenstein contribution and then only when E2 is in play.)	
			
			base: Dictionary. (Default {}). On key (k,t) with 2 <= k <= p+1 and 0 <= t <= p-2, should return the **cuspidal** dimension of rbar(t) in weight k. Note that you do not have to define the "entire" base. It will fill it out for you!
			
			
			mult: List of multiplicities. It should be as follows: a list [m1...md] where mj is the multiplicity of rbar(twist) in the "j"th Serre weight. The Serre weights, for those purpose are ordered in the following way:
					- The weights where rbar itself appears come first, in increasing order.
					- The weights where rbar(twist) appear come next, also in increasing order.
					For instance, if rbar = rbar as in Section 6.3 of Bergdall-Pollack, then you should list [m1,m2,m3] (check!) 
	"""
	def __init__(self,p,krbar,red_type="Non-split generic",eis=0,newforms=False,base=None,mult=None):
		
		## Inititate the prime, krbar, and reduction type. This is enough to gather the Serre weights. We also include the determinant as a parameter.
		
		self.p = p
		self.krbar = krbar
		self.red_type = red_type
		
		self.det = (krbar - 2) % (p-1) + 1 ## This is the parameter "b" in the setup
		
		if self.red_type == "Tres ramifee" or self.red_type == "E2":
			if self.det != 1:
				warnings.warn("Warning: Your reduction type is not compatible with the determinant parameter. I am changing your determinant to be 1.")
				self.krbar = 2
				self.det = 1
			
		## Initialize parameters for Eisenstein series
		
		self.eis = eis		
		self.newforms = newforms
		
		## Introduce two new parameters: eis_type is True/False depending on whether reduction is Eisenstein.
		## E2 is True/False depending on whether reduction is E2.
		
		self.eis_type = (self.red_type in ["Eis", "E2"])
		self.E2 = (self.red_type in ["E2"])
		
		
		## Initialize the base. Note that a lot of zeros are filled in way below, with the lines "for k in..."
		## The initial checks are just making sure the setup is all consistent.
		
		
		self.base = base
		self.mult = mult
		
		if self.base == None:
			self.base = {}
		if self.mult == None:
			self.mult = []
		
		if self.eis_type:
			## Initialize the base in the Eisenstein case.
			if self.eis == 0:
				warnings.warn("Warning: You didn't specify the Eisenstein multiplicity! I am setting it to 1.")
				self.eis = 1
			if self.base == {}:
				warnings.warn("Warning: You didn't specify any base dimensions, which are required for Eisenstein series. I am going to set them all to be 0.")
		else:
			## Warn the user if their eisenstein multiplicity is positive			
			if self.eis > 0:
				warnings.warn("You have a positive Eisenstein multiplicity, yet you didn't choose an Eisenstein reduction type. I'm resetting eis = 0.")
				self.eis = 0
			
			## Initialize the base in the non-Eisenstein case (so Serre's conjecture applies)			
			init_weights = self.serre_weights()
			
			## Start by checking that the mult and base as given are compatible with the Serre weights
			
			if self.mult != []:
				## Initial check to make sure the multiplicities are all positive and there is one per Serre weight and that the base hasn't also been specified 
				assert min(self.mult) > 0 and len(self.mult) == len(init_weights), "You have not specified enough multiplicity for the Serre weights, or mult 0 for some reason."
				assert self.base == {}, "You cannot (currently) specificy both the multiplicity and the base"
				## Now initialize the start of the base, based on multiplicity. Note: it is crucial the multiplicites and initial weights are given in the same order!				
				for i in range(len(init_weights)):
					(k,t) = init_weights[i]					
					self.base[(k,t)] = self.mult[i]
			elif self.base != {}:
				given_base = [(k,t) for (k,t) in self.base if self.base[(k,t)] != 0]
				assert set(given_base) == set(init_weights), "Your given base is incompatible with Serre weights."
			else:
				warnings.warn("Warning: You didn't specify any initial information. I am assuming multiplicity one in all the lowest weights.")
				for (k,t) in init_weights:
					self.base[(k,t)] = 1
			
		## The non-zero parts of the base should be there now. So, fill out the rest of the base.
				
		for k in [2..p+1]:
			for t in [0..p-2]:
				if (k,t) not in self.base.keys():
					self.base[(k,t)] = 0
					
		## Require a new dictionary that contains the mod p Euler characteristics, except with the cohomological degree-shifting. Thus the keys are going to be 0 <= g <= p-1 and twists 0 <= t <= p-2.
		self.mod_p_MS_tame_base = {}
		for g in [0..p-1]:
			for t in [0..p-2]:
				k = g+2
				e = 0
				if self.eis_weight_twist_compat(k,t):
					e = self.eis
				self.mod_p_MS_tame_base[(g,t)] = e + 2*(self.base[(k,t)] - self.E2_weight_two_correction(k,t))
				
		### Initiate dictionaries so that each dimension is calculated at most once
		
		self.mod_p_MS_tame_euler_dict = {}
		
		self.mod_p_MS_wild_euler_dict = {}
		
		self.mod_p_Ig_tame_euler_dict = {}	
		
		## Finally, initialize the "delta" parameter so that it only calculates the important summation a single time.
		
		self.mod_p_MS_delta = sum([self.mod_p_Ig_tame_euler(j,t) for j in [0..self.p-2] for t in [0..self.p-2]])
		
		
		
		
	## TO-DO: Edit this.
	def __repr__(self):	
		return "Mod "+str(self.p)+" repn with red_type = " + str(self.red_type) + ". The determinant is cyclo**" + str(self.det) + ". The Serre weights are " + str(self.serre_weights()) 
		
		
	def serre_weights(self):
		"""
			Returns the pairs (k,t) with 0 <= t <= p-2 and 2 <= k <= p+1 such that rbar(t) appears in weight k. 
			
			This is based on self.red_type and Theorem 3.17 in Buzzard-Diamond-Jarvis.
			
			In the case that type = "Eis", it returns the empty list.
			
			The convention for the ordering of the list is as follows. 
				1. Because of the determinant restriction, the answer is either (*,0) or (*,t) for a unique t != 0. We list those (*,0) first, and (*,t) second.
				2. Within a constant twist, the modular weight is *increasing*. (This is to be consisten with Bergdall-Pollack, Corollary and legacy code for "mult" above. Slightly different than [BDJ])
				
			Note also that our pairs (k,t) are what [BDJ] writes (t,k).
		"""
		p = self.p
		red_type = self.red_type
		b = self.det
		
		if self.eis_type:
			warnings.warn("Okay, you can ask me for the Serre weights, but remember you said you were an Eisenstein series. Be careful!")
			return []
		
		## First we will make the list just of what Buzzard-Diamond-Jarvis says, so we don't make a mistake. Then, we will translate to modular weights. Note that the convention is backwards though (V_{a,b} in [BDJ] has det^a twist).
		BDJ_list = []		
		
		## After "Irred" type, the rest of this is red from W(rbar) as on [p. 141, BDJ]. The "case numbers" in comments refer to that list.
	
		if self.red_type == "Irred":
			BDJ_list = [(b,0), (p+1-b,b-1)]
		elif red_type == "Tres ramifee":
			BDJ_list = [(p,0)] # Case 5
		elif self.red_type == "Non-split generic":
			if 1 < b and b <= p-1 and p > 2:
				BDJ_list = [(b,0)]   # Case 1,4
			else:
				BDJ_list = [(1,0), (p,0)] # Final case
		elif self.red_type == "Split":
			if 1 < b and b < (p-2):
				BDJ_list = [(b,0),(p-1-b,b)] # Case 2
			elif b == (p-2) and p > 3:
				BDJ_list = [(p-2,0), (1,p-2), (p,p-2)] # Case 3
			elif b == 1 and p > 3:
				BDJ_list = [(1,0), (p,0), (p-2,1)] # Case 6
			elif b == 1 and p == 3:
				BDJ_list = [(1,0), (3,0), (1,1), (3,1)] # Case 7
			elif b == p-1 and p > 2:
				BDJ_list = [(p-1,0)] # Case 4
			elif b == 1 and p == 2:
				BDJ_list = [(1,0), (p,0)]  # Final case
		
		####
		## Now we convert from the [BDJ] list to modular weights. The list above is (n,m) such that rbar appears in H^1(Sym^(n-1)\otimes det^m).
		## So if we take k = n + 1 then \rbar \otimes -m appears in weight k. We need to take m \in [0..p-1] though.
		
		return [(n+1, -m % (p-1)) for (n,m) in BDJ_list]
		
	def E2_weight_two_correction(self,k,twist):
		"""
			Returns 1 if all the following conditions are satisfied:
				1. We are working with rbar = 1 + w
				2. We want to include old forms
				3. k = 2 and twist = 0
			Otherwise, returns 0.
			
			This value shows up in two places. 
				- First, it is a correction factor for the dimension of E_k(rbar(twist)). 
				- Second, it is the dimension of H^1_c(Sym^(k-2)(Qp^2))(rbar(twist))
		"""
		if self.E2 and not self.newforms and k == 2 and twist == 0:
			return 1
		else:
			return 0
	
	def weight_twist_compat(self,k,twist):
		"""
			Returns true/false, depending on if rbar(t) has the correct
			determinant to appear in weight k
		"""
		p = self.p
		det = self.det
		return (det + 2*twist) % (p-1) == (k-1) % (p-1)
		
	def eis_weight_twist_compat(self,k,twist,verbose=false):
		"""
			Returns true/false, depending on if rbar(t) has the correct determinant to appear in weight k as an Eisenstein series. Note that only two twists are possible.
		"""
		p = self.p
		det = self.det
		return ((twist % (p-1) == 0) or (twist % (p-1) == (-det) % (p-1))) and self.weight_twist_compat(k,twist) 
	
	### Functions for calculating "modular symbols" mod p. Note: not really. Everything is calculating Euler characteristics	
	
	def mod_p_Ig_tame_euler(self,g,twist):
		"""
			Returns Euler char. for cohomology of I_t for where t = g mod (p-1) and 1 <= t <= p-1. Uses the tame
			answers from Ash-Stevens
		"""
		p = self.p
		g = (g-1) % (p-1) + 1   ### forces g into [1,p-1]
		twist = twist % (p-1)
		
		if (g,twist) not in self.mod_p_Ig_tame_euler_dict:
			self.mod_p_Ig_tame_euler_dict[(g,twist)] = self.mod_p_MS_tame_euler(g,twist) + self.mod_p_MS_tame_euler(p-1-g,twist-g)
			
		return self.mod_p_Ig_tame_euler_dict[(g,twist)]
		
	def mod_p_MS_tame_euler(self,g,twist):
		"""
			Returns the (negative of) Euler characteristic of H^1_c(Gamma,Sym^g(Fp^2)(rbar(twist))-H^2_c(Gamma,Sym^g(Fp^2))(rbar(twist)). Note that
			we make the convention that this is 0 if g < 0. This is useful for handling the case of g = p also.
		"""
		p = self.p
		twist = twist % (p-1)		
		
		if (g,twist) not in self.mod_p_MS_tame_euler_dict:
			k = g + 2
			if not self.weight_twist_compat(k,twist) or g < 0:
				self.mod_p_MS_tame_euler_dict[(g,twist)] = 0
			### This is the basic step we have to start with	
###ROB below elif previously was if
			elif g <= p-1:
				self.mod_p_MS_tame_euler_dict[(g,twist)] = self.mod_p_MS_tame_base[(g,twist)]
			### Once g >= p^2 - 1 it isn't so bad
			elif g >= (p**2 - 1):
				m = floor(g/(p**2-1))
				self.mod_p_MS_tame_euler_dict[(g,twist)] = self.mod_p_MS_tame_euler(g-m*(p**2-1),twist) + m*self.mod_p_MS_delta
			### In remaining cases we know g >= p, so get an Ig contribution, and then a contibution from g - (p+1),
			### which is zero in case g = p
			else: 
				self.mod_p_MS_tame_euler_dict[(g,twist)] = self.mod_p_Ig_tame_euler(g,twist) + self.mod_p_MS_tame_euler(g-(p+1),twist-1) 
			
		return self.mod_p_MS_tame_euler_dict[(g,twist)]
			
	def mod_p_MS_wild_euler(self,g,twist):
		"""
			Returns the (negative of) Euler characteristic of H^1_c(Gamma0,Sym^g(Fp^2)(rbar(twist))-H^2_c(Gamma0,Sym^g(Fp^2))(rbar(twist)). Note that
			we make the convention that this is 0 if g < 0. This is useful for handling the case of g = p also.
		"""
		p = self.p
		twist = twist % (p-1)

		if (g,twist) not in self.mod_p_MS_wild_euler_dict:		
			k = g + 2
			if not self.weight_twist_compat(k,twist) or g < 0:
				self.mod_p_MS_wild_euler_dict[(g,twist)] = 0
			if g < p-1:
				self.mod_p_MS_wild_euler_dict[(g,twist)] = sum([self.mod_p_Ig_tame_euler((2*j-g),twist+j-g) for j in [0..g]])
			else:
				self.mod_p_MS_wild_euler_dict[(g,twist)] = self.mod_p_MS_wild_euler(g-(p-1),twist) + self.mod_p_MS_delta
				
		return self.mod_p_MS_wild_euler_dict[(g,twist)]
			
		
	def cusp_tame(self,k,twist):
		"""
			Return the dimension of S_k(Gamma)(rbar(twist)). This is given by a formula (1/2)*(mod p euler char - eisen contrib) + correction term for E2
		"""
		g = k-2		
		e = 0
		if self.eis_weight_twist_compat(k,twist):
			e = self.eis
		ans = (self.mod_p_MS_tame_euler(g,twist) - e)/2 + self.E2_weight_two_correction(k,twist)
		assert ans == floor(ans), "Dimension you found is not an integer!"
		return ans
		
	def cusp_wild(self,k,twist):
		"""
			Return the dimension of S_k(Gamma0)(rbar(twist)).
		"""
		g = k-2		
		e = 0
		if self.eis_weight_twist_compat(k,twist):
			e = self.eis
		ans = (self.mod_p_MS_wild_euler(g,twist) - 2*e)/2 + self.E2_weight_two_correction(k,twist)
		assert ans == floor(ans), "Dimension you found is not an integer!"
		return ans	
		
	def cusp_new(self,k,twist):
		"""
			Returns the Gamma0(p)-new dimensions in S_k(Gamma0)(rbar(twist))
		"""
		return self.cusp_wild(k,twist) - 2*self.cusp_tame(k,twist)
		
		
	#### These functions are legacy from prior programs. Just different names for the prior functions.
	def tame(self,k,twist):
		return self.cusp_tame(k,twist)
		
	def wild(self,k,twist):
		return self.cusp_wild(k,twist)
		
	def new(self,k,twist):
		return self.wild(k,twist) - 2*self.tame(k,twist)

		


