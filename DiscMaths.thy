theory DiscMaths
  imports Main
begin

text \<open>Section 1.2 Question 7(c)\<close>

lemma dvd_linear_comb:
  fixes d::int
  assumes "d dvd m" and "d dvd n"
  shows "d dvd (k*m + l*n)"
proof -
  from \<open>d dvd m\<close> obtain i where "m = d*i"
    using dvdE by blast
  moreover from \<open>d dvd n\<close> obtain j where "n = d*j"
    using dvdE by blast
  ultimately have "k*m + l*n = d*(k*i + l*j)"
    using int_distrib by simp
  thus "d dvd (k*m + l*n)"
    using dvdI by blast
qed


text \<open>Euclid's algorithm\<close>

fun gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd m 0 = m" |
  "gcd m n = gcd n (m mod n)"


text \<open>Definition of the GCD\<close>

definition gcd_props :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "gcd_props m n x \<equiv> (x dvd m) \<and> (x dvd n) \<and> (\<forall>d. d dvd m \<and> d dvd n \<longrightarrow> d dvd x)"


text \<open>Proof that Euclid's algorithm returns the GCD\<close>

lemma euclid_gcd_props:
  shows "gcd_props m n (gcd m n)"
proof -
  have "(gcd m n) dvd m \<and> (gcd m n) dvd n"
  proof(induction m n rule: gcd.induct)
    case (1 m)
    then show ?case by simp
  next
    case (2 m v)
    then show ?case using dvd_mod_imp_dvd by auto
  qed
  moreover have "\<forall>d. d dvd m \<and> d dvd n \<longrightarrow> d dvd (gcd m n)"
  proof(induction m n rule: gcd.induct)
    case (1 m)
    then show ?case by simp
  next
    case (2 m v)
    then show ?case by (simp add: dvd_mod)
  qed
  ultimately show "gcd_props m n (gcd m n)" by (simp add: gcd_props_def)
qed


text \<open>Properties of GCD: commutativity, linearity, associativity\<close>

lemma gcd_commute:
  shows "gcd m n = gcd n m"
proof -
  fix x::nat
  have "gcd_props m n x \<longleftrightarrow> gcd_props n m x"
    using gcd_props_def by auto
  thus "gcd m n = gcd n m"
    using dvd_antisym euclid_gcd_props gcd_props_def by auto
qed

lemma gcd_linear:
  shows "i * (gcd m n) = gcd (i*m) (i*n)"
proof(induction m n rule: gcd.induct)
  case (1 m)
  then show ?case by simp
next
  case (2 m v)
  then show ?case by (metis divisors_zero gcd.elims mult_eq_if mult_mod_right nat.simps(3))
qed

lemma gcd_assoc:
  shows "gcd l (gcd m n) = gcd (gcd l m) n"
by (meson dvd_antisym dvd_trans euclid_gcd_props gcd_props_def)


text \<open>Section 3.2 Question 2\<close>

lemma gcd_coprime_prod:
  assumes "gcd a c = 1"
  shows "gcd (a*b) c = gcd b c"
proof -
  have "gcd b c = gcd (b * (gcd a c)) c"
    using assms by simp
  moreover have "... = gcd (gcd (b*a) (b*c)) c"
    by (simp add: gcd_linear)
  moreover have "... = gcd (a*b) (gcd (b*c) c)"
    by (simp add: gcd_assoc mult.commute)
  moreover have "... = gcd (a*b) (c*(gcd b 1))"
    by (metis gcd_linear mult.commute mult.right_neutral)
  ultimately show "gcd (a*b) c = gcd b c"
    by simp
qed

end