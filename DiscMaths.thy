theory DiscMaths
  imports Main
begin

lemma dvd_trans:
  assumes "a dvd b" and "b dvd c"
  shows "a dvd c"
  using assms dvd_def by auto

definition divides :: "int \<Rightarrow> int \<Rightarrow> bool" (infix "\<parallel>" 50)
  where "a \<parallel> b \<equiv> (\<exists>k. b = a * k)"

lemma divides_trans [trans]:
  assumes "a \<parallel> b" and "b \<parallel> c"
  shows "a \<parallel> c"
proof -
  from assms obtain v where "b = a * v"
    using divides_def by blast
  moreover from assms obtain w where "c = b * w"
    using divides_def by blast
  ultimately have "c = a * (v * w)"
    by (simp add: mult.assoc)
  then show ?thesis
    by (simp add: divides_def)
qed

definition even :: "int \<Rightarrow> bool" where
  "even n \<equiv> (\<exists>i::int. n = 2 * i)"

definition odd :: "int \<Rightarrow> bool" where
  "odd n \<equiv> (\<exists>i::int. n = 2 * i + 1)"

lemma even_not_odd:
  shows "even n \<longleftrightarrow> \<not> odd n"
using even_def odd_def by presburger


lemma n_squared_even:
  shows "even (n\<^sup>2) \<longleftrightarrow> even n"
  apply(rule iffI)
   apply(subgoal_tac "odd n \<Longrightarrow> odd (n * n)")
    apply simp
    apply simp
  apply(simp add: even_def, erule exE)
  apply(rule_tac x="2*i*i + 2*i" in exI)
  using prod_sums apply force
  apply(simp add: even_def, erule exE)
  apply(rule_tac x="2*i*i" in exI)
  apply(simp add: power2_eq_square)
  done

lemma prod_sums:
  fixes a::int and b::int and c::int and d::int
  shows "(a + b) * (c + d) = a*c + a*d + b*c + b*d"
using int_distrib by simp

end