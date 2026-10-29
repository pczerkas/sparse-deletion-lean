import FiniteBlocks

namespace SparseDeletion

theorem hit_frequency_bound
    (E : Set ℕ) (N : ℕ) (hN : 0 < N) :
    (countUpTo (hitSet E) N : ℝ) / (N : ℝ) ≤
      (13608 : ℝ) / 47027 +
      47027 * ((countUpTo E N : ℝ) / (N : ℝ)) +
      47027 / (N : ℝ) := by
  have hnat := hit_count_bound E N
  have hdiv := Nat.mul_div_le N 47027
  have hrem := Nat.le_of_lt (Nat.mod_lt N (by decide : 0 < 47027))
  have hnatR : (countUpTo (hitSet E) N : ℝ) ≤
      13608 * (↑(N / 47027) : ℝ) +
      47027 * (countUpTo E N : ℝ) + (↑(N % 47027) : ℝ) := by
    exact_mod_cast hnat
  have hdivR : (47027 : ℝ) * (↑(N / 47027) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdiv
  have hremR : (↑(N % 47027) : ℝ) ≤ 47027 := by
    exact_mod_cast hrem
  have hPos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hupper : (countUpTo (hitSet E) N : ℝ) ≤
      (13608 : ℝ) / 47027 * (N : ℝ) +
      47027 * (countUpTo E N : ℝ) + 47027 := by
    nlinarith [hdivR, hnatR, hremR]
  apply (div_le_iff₀ hPos).mpr
  calc
    (countUpTo (hitSet E) N : ℝ) ≤
        (13608 : ℝ) / 47027 * (N : ℝ) +
        47027 * (countUpTo E N : ℝ) + 47027 := hupper
    _ = ((13608 : ℝ) / 47027 +
      47027 * ((countUpTo E N : ℝ) / (N : ℝ)) +
      47027 / (N : ℝ)) * (N : ℝ) := by
        field_simp

/-- Every sparse deletion set obeys a quantitative upper asymptotic density
bound with the 31×37×41 sieve. This is not yet zero density. -/
theorem eventually_hit_density_le_three
    (E : Set ℕ) (hE : HasDensityZero E)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (N : ℕ) in Filter.atTop,
      (countUpTo (hitSet E) N : ℝ) / (N : ℝ) ≤
        (13608 : ℝ) / 47027 + ε := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (2 * 47027 : ℝ) / ε < (K : ℝ) :=
    exists_nat_gt _
  have hsE : ∀ᶠ N : ℕ in Filter.atTop,
      (countUpTo E N : ℝ) / (N : ℝ) < ε / (2 * 47027) :=
    hE.eventually (Iio_mem_nhds (by positivity))
  have hsN : ∀ᶠ N : ℕ in Filter.atTop, K + 1 ≤ N :=
    Filter.eventually_ge_atTop (K + 1)
  filter_upwards [hsE, hsN] with N he hN
  have hpos : 0 < N := by omega
  have hPosR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hpos
  have hCast : (K : ℝ) < (N : ℝ) := by
    exact_mod_cast (show K < N by omega)
  have hlim : (2 * 47027 : ℝ) < ε * (N : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp (lt_trans hK hCast)
  have hsmallN : (47027 : ℝ) / (N : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hPosR).mpr
    nlinarith
  have hsmallE :
      (47027 : ℝ) * ((countUpTo E N : ℝ) / (N : ℝ)) < ε / 2 := by
    nlinarith [he]
  have hbound := hit_frequency_bound E N hpos
  linarith

end SparseDeletion

#print axioms SparseDeletion.eventually_hit_density_le_three
