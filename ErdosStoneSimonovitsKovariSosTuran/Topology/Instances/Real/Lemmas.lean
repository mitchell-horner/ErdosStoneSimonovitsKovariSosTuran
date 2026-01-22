import Mathlib
import ErdosStoneSimonovitsKovariSosTuran.Algebra.Order.Monoid.Canonical.Basic
import ErdosStoneSimonovitsKovariSosTuran.Order.Monotone.Basic

open Filter Set Topology

section Monotone

variable {ι : Type*} [Preorder ι] [Nonempty ι]

/-- A monotone, bounded above sequence `f : ℕ → ℝ` on `Ici k` has the finite
limit `sSup (f '' Ici k)`. -/
theorem Real.tendsto_csSup_of_bddAbove_monotoneOn_Ici_nat {f : ℕ → ℝ} {k : ℕ}
    (h_bdd : BddAbove (f '' Ici k)) (h_mon : MonotoneOn f (Ici k)) :
    Tendsto f atTop (𝓝 (sSup (f '' Ici k))) := by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [← monotone_add_nat_iff_monotoneOn_nat_Ici] at h_mon
  rw [← tendsto_add_atTop_iff_nat k, ← range_add_eq_image_Ici, sSup_range]
  exact tendsto_atTop_ciSup h_mon h_bdd

/-- An antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` has the finite
limit `sInf (f '' Ici k)`. -/
theorem Real.tendsto_csInf_of_bddBelow_antitoneOn_Ici_nat {f : ℕ → ℝ} {k : ℕ}
    (h_bdd : BddBelow (f '' Ici k)) (h_ant : AntitoneOn f (Ici k)) :
    Tendsto f atTop (𝓝 (sInf (f '' Ici k))) := by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [← antitone_add_nat_iff_antitoneOn_nat_Ici] at h_ant
  rw [← tendsto_add_atTop_iff_nat k, ← range_add_eq_image_Ici, sInf_range]
  exact tendsto_atTop_ciInf h_ant h_bdd

variable [IsDirected ι (· ≤ ·)]

/-- The limit of a monotone, bounded above function `f : ι → ℝ` is a least upper bound
of the function. -/
theorem Real.isLUB_of_bddAbove_monotone_tendsto {f : ι → ℝ}
    (h_bdd : BddAbove (range f)) (h_mon : Monotone f)
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x)) : IsLUB (range f) x := by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciSup h_mon h_bdd)]
  exact isLUB_ciSup h_bdd

/-- The limit of an antitone, bounded below function `f : ι → ℝ` is a greatest lower bound
of the function. -/
theorem Real.isGLB_of_bddBelow_antitone_tendsto {f : ι → ℝ}
    (h_bdd : BddBelow (range f)) (h_ant : Antitone f)
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x)) : IsGLB (range f) x := by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciInf h_ant h_bdd)]
  exact isGLB_ciInf h_bdd

/-- The limit of an antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` is a least
upper bound of the sequence. -/
theorem Real.isLUB_of_bddAbove_monotoneOn_Ici_tendsto_nat {f : ℕ → ℝ} {k : ℕ}
    (h_bdd : BddAbove (f '' Ici k)) (h_mon : MonotoneOn f (Ici k))
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x)) : IsLUB (f '' Ici k) x := by
  rw [tendsto_nhds_unique h_tto (Real.tendsto_csSup_of_bddAbove_monotoneOn_Ici_nat h_bdd h_mon)]
  exact isLUB_csSup (image_nonempty.mpr nonempty_Ici) h_bdd

/-- The limit of an antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` is a greatest
lower bound of the sequence. -/
theorem Real.isGLB_of_bddBelow_antitoneOn_Ici_tendsto_nat {f : ℕ → ℝ} {k : ℕ}
    (h_bdd : BddBelow (f '' Ici k)) (h_ant : AntitoneOn f (Ici k))
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x)) : IsGLB (f '' Ici k) x := by
  rw [tendsto_nhds_unique h_tto (Real.tendsto_csInf_of_bddBelow_antitoneOn_Ici_nat h_bdd h_ant)]
  exact isGLB_csInf (image_nonempty.mpr nonempty_Ici) h_bdd

end Monotone
