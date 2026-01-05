import Mathlib

open Fintype Function

namespace SimpleGraph

noncomputable def completeBipartiteGraph.overFinIso {α β : Type*} [Fintype α] [Fintype β]
    {s t : ℕ} (hc₁ : card α = s) (hc₂ : card β = t) :
    completeBipartiteGraph α β ≃g completeBipartiteGraph (Fin s) (Fin t) where
  toFun := Sum.map (equivFinOfCardEq hc₁) (equivFinOfCardEq hc₂)
  invFun := Sum.map (equivFinOfCardEq hc₁).symm (equivFinOfCardEq hc₂).symm
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := by simp

variable {V W : Type*} (G : SimpleGraph V)

theorem edgeSet_map (f : V ↪ W) (G : SimpleGraph V) :
    (G.map f).edgeSet = f.sym2Map '' G.edgeSet := by
  ext v
  induction v
  rw [mem_edgeSet, map_adj, Set.mem_image]
  constructor
  · intro ⟨a, b, hadj, ha, hb⟩
    use s(a, b), hadj
    rw [Embedding.sym2Map_apply, Sym2.map_pair_eq, ha, hb]
  · intro ⟨e, hadj, he⟩
    induction e
    rw [Embedding.sym2Map_apply, Sym2.map_pair_eq, Sym2.eq_iff] at he
    exact he.elim (fun ⟨h, h'⟩ ↦ ⟨_, _, hadj, h, h'⟩) (fun ⟨h', h⟩ ↦ ⟨_, _, hadj.symm, h, h'⟩)

theorem support_map (f : V ↪ W) : (G.map f).support = f '' G.support := by
  ext; simp [mem_support]; tauto

end SimpleGraph
