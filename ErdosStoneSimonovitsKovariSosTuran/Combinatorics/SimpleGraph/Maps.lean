import Mathlib

open Fintype Function

namespace SimpleGraph

/-- The isomorphism between `completeBipartiteGraph α₁ β₁` and
`completeBipartiteGraph α₂ β₂ ` where `α₁ ≃ α₂` and `β₁ ≃ β₂`. -/
noncomputable def completeBipartiteGraph.congr {α₁ α₂ β₁ β₂ : Type*}
  [Fintype α₁] [Fintype α₂] [Fintype β₂] [Fintype β₂] (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) :
    completeBipartiteGraph α₁ β₁ ≃g completeBipartiteGraph α₂ β₂ where
  toFun := Sum.map hα hβ
  invFun := Sum.map hα.symm hβ.symm
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
