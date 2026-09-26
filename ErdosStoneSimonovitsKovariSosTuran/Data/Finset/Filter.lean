import Mathlib

namespace Finset

variable {α β : Type*}

theorem filter_true {h} (s : Finset α) : @filter _ (fun _ => True) h s = s := by ext; simp

end Finset
