module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Directed colimits of quasi-coherent modules

Source: Stacks Project, Schemes, Lemma 01ID and Section 26.24, item (4)
(blueprint: lem-weil-pbc-quasi-coherent-module-colimit-affine-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A directed colimit of quasi-coherent modules is quasi-coherent, and its sections
on an affine open have the expected elementwise description. Source: Stacks Project,
Schemes, Lemma 01ID and Section 26.24, item (4)
(blueprint: lem-weil-pbc-quasi-coherent-module-colimit-affine-sections).

Proof: for an affine open `U` with `R = Γ(X, U)`, restrict to `Spec R ≅ U`; there the
restricted system is `M_i~` with `M_i = F_i(U)` and the restricted colimit is `M~` for
`M = colim M_i` (the tilde functor preserves colimits), so `F(U) ≅ M` compatibly with the
`c_{i,U}`; the elementwise description of a directed colimit of modules gives the two
clauses, and `F|_U ≅ M~` on an affine cover gives quasi-coherence. -/
theorem quasiCoherentModuleColimitAffineSections
    (X : Scheme.{u}) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ X.Modules) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i : I, (F.obj i).IsQuasicoherent) :
    c.pt.IsQuasicoherent ∧
      ∀ (U : X.Opens), IsAffineOpen U →
        (∀ s : Γ(c.pt, U), ∃ (i : I) (x : Γ(F.obj i, U)),
          ((c.ι.app i).val.app (Opposite.op U)) x = s) ∧
        (∀ (i : I) (x : Γ(F.obj i, U)),
          ((c.ι.app i).val.app (Opposite.op U)) x = 0 ↔
            ∃ (i' : I) (h : i ≤ i'),
              ((F.map (homOfLE h)).val.app (Opposite.op U)) x = 0) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
