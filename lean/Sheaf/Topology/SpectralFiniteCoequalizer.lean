module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Sheaf.Topology.SetsExtensionByEmpty

/-!
# Finite-space descent of spectral coequalizers

Source: literature/stacks-project/modules.tex, Lemma 0CAK (blueprint:
`lem-weil-pbc-spectral-finite-coequalizer-from-finite-space`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens

namespace TopCat

/-- A finite coequalizer of extensions by the empty set of finite constant sheaves on
quasi-compact opens of a spectral space is pulled back from a finite sober space.
Source: Stacks Project, Modules, Lemma 0CAK, label `lemma-constructible-comes-from-finite`.
The proof proceeds by expressing the spectral space as a directed limit of finite sober
spaces, descending the finitely many opens and maps, forming the coequalizer downstairs,
and checking the pullback coequalizer and finiteness of stalks (blueprint:
`lem-weil-pbc-spectral-finite-coequalizer-from-finite-space`).
(blueprint: lem-weil-pbc-spectral-finite-coequalizer-from-finite-space) -/
theorem spectral_finite_coequalizer_from_finite_space
    (X : TopCat.{u}) [SpectralSpace X]
    (n m : ℕ) (U : Fin n → Opens X) (V : Fin m → Opens X)
    (S : Fin n → Type u) (T : Fin m → Type u)
    (hU : ∀ a, IsCompact (U a : Set X))
    (hV : ∀ b, IsCompact (V b : Set X))
    (hS : ∀ a, Finite (S a)) (hT : ∀ b, Finite (T b))
    (F : X.Sheaf (Type u))
    (hdata : ∃ (H D : X.Sheaf (Type u)),
      (∃ (ι : ∀ a, extensionByEmptyConstant (U := U a) (S a) ⟶ H),
        Nonempty (IsColimit (Cofan.mk H ι))) ∧
      (∃ (ε : ∀ b, extensionByEmptyConstant (U := V b) (T b) ⟶ D),
        Nonempty (IsColimit (Cofan.mk D ε))) ∧
      ∃ (β γ : D ⟶ H) (q : H ⟶ F),
        ∃ hEq : β ≫ q = γ ≫ q, Nonempty (IsColimit (Cofork.ofπ q hEq))) :
    ∃ (Y : TopCat.{u}),
      Finite Y ∧ QuasiSober Y ∧
      ∃ (f : X ⟶ Y),
        Continuous f ∧
        (∀ W : Opens Y, IsCompact (f ⁻¹' (W : Set Y))) ∧
        ∃ (G : Y.Sheaf (Type u)),
          (∀ y : Y, Finite (G.presheaf.stalk y)) ∧
          Nonempty ((TopCat.Sheaf.pullback (Type u) f).obj G ≅ F) := by
  sorry

end TopCat
