/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.WeilDistTriang
public import WeilConjectures.TraceFormula.WeilTrace
public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-!

# Additivity of the local trace along distinguished triangles of Weil objects

For a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil objects
(`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang`), the local traces satisfy
`t_{n+1}(B; x̄) = t_{n+1}(A; x̄) + t_{n+1}(C; x̄)`
(`ProEtale.CondensedRing.weilStalkSupertrace_eq_add_of_isDistTriang`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- **Additivity of the local trace along distinguished triangles, for finite free stalks.**
Assume that `End (𝟙_ Mod_{Spec k̄})` is a field and that the stalks at `x̄` of the homology sheaves
of Weil objects are finite free. Then for a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil
objects for `e`, `t_{n+1}(B; x̄) = t_{n+1}(A; x̄) + t_{n+1}(C; x̄)`: the homology sheaves form a
long exact sequence of Weil sheaves, whose stalks at `x̄` form a long exact sequence with the
Frobenius operators commuting with all the maps (`superTrace_eq_add_of_exact`). -/
theorem weilStalkSupertrace_eq_add_of_isDistTriang_of_isFiniteFree {e : Y ≅ Y} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ Y.left)
    (hx : x ≫ (e.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x)
    (hK : ∀ t : End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))), t ≠ 0 → IsIso t)
    (h₁ : (1 : End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k)))) ≠ 0)
    (hfree : ∀ (K : WeilBoundedConstructible ℓ e.hom) (j : ℤ),
      letI := Abelian.hasFiniteBiproducts (C := GeometricPointMod ℓ (AlgebraicClosure k))
      IsFiniteFree ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
        ((DerivedCategory.homologyFunctor _ j).obj K.carrier.obj)))
    {A B C : WeilBoundedConstructible ℓ e.hom} {a : A ⟶ B} {b : B ⟶ C}
    (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    weilStalkSupertrace ℓ n x hx B =
      weilStalkSupertrace ℓ n x hx A + weilStalkSupertrace ℓ n x hx C :=
  sorry

/-- **Additivity of the local trace along distinguished triangles of Weil objects** (standard
input, still `sorry`): for a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil objects for `e`,
`t_{n+1}(B; x̄) = t_{n+1}(A; x̄) + t_{n+1}(C; x̄)`. The long exact sequence of homology sheaves
`Hʲ(A) ⟶ Hʲ(B) ⟶ Hʲ(C) ⟶ Hʲ⁺¹(A)` is one of Weil sheaves, the connecting morphisms commuting with
the Frobenius structures; the stalk functor at `x̄` is exact, the stalks of the homology sheaves of
constructible complexes are finite-dimensional `ℚ̄_ℓ`-vector spaces, and the alternating sum of
the traces of an endomorphism of a bounded exact sequence of finite-dimensional vector spaces
vanishes. -/
theorem weilStalkSupertrace_eq_add_of_isDistTriang {e : Y ≅ Y} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ Y.left)
    (hx : x ≫ (e.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x)
    {A B C : WeilBoundedConstructible ℓ e.hom} {a : A ⟶ B} {b : B ⟶ C}
    (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    weilStalkSupertrace ℓ n x hx B =
      weilStalkSupertrace ℓ n x hx A + weilStalkSupertrace ℓ n x hx C :=
  weilStalkSupertrace_eq_add_of_isDistTriang_of_isFiniteFree ℓ n x hx
    (isIso_of_ne_zero_end_tensorUnit ℓ (instΩ := AlgebraicClosure.instCommRing k)
      (Field.toIsField _) IsField.isSepClosed_toField)
    (one_ne_zero_end_tensorUnit ℓ (instΩ := AlgebraicClosure.instCommRing k)
      (Field.toIsField _) IsField.isSepClosed_toField)
    (fun K j ↦ isFiniteFree_upperStar_homology ℓ (instΩ := AlgebraicClosure.instCommRing k)
      (Field.toIsField _) IsField.isSepClosed_toField K.carrier j x) h

end AlgebraicGeometry.ProEtale.CondensedRing
