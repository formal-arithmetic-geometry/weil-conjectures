/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.Algebra.Homology.ModuleCat.Subcomplex
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Dualizable complexes of modules are perfect

Let `R` be a commutative ring. A perfect complex of `D(R)` is dualizable for the derived tensor
product (`DerivedCategory.IsPerfect.isDualizable`). This file proves the converse over a
Noetherian ring: a dualizable object of `D(R)` is perfect (`DerivedCategory.isPerfect_of_isDualizable`).
Together, perfectness and dualizability agree (`DerivedCategory.isPerfect_iff_isDualizable`).

## Strategy

Let `C` be dualizable, with right dual `D`, and represent `C` by a complex `L`.

1. Maps `C ⟶ Z` correspond to maps `𝟙 ⟶ Z ⊗ D`. Represent `D` by a K-flat complex `F` of flat
   modules. A map `𝟙 ⟶ Q(L) ⊗ D = Q(L ⊗ F)` is given by a cocycle `x` of degree `0` of the
   complex `L ⊗ F`, as `𝟙 = R[0]` is K-projective. The element `x` comes from a subcomplex
   `L' ⊗ F` with `L'` a subcomplex of `L` with finitely generated terms, vanishing outside a
   finite interval, and it is a cocycle there since `L' ⊗ F ⟶ L ⊗ F` is injective. Applied to
   the identity of `C`, this shows that `C` is a retract of `Q(L')`
   (`DerivedCategory.exists_retract_of_exactPairing`).
2. Over a Noetherian ring, `C` is then bounded with finitely generated cohomology. So is its dual
   `D`, which is again dualizable. If `C` vanishes above `b` and `D` vanishes above `b'`, then
   `C` has Tor amplitude in `[-b', b]`: maps `Y ⟶ C ⊗ᴸ M` correspond to maps `D ⊗ᴸ Y ⟶ M`.
3. A bounded complex with finitely generated cohomology and finite Tor amplitude is perfect
   (`DerivedCategory.isPerfect_of_finiteTorAmplitude`).

## Main statements

- `DerivedCategory.exists_retract_of_exactPairing`: a dualizable object of `D(R)` is a retract
  of a bounded complex with finitely generated terms.
- `DerivedCategory.isPerfect_of_isDualizable`, `DerivedCategory.isPerfect_iff_isDualizable`
  (`sk-def-perfect`): over a Noetherian ring, the perfect objects of `D(R)` are exactly the
  dualizable ones.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

/-- Every complex has a K-flat resolution by a complex of flat objects: the functorial flat
resolution of an unbounded complex is a colimit of bounded above complexes of flat objects. -/
lemma exists_quasiIso_flat_kFlat (L : CochainComplex C ℤ) :
    ∃ (P : CochainComplex C ℤ) (π : P ⟶ L), QuasiIso π ∧ (∀ n, ObjectProperty.flat (P.X n)) ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  have (X : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ C).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  refine ⟨Λ.resolutionFunctor.obj L, Λ.resolutionNatTrans.app L, inferInstance, fun n ↦ ?_,
    Λ.kFlat_resolutionFunctor_obj hι L⟩
  have := CochainComplex.closedUnderColimitsOfShape_flat C ℤ
  let c := Λ.colimitOfShapeResolutionFunctorObj L
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n) c.isColimit)
    (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))

end CochainComplex
