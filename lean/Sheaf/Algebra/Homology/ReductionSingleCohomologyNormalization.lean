/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Algebra.Homology.ScalarReductionUnitTriangle
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Algebra.Homology.UpperTruncationStepSES
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.CategoryTheory.TorsionSheafConstantModule
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Scalar-reduction cohomology and signed single-sheaf identifications

Source: blueprint main-20261015, Cartier proof paragraph 4; Stacks Project,
Tags 0118, 0145, 0152, 05RS and 06XS.
(blueprint: lem-sfb-reduction-single-cohomology-normalization).

All scalar-extension objects and units are those of the recorded universal cochain model
and its normalized adjunction. The boundary parameter is the last arrow of the specified
multiplication triangle, supplied by `scalarReductionUnitTriangle.resolution_triangle`.
A sheaf cokernel or kernel is allowed any representative with its universal maps.
The single complex in degree `a` is the cohomological notation `Hᵃ(Q)[-a]`.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wZ wR

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace SheafOfModules.ScalarAdjunctionNormalization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [EssentiallySmall.{r} C]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasDerivedCategory.{wZ} (IntegerModules J)]
  (n : ℕ) [HasDerivedCategory.{wR} (ResidueModules J n)]

/-- The canonical R-linear projection τ≤ᵃQ → Hᵃ(Q)[-a], reusing the existing
upper-truncation construction. Its degree-a component is the cycles quotient; every
other component is zero. These components determine the selected map uniquely.
Source: Stacks Tag 0118; `lem-weil-pbc-truncation-step-ses`
(blueprint: lem-sfb-reduction-single-cohomology-normalization). -/
noncomputable def reductionTruncationProjection
    (Q : CochainComplex (ResidueModules J n) ℤ) (a : ℤ) :
    Q.truncLE a ⟶ (CochainComplex.singleFunctor (ResidueModules J n) a).obj (Q.homology a) :=
  (Classical.choose (Classical.choose_spec
    (CochainComplex.exists_upperTruncationStepSES (C := ResidueModules J n)))) Q a

/-- The canonical truncation zigzag is R-linear, quasi-isomorphic, and natural.
Source: Stacks Tags 0118 and 06XS
(blueprint: lem-sfb-reduction-single-cohomology-normalization).
Proof (Step 3): the inclusion induces the identity in retained cohomology degrees.
The projection induces the identity on degree a; in every other degree both its source
and target have zero cohomology. Thus both arrows are quasi-isomorphisms. Chain maps
preserve cycles, boundaries and their quotient, so both naturality squares commute.
All objects and arrows are in the category of residue-module complexes. -/
theorem reduction_single_cohomology_truncation
    (Q : CochainComplex (ResidueModules J n) ℤ) (a : ℤ)
    (hQ : ∀ j : ℤ, j ≠ a → IsZero (Q.homology j)) :
    QuasiIso (Q.ιTruncLE a) ∧ QuasiIso (reductionTruncationProjection J n Q a) ∧
    ∀ (Q' : CochainComplex (ResidueModules J n) ℤ) (f : Q ⟶ Q'),
      CochainComplex.truncLEMap f a ≫ Q'.ιTruncLE a = Q.ιTruncLE a ≫ f ∧
      CochainComplex.truncLEMap f a ≫ reductionTruncationProjection J n Q' a =
        reductionTruncationProjection J n Q a ≫
          (CochainComplex.singleFunctor (ResidueModules J n) a).map
            (HomologicalComplex.homologyMap f a) := by
  sorry

variable (M : DerivedChangeOfRingsCochainModel (quotient J n)) (N : Normalization J n M)

/-- H⁰ of the actual scalar-adjunction unit, with the canonical single comparison.
Source: Stacks Tags 0152 and 05RS
(blueprint: lem-sfb-reduction-single-cohomology-normalization). -/
noncomputable def reductionCohomologyUnit (A : IntegerModules J) :
    A ⟶ (DerivedCategory.homologyFunctor (IntegerModules J) 0).obj
      ((restriction J n).mapDerivedCategory.obj
        (M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A))) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (IntegerModules J) 0).inv.app A ≫
    (DerivedCategory.homologyFunctor (IntegerModules J) 0).map
      (N.derived.unit.app ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A))

/-- The actual boundary on H⁻¹, followed by H⁻¹(A[1]) = H⁰(A[0]) = A.
Source: Stacks Tags 0152 and 05RS
(blueprint: lem-sfb-reduction-single-cohomology-normalization). -/
noncomputable def reductionCohomologyBoundary (A : IntegerModules J)
    (δ : (restriction J n).mapDerivedCategory.obj
        (M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A)) ⟶
      ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A)⟦(1 : ℤ)⟧) :
    (DerivedCategory.homologyFunctor (IntegerModules J) (-1)).obj
      ((restriction J n).mapDerivedCategory.obj
        (M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A))) ⟶ A :=
  (DerivedCategory.homologyFunctor (IntegerModules J) 0).shiftMap δ (-1) 0 (by rfl) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (IntegerModules J) 0).hom.app A

/-- Restriction commutes with the single complex and the shift, using its canonical
termwise comparisons. Source: Stacks Tags 03D7 and 015F
(blueprint: lem-sfb-reduction-single-cohomology-normalization). -/
noncomputable def reductionRestrictionSingleShiftIso (H : ResidueModules J n) :
    (restriction J n).mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (ResidueModules J n) 0).obj H)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj
        ((restriction J n).obj H))⟦(1 : ℤ)⟧ :=
  ((restriction J n).mapDerivedCategory.commShiftIso (1 : ℤ)).app
      ((DerivedCategory.singleFunctor (ResidueModules J n) 0).obj H) ≪≫
    (shiftFunctor (DerivedCategory (IntegerModules J)) (1 : ℤ)).mapIso
      (((restriction J n).mapDerivedCategorySingleFunctor 0).app H)

/-- The canonical cohomology comparison H⁻¹(H[0][1]) ≅ H.
Source: Stacks Tags 05RS and 06XS
(blueprint: lem-sfb-reduction-single-cohomology-normalization). -/
noncomputable def reductionShiftedSingleHomologyIso (H : IntegerModules J) :
    (DerivedCategory.homologyFunctor (IntegerModules J) (-1)).obj
        (((DerivedCategory.singleFunctor (IntegerModules J) 0).obj H)⟦(1 : ℤ)⟧) ≅ H :=
  ((DerivedCategory.homologyFunctor (IntegerModules J) 0).shiftIso
      (1 : ℤ) (-1) 0 (by rfl)).app
      ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj H) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (IntegerModules J) 0).app H

/-- Scalar reduction has cohomology only in degrees -1 and 0, with the stated maps in
its five-term exact sequence. Source: Cartier proof paragraph 4; Stacks Tags 05RS and 0145
(blueprint: lem-sfb-reduction-single-cohomology-normalization).
Proof (Steps 1--2): apply long exact cohomology to the specified multiplication triangle
and to its two signed rotations. Middle-term exactness gives exactness with the actual
H⁻¹(δ) and H⁰(η), rather than unspecified connecting maps. Single-sheaf cohomology is
zero off degree zero, forcing the other groups to vanish. Exactness at each end gives
monicity and epicity. Exact restriction identifies these with the underlying abelian
sheaves and also detects vanishing of residue-module cohomology. -/
theorem reduction_single_cohomology_exact [HasTerminal C] (hn : 1 ≤ n)
    (A : IntegerModules J)
    (δ : (restriction J n).mapDerivedCategory.obj
        (M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A)) ⟶
      ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A)⟦(1 : ℤ)⟧)
    (hδ : Triangle.mk
      (n • 𝟙 ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A))
      (N.derived.unit.app ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A)) δ ∈
        distTriang (DerivedCategory (IntegerModules J))) :
    (∀ j : ℤ, j ≠ -1 → j ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (IntegerModules J) j).obj
        ((restriction J n).mapDerivedCategory.obj
          (M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj A))))) ∧
    Mono (reductionCohomologyBoundary J n M A δ) ∧
    Epi (reductionCohomologyUnit J n M N A) ∧
    ∃ (w₁ : reductionCohomologyBoundary J n M A δ ≫ (n • 𝟙 A) = 0)
      (w₂ : (n • 𝟙 A) ≫ reductionCohomologyUnit J n M N A = 0),
      (ShortComplex.mk (reductionCohomologyBoundary J n M A δ) (n • 𝟙 A) w₁).Exact ∧
      (ShortComplex.mk (n • 𝟙 A) (reductionCohomologyUnit J n M N A) w₂).Exact := by
  sorry

/-- In the monic case, the residue quotient identifies reduction with F̄[0], carrying
its actual derived unit to the quotient. Source: Cartier proof paragraph 4; Stacks 06XS
(blueprint: lem-sfb-reduction-single-cohomology-normalization).
Proof (Steps 3--5): the exact sequence makes H⁻¹ vanish and H⁰(η) a cokernel of n.
Cokernel uniqueness gives the isomorphism H⁰ → F̄. Both sheaves are killed by n, hence
this additive isomorphism is residue-linear by lem-pur-torsion-sheaf-constant-module.
Compose the R-linear single-cohomology truncation zigzag with this isomorphism. Its
restriction carries the unit to p on H⁰, hence on the derived category by full
faithfulness of the single functor. This also proves the claim for any cokernel model. -/
theorem reduction_single_cohomology_monic [HasTerminal C] (hn : 1 ≤ n)
    (F : IntegerModules J) [Mono (n • 𝟙 F)] (Fbar : ResidueModules J n)
    (p : F ⟶ (restriction J n).obj Fbar) (w : (n • 𝟙 F) ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p w)) :
    ∃ α : M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj F) ≅
        (DerivedCategory.singleFunctor (ResidueModules J n) 0).obj Fbar,
      N.derived.unit.app ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj F) ≫
        (restriction J n).mapDerivedCategory.map α.hom ≫
        ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app Fbar =
          (DerivedCategory.singleFunctor (IntegerModules J) 0).map p := by
  sorry

/-- In the epic case, the Kummer boundary and the signed kernel inclusion normalize
reduction as H[1]; its H⁻¹ map is the unique signed kernel comparison.
Source: Cartier proof paragraph 4; Stacks Tags 0145, 0152 and 06XS
(blueprint: lem-sfb-reduction-single-cohomology-normalization).
Proof (Steps 1--7): rotate the SES triangle H → B → B → H[1]. Its last map is -i[1].
TR3 compares the multiplication triangle to this rotation with identities on both B's,
giving u with uη = κ and (-i[1])u = δ. The cohomology exact sequence identifies H⁻¹(u)
with the unique kernel comparison v satisfying (-i)v = H⁻¹(δ); it is invertible.
Epic n also kills H⁰ of reduction. The R-linear truncation zigzag and the R-linearity
of v give α in D(R). Full faithfulness in the single cohomological degree, separately
in D(Z), identifies its restriction with u. Substitution gives both displayed equations.
The H⁻¹ description uses exactly the canonical shift and single comparisons. Uniqueness
of v follows by cancelling the monomorphism -i, without assuming derived restriction
is fully faithful. This includes n = 1 and zero kernel. -/
theorem reduction_single_cohomology_epic [HasTerminal C] (hn : 1 ≤ n)
    (B : IntegerModules J) (H : ResidueModules J n)
    (i : (restriction J n).obj H ⟶ B) (w : i ≫ (n • 𝟙 B) = 0)
    (hS : (ShortComplex.mk i (n • 𝟙 B) w).ShortExact)
    (δ : (restriction J n).mapDerivedCategory.obj
        (M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj B)) ⟶
      ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj B)⟦(1 : ℤ)⟧)
    (hδ : Triangle.mk
      (n • 𝟙 ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj B))
      (N.derived.unit.app ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj B)) δ ∈
        distTriang (DerivedCategory (IntegerModules J))) :
    ∃ α : M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj B) ≅
        ((DerivedCategory.singleFunctor (ResidueModules J n) 0).obj H)⟦(1 : ℤ)⟧,
      (N.derived.unit.app ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj B) ≫
        (restriction J n).mapDerivedCategory.map α.hom ≫
        (reductionRestrictionSingleShiftIso J n H).hom = hS.singleδ) ∧
      ((restriction J n).mapDerivedCategory.map α.hom ≫
        (reductionRestrictionSingleShiftIso J n H).hom ≫
        (-((DerivedCategory.singleFunctor (IntegerModules J) 0).map i)⟦(1 : ℤ)⟧') = δ) ∧
      ∃ v : (DerivedCategory.homologyFunctor (IntegerModules J) (-1)).obj
          ((restriction J n).mapDerivedCategory.obj
            (M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj B))) ≅
          (restriction J n).obj H,
        v.hom = (DerivedCategory.homologyFunctor (IntegerModules J) (-1)).map
            ((restriction J n).mapDerivedCategory.map α.hom ≫
              (reductionRestrictionSingleShiftIso J n H).hom) ≫
            (reductionShiftedSingleHomologyIso J ((restriction J n).obj H)).hom ∧
        v.hom ≫ (-i) = reductionCohomologyBoundary J n M B δ ∧
        ∀ v' : (DerivedCategory.homologyFunctor (IntegerModules J) (-1)).obj
            ((restriction J n).mapDerivedCategory.obj
              (M.T.obj ((DerivedCategory.singleFunctor (IntegerModules J) 0).obj B))) ≅
            (restriction J n).obj H,
          v'.hom ≫ (-i) = reductionCohomologyBoundary J n M B δ → v' = v := by
  sorry

end SheafOfModules.ScalarAdjunctionNormalization
