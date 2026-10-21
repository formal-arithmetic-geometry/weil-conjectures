/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.DerivedReductionResolutionIndependence
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.MixedTensorPointwiseLeftDerived
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.PrincipalQuotientQuasiIso

/-! # Exact sections and the principal scalar-extension unit

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A6;
derived.tex, Tag 0FND (blueprint: lem-coef-exact-sections-reduction-unit).

The coefficient data and all derived tensor models are those of `PrincipalReduction.Setup`.
The restriction square below is the identity on sections, with its scalar linearity supplied
by the specified coefficient square. In particular it is a canonical identification.

## Main statements

* `SheafOfModules.PrincipalReduction.Setup.exactSectionsReductionUnit`: the natural
  isomorphism, its normalized unit equation, uniqueness, and resolution formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v r wO wS wR wA

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules.PrincipalReduction.Setup

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Type r} [CommRing R] (D : Setup (C := C) (J := J) R)

/-- Sheaf coefficient restriction, using the recorded Mathlib functor.
Source: Stacks 03DA, 07A6 (blueprint: lem-coef-exact-sections-reduction-unit). -/
abbrev reductionRestriction :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map D.φ)

/-- Exactness of restriction, supplied by the normalized coefficient adjunction.
Source: Stacks 03DA (blueprint: lem-coef-exact-sections-reduction-unit). -/
instance reductionRestrictionLimits : PreservesFiniteLimits D.reductionRestriction :=
  (sheafRingCoefficientOrdinaryAdjunction D.φ).choose

/-- Exactness of restriction, supplied by the normalized coefficient adjunction.
Source: Stacks 03DA (blueprint: lem-coef-exact-sections-reduction-unit). -/
instance reductionRestrictionColimits : PreservesFiniteColimits D.reductionRestriction :=
  (sheafRingCoefficientOrdinaryAdjunction D.φ).choose_spec.choose

/-- Sections and coefficient restriction commute by the identity on the underlying group.
Source: Stacks 03DA, 06YY (blueprint: lem-coef-exact-sections-reduction-unit). -/
def sectionsReductionRestrictionIso :
    D.reductionRestriction ⋙ D.sections ≅
      D.quotientSections ⋙ ModuleCat.restrictScalars D.quotientMap :=
  NatIso.ofComponents (fun M ↦
    (LinearEquiv.toModuleIso
      ({
        toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a x ↦ by
          change ((M.val.obj (op D.U)).smul ((D.φ.hom.app (op D.U)) (D.ρ a))).hom x =
            ((M.val.obj (op D.U)).smul (D.quotientSectionsMap (D.quotientMap a))).hom x
          rw [D.quotient_sections_comm] } :
        ((D.reductionRestriction ⋙ D.sections).obj M) ≃ₗ[R]
          ((D.quotientSections ⋙ ModuleCat.restrictScalars D.quotientMap).obj M))))
    (by intro M N f; ext x; rfl)

variable [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)]

/-- The derived restriction square induced by the identity on section groups.
Source: Stacks 05RU, 06YY (blueprint: lem-coef-exact-sections-reduction-unit). -/
def derivedSectionsReductionRestrictionIso :
    D.reductionRestriction.mapDerivedCategory ⋙ D.G ≅
      D.G' ⋙ (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso D.reductionRestriction D.sections).symm ≪≫
    Functor.mapDerivedCategoryNatIso D.sectionsReductionRestrictionIso ≪≫
    Functor.mapDerivedCategoryCompIso D.quotientSections
      (ModuleCat.restrictScalars D.quotientMap)

/-- The ordinary quotient representative: extend q and then take quotient sections.
Source: Stacks 06Y6, 06YY (blueprint: lem-coef-exact-sections-reduction-unit). -/
def reductionRepresentative
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    {Q : CochainComplex (ModuleCat.{r} R) ℤ}
    (q : Q ⟶ (D.sections.mapHomologicalComplex (.up ℤ)).obj P) :=
  ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).map q ≫
    (D.theta P hf).hom

/-- The ordinary extension/restriction adjunct of the quotient representative.
Source: Stacks 07A6, 0FND (blueprint: lem-coef-exact-sections-reduction-unit). -/
def reductionRepresentativeAdjunct
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    {Q : CochainComplex (ModuleCat.{r} R) ℤ}
    (q : Q ⟶ (D.sections.mapHomologicalComplex (.up ℤ)).obj P) :=
  ((ModuleCat.extendRestrictScalarsAdj D.quotientMap).mapHomologicalComplex (.up ℤ)).homEquiv
    Q _ (D.reductionRepresentative P hf q)

/-- Exact sections commute with principal derived reduction, with its actual normalized
scalar-extension unit and both resolution formulas. The coefficient ring need not be a domain.
The auxiliary ordinary adjunction is fixed by its sectionwise formula, and the two derived
adjunctions are fixed by their K-flat unit formulas. Thus none is an arbitrary adjunction.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A6;
derived.tex, Tag 0FND (blueprint: lem-coef-exact-sections-reduction-unit).

Proof:
1. Restriction changes no underlying abelian sheaf. The coefficient square gives the
identity-on-sections restriction square. Exact sections preserve kernels and cokernels,
hence cohomology and quasi-isomorphisms, so this square descends to derived categories.
2. Resolve N by a flat-term K-flat sheaf complex P (lem-pc-kflat-resolution). Tensor the
coefficient short exact sequence with its flat terms. Multiplication by t is injective on
Gamma P. Exact sections give theta_P, and resolution-independence gives theta_P c_Gamma P
and its coherence (lem-pod-derived-reduction-sheaf-resolution-independence).
3. Resolve Gamma P by an ordinary flat-term K-flat Q (lem-pc-source-module-kflat-resolution).
Flat tensor exactness makes t injective on Q (lem-weil-pbc-flat-tensor-exact). Specializing
the mixed tensor counit to A[0] gives c_C L(q) = Q_A(q-bar) c_Q, so the representative is
q-bar followed by theta_P; no K-flatness of Gamma P is used
(lem-pc-mixed-tensor-pointwise-left-derived, lem-pc-derived-tensor-second-factor-functor).
4. The principal-quotient quasi-isomorphism lemma makes q-bar a quasi-isomorphism
(lem-pod-principal-quotient-quasi-iso). The K-flat counit c_Q and L(q) are invertible,
so c_C, and then theta_P c_C, are invertible.
5. Use the normalized coefficient adjunction on the site and on the point site
(lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-pur-derived-change-of-rings).
Uniqueness of left derived functors identifies the point-site extension and mixed tensor,
compatibly with their counits. Their units on P and Q are the quotient projections.
Naturality and c_C L(q) = Q_A(q-bar) c_Q give Res(beta_P) u_C Q_R(q) = Q_R(pi_C q).
Cancel the invertible Q_R(q). The transpose on representatives sends x to q(x) modulo t.
6. Transport beta_P along P to N. Resolution-independence makes the result independent of
P. Naturality of the units proves the displayed unit equation. The adjunction bijection
makes its solution unique, and its injectivity proves naturality for every derived map.
7. Every ordinary resolution q represents the same intrinsic theta_P c_C, so both its
map and its adjunct are independent of q. Transport along any sheaf resolution gives the
same intrinsic comparison. These observations give both independence assertions.
-/
theorem exactSectionsReductionUnit
    (ht : Function.Injective (fun x : R ↦ D.t * x)) :
    ∃ a : D.extension.E ⊣ D.reductionRestriction,
      (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))
        (V : Cᵒᵖ) (x : M.val.obj V),
        ((eqToHom (D.extension.obj_eq M)).val.app V)
            ((a.unit.app M).val.app V x) =
          ((PresheafOfModules.sheafificationAdjunction
            (R := derivedChangeRingIndependentCoefficients J D.S) (𝟙 _)).unit.app
              (changeOfRingsPresheaf D.φ M)).app V
                ((1 : D.S.obj.obj V) ⊗ₜ[D.O.obj.obj V, (D.φ.hom.app V).hom] x)) ∧
      ∃ b : D.T ⊣ D.reductionRestriction.mapDerivedCategory,
        (∀ (P : CochainComplex
            (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P →
          (∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) →
          b.unit.app (DerivedCategory.Q.obj P) ≫
              D.reductionRestriction.mapDerivedCategory.map (D.extension.ε.app P) ≫
              D.reductionRestriction.mapDerivedCategoryFactors.hom.app
                (D.quotientComplex.obj P) =
            DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
        ∃ d : D.L ⊣ (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory,
          (∀ (Q : CochainComplex (ModuleCat.{r} R) ℤ),
            (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).kFlat Q →
            (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
            d.unit.app (DerivedCategory.Q.obj Q) ≫
                (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory.map (D.c Q) ≫
                (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategoryFactors.hom.app
                  (((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj Q) =
              DerivedCategory.Q.map
                (((ModuleCat.extendRestrictScalarsAdj D.quotientMap).mapHomologicalComplex
                  (.up ℤ)).unit.app Q)) ∧
          ∃ α : D.G ⋙ D.L ≅ D.T ⋙ D.G',
            (∀ N : DerivedCategory
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)),
              d.unit.app (D.G.obj N) ≫
                  (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory.map
                    (α.hom.app N) =
                D.G.map (b.unit.app N) ≫
                  D.derivedSectionsReductionRestrictionIso.hom.app (D.T.obj N)) ∧
            (∀ (N : DerivedCategory
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)))
              (f : (D.G ⋙ D.L).obj N ⟶ (D.T ⋙ D.G').obj N),
              d.unit.app (D.G.obj N) ≫
                  (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory.map f =
                D.G.map (b.unit.app N) ≫
                  D.derivedSectionsReductionRestrictionIso.hom.app (D.T.obj N) →
              f = α.hom.app N) ∧
            (∀ (P : CochainComplex
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
              (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
              (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)),
              α.hom.app (DerivedCategory.Q.obj P) = D.alpha P hP hf) ∧
            (∀ (P : CochainComplex
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
              (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
              (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
              (Q : CochainComplex (ModuleCat.{r} R) ℤ)
              (q : Q ⟶ (D.sections.mapHomologicalComplex (.up ℤ)).obj P),
              QuasiIso q →
              (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).kFlat Q →
              (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
              (∀ (i : ℤ) (x : Q.X i),
                (D.reductionRepresentative P hf q).f i
                    ((1 : D.A) ⊗ₜ[R, D.quotientMap] x) =
                  D.quotientSection (P.X i) (q.f i x)) ∧
              (∀ (i : ℤ) (x : Q.X i),
                (D.reductionRepresentativeAdjunct P hf q).f i x =
                  D.quotientSection (P.X i) (q.f i x)) ∧
              (D.L.map (DerivedCategory.Q.map q) ≫
                  D.L.map (D.sections.mapDerivedCategoryFactors.inv.app P) ≫
                  α.hom.app (DerivedCategory.Q.obj P) ≫
                  D.G'.map (D.modelIso P hP).hom ≫
                  D.quotientSections.mapDerivedCategoryFactors.hom.app (D.quotientComplex.obj P) =
                D.c Q ≫ DerivedCategory.Q.map (D.reductionRepresentative P hf q)) ∧
              (d.homEquiv _ _
                  (D.c Q ≫ DerivedCategory.Q.map (D.reductionRepresentative P hf q)) =
                DerivedCategory.Q.map (D.reductionRepresentativeAdjunct P hf q) ≫
                  (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategoryFactors.inv.app
                    ((D.quotientSections.mapHomologicalComplex (.up ℤ)).obj
                      (D.quotientComplex.obj P)))) ∧
            (∀ (M P : CochainComplex
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
              (p : P ⟶ M) [QuasiIso p]
              (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
              (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)),
              D.resolvedComparison p hP hf = α.hom.app (DerivedCategory.Q.obj M)) := by
  sorry

end SheafOfModules.PrincipalReduction.Setup
