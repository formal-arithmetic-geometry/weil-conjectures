/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # The derived scalar-extension unit and distinguished triangles

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT, 06YY;
derived.tex, Tags 014V, 015F and 06XN
(blueprint: lem-weil-pbc-scalar-extension-unit-triangles).

The ordinary functor is specified by its existing tensor objects and maps. The
universal derived pair is arbitrary, with the counit-compatible canonical shift.
Restriction's exactness is asserted, rather than assumed. The roof predicate
specifies its comparison by the derived counit, including every K-flat resolution.
-/

@[expose] public section

set_option autoImplicit false

universe u v r wR wS a b va vb

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace SheafOfModules

/-- Apply an ordinary coefficient natural transformation termwise to complexes.
The identity and composite comparison maps have identity components, so its component
in degree `n` is precisely `ι.app (P.X n)`.
Source: Stacks Project, Tag 03EK and the explicit complex map in Tag 06YY
(blueprint: lem-weil-pbc-scalar-extension-unit-triangles). -/
noncomputable def scalarExtensionCoefficientComplexMap
    {A : Type a} [Category.{va} A] [Preadditive A]
    {B : Type b} [Category.{vb} B] [Preadditive B]
    (E : A ⥤ B) [E.Additive] (V : B ⥤ A) [V.Additive]
    (ι : 𝟭 A ⟶ E ⋙ V) (P : CochainComplex A ℤ) :
    P ⟶ (V.mapHomologicalComplex (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app P ≫
    (NatTrans.mapHomologicalComplex ι (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ V)) (.up ℤ)).inv.app P

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

/-- The coefficient roof characterization, including its canonical comparison.
`c` is the inverse of the derived image of the resolution followed by the counit:
`F(Qp) ≫ c.hom = ε_P`. The second equality says that the roof with denominator `Qp`
and numerator the termwise coefficient map represents `η_C`. The comparison is an
isomorphism for every K-flat resolution, with no flatness condition on its terms.
Source: Stacks Project, Tags 06YS, 06YT and 06YY
(blueprint: lem-weil-pbc-scalar-extension-unit-triangles). -/
def ScalarExtensionUnitRoof
    (φ : R ⟶ S)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)) [E.Additive]
    [PreservesFiniteLimits
      (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))]
    [PreservesFiniteColimits
      (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))]
    (F : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ι : 𝟭 (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⟶
      E ⋙ restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))
    (η : 𝟭 (DerivedCategory
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))) ⟶
      F ⋙ (restrictScalars.{r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory) : Prop :=
  ∀ (P K : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (p : P ⟶ K), CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      QuasiIso p →
    ∃ c : F.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P),
      F.map (DerivedCategory.Q.map p) ≫ c.hom = ε.app P ∧
      DerivedCategory.Q.map p ≫ η.app (DerivedCategory.Q.obj K) ≫
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          φ)).mapDerivedCategory.map
          c.hom ≫
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          φ)).mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map (scalarExtensionCoefficientComplexMap E
          (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) ι P)

/-- The canonical derived coefficient transformation is independent of resolutions,
commutes with the canonical shift and gives morphisms of distinguished triangles.
The parameters `E,h,hmap` specify ordinary tensor extension exactly, and `F,ε`
specify its universal left derived functor. The shift hypothesis on `ε` specifies
its canonical shift structure, rather than an arbitrary triangulated structure.
Source: Stacks Project, Tags 03EK, 06YS, 06YT, 06YY and derived.tex Tags 014V, 015F
(blueprint: lem-weil-pbc-scalar-extension-unit-triangles).

Proof:
1. Define the ordinary scalar map sectionwise by x to 1 tensor x, followed by
sheafification (def-pur-sheaf-tensor-product). It is linear and natural and commutes
with differentials. Termwise tensor preserves homotopies. Restriction preserves the
same kernels and sheafified cokernels, so is exact (def-pc-sheaf-restrict-scalars).
The exact derived factorization (lem-weil-pbc-exact-functor-derived-factorization)
identifies derived restriction of a complex with its termwise restriction.
2. Restrict to K-flat homotopy complexes with flat terms. They localize to D(R)
(lem-weil-pbc-site-derived-tensor-descent); the counit is invertible there
(lem-pur-derived-change-of-rings, lem-pur-left-derived-from-kflat-class). Compose
the localized scalar map with the inverse counit and restriction comparison.
The localization universal property (lem-weil-pbc-localization-universal-property)
extends this uniquely to a natural transformation eta on D(R).
3. Naturality at a flat-term K-flat resolution gives precisely the displayed roof.
Every complex has such a resolution (lem-pc-kflat-resolution), proving uniqueness.
4. For an arbitrary K-flat resolution P to K, resolve P by a flat-term K-flat T.
Both tensor images of T to P are quasi-isomorphic (lem-pur-derived-change-of-rings).
The equation E(t)i_T = i_P t and counit naturality identify the two roof formulas.
Thus the characterization covers all K-flat resolutions and is independent of them.
5. K-flatness is stable under shift (def-pc-kflat-complex). Scalar extension and
restriction have identity termwise shift comparisons and i_(P[1]) = i_P[1].
The counit-compatible shift (lem-sbc-derived-scalar-extension-counit-shift) and
exact derived restriction comparison turn these into the asserted equation on
K-flat models; localization extends the equality to all derived objects.
6. Both functors with these canonical shifts are triangulated. The first two
triangle squares are naturality. Naturality at the connecting arrow followed by
step 5 gives the third square, including its sign. No flatness of S, bounds,
constructibility, or points enter the argument. -/
theorem exists_scalarExtensionUnit_triangles
    (φ : R ⟶ S)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R),
      E.obj M = changeOfRings.{v, u, r} φ M)
    (hmap : ∀ {M N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)}
      (f : M ⟶ N),
      E.map f = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M f ≫ eqToHom (h N).symm)
    [E.Additive]
    (F : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ))]
    [F.CommShift ℤ] [NatTrans.CommShift ε ℤ] :
    ∃ (_ : PreservesFiniteLimits
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)))
      (_ : PreservesFiniteColimits
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))),
      F.IsTriangulated ∧
      ∃ ι : 𝟭 (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⟶
          E ⋙ restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ),
        (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
          (U : Cᵒᵖ) (x : M.val.obj U),
          (eqToHom (h M)).val.app U ((ι.app M).val.app U x) =
            (((PresheafOfModules.sheafificationAdjunction.{r}
              (J := J) (R := derivedChangeRingIndependentCoefficients J S)
              (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
              (changeOfRingsPresheaf.{v, u, r} φ M)).app U
              ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
                (M.val.obj U) x))) ∧
        ∃ η : 𝟭 (DerivedCategory
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))) ⟶
            F ⋙ (restrictScalars.{r}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory,
          ScalarExtensionUnitRoof φ E F ε ι η ∧
          (∀ η' : 𝟭 (DerivedCategory (ringedSiteModules.{r}
            (derivedChangeRingIndependentCoefficients J R))) ⟶
              F ⋙ (restrictScalars.{r}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory,
            ScalarExtensionUnitRoof φ E F ε ι η' → η' = η) ∧
          (∀ X : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients
            J R)),
            η.app ((shiftFunctor _ (1 : ℤ)).obj X) ≫
            ((F ⋙ (restrictScalars.{r}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map
                φ)).mapDerivedCategory).commShiftIso
                (1 : ℤ)).hom.app X = (shiftFunctor _ (1 : ℤ)).map (η.app X)) ∧
          (∀ T : Triangle (DerivedCategory
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))),
            T ∈ distTriang _ →
            (F ⋙ (restrictScalars.{r}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map
                φ)).mapDerivedCategory).mapTriangle.obj
                T ∈ distTriang _ ∧
            ∃ m : T ⟶ (F ⋙ (restrictScalars.{r}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map
                  φ)).mapDerivedCategory).mapTriangle.obj
                T,
              m.hom₁ = η.app T.obj₁ ∧ m.hom₂ = η.app T.obj₂ ∧ m.hom₃ = η.app T.obj₃) := by
  sorry

end SheafOfModules
