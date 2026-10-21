/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.Paper.SfCommonStageWeilCohomology
public import Sheaf.Paper.CommonStageLocallyFree
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.DeligneLaumon.AffineLine.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.CondensedERealization
import Sheaf.Paper.DerivedDirectImageOpenCoherence
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.PbcDescentFunctors
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.LisseIntegralSmallCoefficients
import Sheaf.Paper.A1QbarOpenClosedCohomology
import Sheaf.Paper.DlConstructibleFibresExact

/-! # The natural low-degree open-image sequence for adic Weil sheaves

Source: Stacks 05TD, 05TE, 0D6G; Bhatt--Scholze 6.8; main-20261015,
p-dl-a1-exact.proof.md Steps 1--2 (blueprint: lem-dl-a1-weil-open-image-delta).
The clause packages below state a single theorem. Every operation is the recorded
ordinary or derived common-stage operation. All arrows live in the Weil heart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The prescribed ordinary inverse-image/direct-image adjunction on Weil hearts.
Source: BS 6.8.15, ordinary open image convention
(blueprint: lem-dl-a1-weil-open-image-delta). -/
@[irreducible]
def dlOpenOrdinaryAdjunction (c : Scheme.MiddleExtensionCurve D) :
    zlWeilPull D l hl Ω c.j ⊣ qbarCurveWeilOrdinaryPushforward D l hl Ω c :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _ (zlWeilPull D l hl Ω c.j)
    (qbarCurveWeilPull_isLeftAdjoint D l hl Ω c)

/-- R^r j_* is H^r of the actual geometric derived image with its induced Weil map.
Source: Stacks 05TD; BS 6.8 (blueprint: lem-dl-a1-weil-open-image-delta). -/
def dlOpenHigherImage (c : Scheme.MiddleExtensionCurve D) (r : ℤ) :
    sfCommonStageWeilSheaf D l hl c.U Ω ⥤ sfCommonStageWeilSheaf D l hl c.C Ω :=
  ((sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).inverseImage
    (sfCommonStageWeilForget D l hl c.U Ω)).ι ⋙
    sfModelWeilDerivedPush D l hl Ω c.j ⋙ sfModelWeilCohomology D l hl Ω c.C r

/-- The canonical underlying comparison R^r j_* F = H^r(Rj_* For F).
Only the specified derived-image forgetful isomorphism is used.
Source: p-dl-a1-exact Step 1 (blueprint: lem-dl-a1-weil-open-image-delta). -/
def dlHigherGeometricComparison (c : Scheme.MiddleExtensionCurve D) (r : ℤ)
    (F : sfCommonStageWeilSheaf D l hl c.U Ω) :
    ((dlOpenHigherImage D l hl Ω c r).obj F).obj.carrier ≅
      (sfModelCohomology D l hl Ω c.C r).obj
        ((sfModelDerivedPush D l hl Ω c.j).obj F.obj.carrier) :=
  (sfModelCohomology D l hl Ω c.C r).mapIso
    ((sfModelWeilDerivedPushForget D l hl Ω c.j).app F.obj)

/-- The lisse hypothesis on the recorded geometric carrier, with rank zero allowed.
Source: BS 6.8.3, 6.8.15 (blueprint: lem-dl-a1-weil-open-image-delta). -/
abbrev DlOpenIsLisse (c : Scheme.MiddleExtensionCurve D)
    (F : sfCommonStageWeilSheaf D l hl c.U Ω) : Prop :=
  @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber c.U).left
    (sfWeilPrimeInvertible D l hl c.U) F.obj.carrier

/-- Inputs are precisely short exact sequences of three lisse constructible Weil sheaves.
No condition on weights or integral Frobenius-stable lattices is imposed.
Source: p-dl-a1-exact Step 1 (blueprint: lem-dl-a1-weil-open-image-delta). -/
structure DlOpenLisseSES (c : Scheme.MiddleExtensionCurve D) where
  S : ShortComplex (sfCommonStageWeilSheaf D l hl c.U Ω)
  exact : S.ShortExact
  lisse₁ : @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber c.U).left
    (sfWeilPrimeInvertible D l hl c.U) S.X₁.obj.carrier
  lisse₂ : @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber c.U).left
    (sfWeilPrimeInvertible D l hl c.U) S.X₂.obj.carrier
  lisse₃ : @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber c.U).left
    (sfWeilPrimeInvertible D l hl c.U) S.X₃.obj.carrier

/-- For one curve-open pair: the boundary, its naturality, low-degree exactness,
negative vanishing, degree-zero comparison and both open-counit assertions.
Source: Stacks 05TD, 05TE; p-dl-a1-exact Steps 1--2
(blueprint: lem-dl-a1-weil-open-image-delta). -/
structure DlOpenImageData (c : Scheme.MiddleExtensionCurve D) where
  boundary : ∀ A : DlOpenLisseSES D l hl Ω c,
    (qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj A.S.X₃ ⟶
      (dlOpenHigherImage D l hl Ω c 1).obj A.S.X₁
  exact : ∀ A : DlOpenLisseSES D l hl Ω c,
    (ComposableArrows.mk₄
      (0 : (0 : sfCommonStageWeilSheaf D l hl c.C Ω) ⟶
        (qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj A.S.X₁)
      ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).map A.S.f)
      ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).map A.S.g) (boundary A)).Exact
  naturality : ∀ (A B : DlOpenLisseSES D l hl Ω c) (f : A.S ⟶ B.S),
    (qbarCurveWeilOrdinaryPushforward D l hl Ω c).map f.τ₃ ≫ boundary B =
      boundary A ≫ (dlOpenHigherImage D l hl Ω c 1).map f.τ₁
  negative : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω) (r : ℤ),
    DlOpenIsLisse D l hl Ω c F → r < 0 → IsZero ((dlOpenHigherImage D l hl Ω c r).obj F)
  degreeZero : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω),
    DlOpenIsLisse D l hl Ω c F → ((dlOpenHigherImage D l hl Ω c 0).obj F ≅
      (qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F)
  degreeZero_natural : ∀ (F G : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F) (hG : DlOpenIsLisse D l hl Ω c G) (f : F ⟶ G),
    (dlOpenHigherImage D l hl Ω c 0).map f ≫ (degreeZero G hG).hom =
      (degreeZero F hF).hom ≫ (qbarCurveWeilOrdinaryPushforward D l hl Ω c).map f
  -- The augmentation normalization: H^0 of the adjoint j_*F -> Rj_*F of the ordinary
  -- counit, after the heart truncation maps, is inverse to `degreeZero`.
  degreeZero_normalization : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F),
    ((sfCommonStageStandardTStructure l (D.geometricFiber c.C).left Ω D hl).truncGEπ 0).app
        (((sfCommonStageStandardTStructure l (D.geometricFiber c.C).left Ω D hl).truncLE 0).obj
          ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F).obj.carrier) ≫
      (shiftFunctorZero (generalAlgebraicallyClosedConstructibleCategory l Ω
        (D.geometricFiber c.C).left) ℤ).inv.app _ ≫
      (sfModelCohomology D l hl Ω c.C 0).map
        ((sfModelDerivedAdjunction D l hl Ω c.j).homEquiv _ _
          ((dlOpenOrdinaryAdjunction D l hl Ω c).counit.app F).hom.hom.f) ≫
      (dlHigherGeometricComparison D l hl Ω c 0 F).inv ≫ (degreeZero F hF).hom.hom.hom.f =
    ((sfCommonStageStandardTStructure l (D.geometricFiber c.C).left Ω D hl).truncLEι 0).app
      ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F).obj.carrier
  boundary_formula : ∀ A : DlOpenLisseSES D l hl Ω c,
    ∃ w : A.S.X₃.obj.carrier ⟶ A.S.X₁.obj.carrier⟦(1 : ℤ)⟧,
      Triangle.mk A.S.f.hom.hom.f A.S.g.hom.hom.f w ∈
        distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω
          (D.geometricFiber c.U).left) ∧
      (degreeZero A.S.X₃ A.lisse₃).hom.hom.hom.f ≫ (boundary A).hom.hom.f =
        (dlHigherGeometricComparison D l hl Ω c 0 A.S.X₃).hom ≫
          (sfModelCohomology D l hl Ω c.C 0).map
            (sfModelPushConnecting D l hl Ω c.j w) ≫
          (sfCohomologyShift
            (sfCommonStageStandardTStructure l (D.geometricFiber c.C).left Ω D hl)
            ((sfModelDerivedPush D l hl Ω c.j).obj A.S.X₁.obj.carrier)).hom ≫
          (dlHigherGeometricComparison D l hl Ω c 1 A.S.X₁).inv
  counit : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω),
    DlOpenIsLisse D l hl Ω c F →
      ((zlWeilPull D l hl Ω c.j).obj
        ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F) ≅ F)
  counit_normalization : ∀ F hF, (counit F hF).hom =
    (dlOpenOrdinaryAdjunction D l hl Ω c).counit.app F
  positiveOnOpen : ∀ F : sfCommonStageWeilSheaf D l hl c.U Ω,
    DlOpenIsLisse D l hl Ω c F →
      IsZero ((zlWeilPull D l hl Ω c.j).obj ((dlOpenHigherImage D l hl Ω c 1).obj F))

set_option maxHeartbeats 800000 in
-- The restriction equations compare carriers in nested full subcategories of Weil pairs.
/-- All displayed maps and identifications commute with arbitrary open restriction.
The Cartesian square has horizontal maps b:U_W -> U and a:W -> X. Both d and c
are the recorded dense-open curve data, including the empty and disconnected cases.
The boundary equation asserts compatibility for every morphism of restricted inputs,
so it applies in particular to the actual restricted sequence and all its isomorphic
presentations. Source: Stacks 0D6G (blueprint: lem-dl-a1-weil-open-image-delta). -/
structure DlOpenImageRestriction
    (I : ∀ c : Scheme.MiddleExtensionCurve D, DlOpenImageData D l hl Ω c)
    (c d : Scheme.MiddleExtensionCurve D) (a : d.C ⟶ c.C) (b : d.U ⟶ c.U)
    (h : IsPullback b.left d.j.left c.j.left a.left) where
  ordinary : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω),
    DlOpenIsLisse D l hl Ω c F →
      ((zlWeilPull D l hl Ω a).obj
          ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F) ≅
        (qbarCurveWeilOrdinaryPushforward D l hl Ω d).obj
          ((zlWeilPull D l hl Ω b).obj F))
  ordinary_natural : ∀ (F G : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F) (hG : DlOpenIsLisse D l hl Ω c G) (f : F ⟶ G),
    (zlWeilPull D l hl Ω a).map
        ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).map f) ≫ (ordinary G hG).hom =
      (ordinary F hF).hom ≫ (qbarCurveWeilOrdinaryPushforward D l hl Ω d).map
        ((zlWeilPull D l hl Ω b).map f)
  higher : ∀ (r : ℤ) (F : sfCommonStageWeilSheaf D l hl c.U Ω),
    DlOpenIsLisse D l hl Ω c F →
      ((zlWeilPull D l hl Ω a).obj ((dlOpenHigherImage D l hl Ω c r).obj F) ≅
        (dlOpenHigherImage D l hl Ω d r).obj ((zlWeilPull D l hl Ω b).obj F))
  higher_natural : ∀ (r : ℤ) (F G : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F) (hG : DlOpenIsLisse D l hl Ω c G) (f : F ⟶ G),
    (zlWeilPull D l hl Ω a).map ((dlOpenHigherImage D l hl Ω c r).map f) ≫
        (higher r G hG).hom =
      (higher r F hF).hom ≫ (dlOpenHigherImage D l hl Ω d r).map
        ((zlWeilPull D l hl Ω b).map f)
  higher_normalization : ∀ (r : ℤ) (F : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F),
    (higher r F hF).hom.hom.hom.f =
      (zlPull D l hl Ω a).map (dlHigherGeometricComparison D l hl Ω c r F).hom ≫
        (sfModelPullCohomology D l hl Ω d.C a r).hom.app
          ((sfModelDerivedPush D l hl Ω c.j).obj F.obj.carrier) ≫
        (sfModelCohomology D l hl Ω d.C r).map
          (sfModelDerivedExchange D l hl Ω c.j a b d.j (Over.OverMorphism.ext h.w) F.obj.carrier) ≫
        (dlHigherGeometricComparison D l hl Ω d r ((zlWeilPull D l hl Ω b).obj F)).inv
  degreeZero : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F)
    (hbF : DlOpenIsLisse D l hl Ω d ((zlWeilPull D l hl Ω b).obj F)),
    (zlWeilPull D l hl Ω a).map ((I c).degreeZero F hF).hom ≫ (ordinary F hF).hom =
      (higher 0 F hF).hom ≫ ((I d).degreeZero ((zlWeilPull D l hl Ω b).obj F) hbF).hom
  lisse : ∀ F : sfCommonStageWeilSheaf D l hl c.U Ω,
    DlOpenIsLisse D l hl Ω c F →
      DlOpenIsLisse D l hl Ω d ((zlWeilPull D l hl Ω b).obj F)
  pullSquare : zlWeilPull D l hl Ω a ⋙ zlWeilPull D l hl Ω d.j ≅
    zlWeilPull D l hl Ω c.j ⋙ zlWeilPull D l hl Ω b
  pullSquare_normalization : ∀ F : sfCommonStageWeilSheaf D l hl c.C Ω,
    (pullSquare.hom.app F).hom.hom.f =
      (sfModelPullSquare D l hl Ω c.j a b d.j (Over.OverMorphism.ext h.w)).hom.app F.obj.carrier
  ordinary_normalization : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F),
    (ordinary F hF).hom =
      (dlOpenOrdinaryAdjunction D l hl Ω d).homEquiv
          ((zlWeilPull D l hl Ω a).obj
            ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F))
          ((zlWeilPull D l hl Ω b).obj F)
          (pullSquare.hom.app ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F) ≫
            (zlWeilPull D l hl Ω b).map
              ((dlOpenOrdinaryAdjunction D l hl Ω c).counit.app F))
  counit : ∀ (F : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF : DlOpenIsLisse D l hl Ω c F),
    (zlWeilPull D l hl Ω d.j).map ((ordinary F hF).hom) ≫
        ((I d).counit ((zlWeilPull D l hl Ω b).obj F) (lisse F hF)).hom =
      pullSquare.hom.app ((qbarCurveWeilOrdinaryPushforward D l hl Ω c).obj F) ≫
        (zlWeilPull D l hl Ω b).map ((I c).counit F hF).hom
  boundary : ∀ (A : DlOpenLisseSES D l hl Ω c) (B : DlOpenLisseSES D l hl Ω d)
    (f₁ : (zlWeilPull D l hl Ω b).obj A.S.X₁ ⟶ B.S.X₁)
    (f₂ : (zlWeilPull D l hl Ω b).obj A.S.X₂ ⟶ B.S.X₂)
    (f₃ : (zlWeilPull D l hl Ω b).obj A.S.X₃ ⟶ B.S.X₃),
    (zlWeilPull D l hl Ω b).map A.S.f ≫ f₂ = f₁ ≫ B.S.f →
    (zlWeilPull D l hl Ω b).map A.S.g ≫ f₃ = f₂ ≫ B.S.g →
    (ordinary A.S.X₃ A.lisse₃).hom ≫
        (qbarCurveWeilOrdinaryPushforward D l hl Ω d).map f₃ ≫ (I d).boundary B =
      (zlWeilPull D l hl Ω a).map ((I c).boundary A) ≫
        (higher 1 A.S.X₁ A.lisse₁).hom ≫ (dlOpenHigherImage D l hl Ω d 1).map f₁

/-- The low-degree sequence, its Weil equivariance and natural open compatibility.
Source: Stacks 05TD, 05TE, 0D6G; BS 6.8; p-dl-a1-exact Steps 1--2
(blueprint: lem-dl-a1-weil-open-image-delta).

Proof, following the node's eight steps:
1. Geometric base change gives smooth separated finite-type curves. Finite type over a
field gives Noetherianity and finite dimension. Forget Weil structures; exactness in
constructible fibres gives a short exact sequence in the geometric heart, hence its
unique distinguished heart triangle by lem-weil-heart-short-exact-triangles.
2. The completed-coefficient pushforward comparison identifies the specified reduction
 tower with ordinary total right-derived direct image. The latter is triangulated.
Constructibility and the integral stratified-perfect characterization permit rational
transport. Coherent scalar comparisons and descent give the exact common-stage functor.
3. The bottom-cohomology theorem lem-a1-qbar-open-closed-cohomology gives negative
vanishing, H^0 Rj_* = j_* and the ordinary open counit, at these same coefficients.
4. The cohomology long exact sequence gives 0 -> j_*G1 -> j_*G -> j_*G2 -> H^1 Rj_*G1.
Its boundary is H^0 of the image of the heart-triangle connecting map, followed by the
canonical shift comparison. The triangle axiom and the cokernel property of G2 prove
naturality in short exact sequences, fixing the boundary and its sign.
5. Apply this naturality to Frobenius pullback and the three Weil isomorphisms. The
canonical equivariant direct-image comparison and t-exact Frobenius cohomology comparison
make every arrow, including the boundary, a Weil morphism. Underlying exactness detects
exactness in the Weil heart; no triangulated category of Weil pairs is used.
6. Realize at a finite coefficient field as continuous E-modules. Open direct-image
coherence gives a^* Rj_* = Rj_W* b^*, normalized by the identity on K-injective sections
I(V times_X U). Its successive restriction equation survives realization, scalar
extension and descent; all opens are quasi-compact on these Noetherian curves.
7. Exact restriction commutes with cohomology, kernels and images. Apply the open
comparison to the heart triangle. Its H^0 and shift comparisons give the boundary
square and the degree-zero compatibility equation, as well as compatibility of the
counits. The identity section maps also give compatibility for successive restrictions.
8. Restrict to U. The restricted open immersion is the identity, whose derived image
is the identity. Since each Gi is in the heart, j^* H^1 Rj_* Gi vanishes. In degree
zero the comparison is exactly the ordinary counit. These arguments include empty
opens, disconnected curves, the zero sheaf and j=id, and impose no purity hypothesis. -/
theorem dlOpenImageDelta :
    ∃ I : ∀ c : Scheme.MiddleExtensionCurve D, DlOpenImageData D l hl Ω c,
      ∀ (c d : Scheme.MiddleExtensionCurve D) (a : d.C ⟶ c.C) (b : d.U ⟶ c.U)
        [IsOpenImmersion a.left] [IsOpenImmersion b.left],
        ∀ h : IsPullback b.left d.j.left c.j.left a.left,
          Nonempty (DlOpenImageRestriction D l hl Ω I c d a b h) := by
  sorry

end WeilConjectures
