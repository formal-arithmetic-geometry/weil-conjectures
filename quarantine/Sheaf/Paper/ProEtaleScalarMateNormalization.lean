/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.SecSmoothPurity.DirectImageScalarOperations
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.ProEtaleProjectionFormulaArrows
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-! # Pro-etale scalar mate normalization

Source: Stacks Project, Tag 0B56, equation-projection-formula-map
(blueprint: lem-fix-proetale-scalar-mate-normalization).
-/

@[expose] public section

set_option autoImplicit false


universe u
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The actual scalar restriction, with unchanged underlying abelian sheaf.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (Scheme.proEtaleConstantRingMap (T := W) φ)

/-- The coefficient B_W with its A_W action, without deriving or resolving B.
Source: Stacks 0B56 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateCoefficient {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (scalarMateRestriction φ W).obj (SheafOfModules.unit
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B)))

/-- The degree-zero coefficient complex B_W, as an A_W-module complex.
Source: Stacks 0B56 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateCoefficientComplex {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (CochainComplex.singleFunctor (Scheme.proEtaleRingModules W
    (Scheme.proEtaleConstantRing W A)) (0 : ℤ)).obj (scalarMateCoefficient φ W)

/-- The existing ordinary tensor with B as its last factor.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateOrdinaryTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A)).flip.obj
    (scalarMateCoefficient φ W)

/-- The original sheafification image of b tensor m in scalar extension.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateTensorSection {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (M : Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (b : (Scheme.proEtaleConstantRing W B).obj.obj U)
    (m : M.val.obj U) :
    (SheafOfModules.changeOfRings (Scheme.proEtaleConstantRingMap (T := W) φ) M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B))
    (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (Scheme.proEtaleConstantRingMap (T := W) φ) M)).app U)
    (b ⊗ₜ[_, ((Scheme.proEtaleConstantRingMap (T := W) φ).hom.app U).hom] m)

/-- The normalization on all sectionwise pure tensors, including nonconstant local scalars.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
def IsScalarMateOrdinaryTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (e : Scheme.proEtaleRingExtension (Scheme.proEtaleConstantRingMap (T := W) φ) ⋙
      scalarMateRestriction φ W ≅ scalarMateOrdinaryTensor φ W) : Prop :=
  ∀ (M : Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (b : (Scheme.proEtaleConstantRing W B).obj.obj U)
    (m : M.val.obj U),
    ((scalarMateRestriction φ W).map
      (eqToHom (Scheme.proEtaleRingExtension_obj
        (Scheme.proEtaleConstantRingMap (T := W) φ) M).symm) ≫
      e.hom.app M).val.app U (scalarMateTensorSection φ W M U b m) =
        Scheme.proEtaleTensorPair W (Scheme.proEtaleConstantRing W A) M
          (scalarMateCoefficient φ W) U m b

/-- The canonical ordinary identification, uniquely fixed by balanced pure tensors.
Source: Stacks 03EK, 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization).
Proof: the restricted scalar extension and tensor have the same balanced tensor
abelian presheaf, with factors reversed. Sheafify this identification. The inverse
reverses the factors back; both composites fix pure tensors. The balancing relation
proves linearity, and id tensor a proves naturality. Sheafification uniqueness proves
that the displayed formula determines the natural isomorphism uniquely. This is
step 1 of the node, retaining its specified normalization. -/
theorem scalarMateOrdinaryTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u}) :
    ∃! e : Scheme.proEtaleRingExtension (Scheme.proEtaleConstantRingMap (T := W) φ) ⋙
        scalarMateRestriction φ W ≅ scalarMateOrdinaryTensor φ W,
      IsScalarMateOrdinaryTensor φ W e := by
  sorry

/-- The uniquely normalized ordinary identification; its data are determined by the formula.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateOrdinaryTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u}) :=
  Classical.choose (scalarMateOrdinaryTensorIso_existsUnique φ W).exists

/-- The canonical restriction/direct-image comparison of the recorded ring-sheaf adjunction.
Source: Stacks 0D6E (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateRestrictionPush
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  Scheme.proEtaleRingRestrictionDerivedDirectImage f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm


/-- On complexes, reverse the balanced tensors degreewise and use the degree-zero
single-factor identification. This is an actual chain isomorphism.
Source: Stacks 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateOrdinaryComplexIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (P : CochainComplex (Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso (scalarMateOrdinaryTensorIso φ W)
    (ComplexShape.up ℤ)).app P ≪≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A))
        (scalarMateCoefficient φ W) P).symm

/-- The full normalization of h on two flat K-flat representatives, resolving B too.
The equation uses Q → B[0] only after tensoring with the K-flat first factor.
Source: Stacks 06YY, 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
def IsScalarMateDerivedTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A))
    (h : directImageScalarExtension φ W ⋙ (scalarMateRestriction φ W).mapDerivedCategory ≅
      (Functor.curryObj a.tensor).flip.obj
        (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W))) : Prop :=
  ∀ (P Q : CochainComplex (Scheme.proEtaleRingModules W
      (Scheme.proEtaleConstantRing W A)) ℤ)
    (hp : Scheme.proEtaleFlatRepresentatives W (Scheme.proEtaleConstantRing W A) P)
    (hq : Scheme.proEtaleFlatRepresentatives W (Scheme.proEtaleConstantRing W A) Q)
    (q : Q ⟶ scalarMateCoefficientComplex φ W), QuasiIso q →
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) ≫
      h.inv.app (DerivedCategory.Q.obj P) ≫
      (scalarMateRestriction φ W).mapDerivedCategory.map
        ((Scheme.proEtaleRingDerivedExtensionCounit
          (Scheme.proEtaleConstantRingMap (T := W) φ)).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
      (scalarMateRestriction φ W).mapDerivedCategoryFactorsh.hom.app
        (((Scheme.proEtaleRingExtension
          (Scheme.proEtaleConstantRingMap (T := W) φ)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A))
        (ComplexShape.up ℤ) ≫ (scalarMateOrdinaryComplexIso φ W P).inv)

/-- The restricted extension is the derived tensor with B, with its full normalization.
Source: Stacks 06YY, 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization).
Proof: use step 1 of the node. Resolve the first input P and B[0] by flat K-flat
complexes. The ordinary complex identification is identity on the balanced tensor,
with the symmetry putting B last. Tensoring P with the resolution of B is a
quasi-isomorphism because P is K-flat, even when B is nonflat. The scalar derived
counit is invertible on P. These maps construct h and give the displayed equation.
Naturality descends from the ordinary comparison through the resolving-class
localization. Every derived object has such a representative, so the equation
uniquely determines h, including compatibility with changes of resolutions. -/
theorem scalarMateDerivedTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A)) :
    ∃! h : directImageScalarExtension φ W ⋙ (scalarMateRestriction φ W).mapDerivedCategory ≅
        (Functor.curryObj a.tensor).flip.obj
          (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W)),
      IsScalarMateDerivedTensor φ W a h := by
  sorry

/-- The comparison h selected by its unique representative normalization.
Source: Stacks 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateDerivedTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A)) :=
  Classical.choose (scalarMateDerivedTensorIso_existsUnique φ W a).exists


/-- The tensor unit in the existing constant-ring module category.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateUnit (B : Type u) [CommRing B] (W : Scheme.{u}) :=
  SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B))

/-- The normalized ordinary B-unit pullback, supplied by the projection-arrow interface.
Source: Stacks 03EL (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateUnitPullback (B : Type u) [CommRing B]
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  Classical.choose (Scheme.proEtaleProjectionUnit_existsUnique f
    (Scheme.proEtaleConstantRing V B) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingComparison f B)).exists

/-- The ordinary identification u_A^*(B_V)=B_T, using scalar restriction and unit pullback.
Source: Stacks 03EL, 0D6D (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateCoefficientPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  letI := Scheme.proEtaleRingRestrictionPullbackInv_isIso f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  (asIso (Scheme.proEtaleRingRestrictionPullbackInv f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm)).app (scalarMateUnit B V) ≪≫
    (scalarMateRestriction φ T).mapIso (scalarMateUnitPullback B f)

/-- The coefficient identification on degree-zero complexes, with exact pullback factors.
Source: Stacks 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateDerivedCoefficientPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  (Scheme.proEtaleRingDerivedPullbackFactors f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
    (Scheme.proEtaleConstantRingComparison f A)).app (scalarMateCoefficientComplex φ V) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.proEtaleConstantRingPullback A f) (ComplexShape.up ℤ) 0).app
          (scalarMateCoefficient φ V)) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.singleFunctor
        (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) (0 : ℤ)).mapIso
          (scalarMateCoefficientPullback φ f))

/-- Restriction of the specified scalar mate is precisely the counit-defined projection.
Source: Stacks 0B56, equation-projection-formula-map
(blueprint: lem-fix-proetale-scalar-mate-normalization).
Proof: (1) scalarMateDerivedTensorIso gives the natural h identifications from step 1,
normalized on balanced tensors. (2) Apply the ring-sheaf change adjunction to the
constant coefficient square, which commutes by naturality of constant sections.
Its canonical d compares the direct images without asserting that restriction
preserves K-injectives. (3) Resolve N and B by flat-term K-flat complexes. Both
pullback/tensor routes send x tensor b to the same pullbacks, by the ordinary
pure-tensor normalizations. They preserve bidegrees and signed total differentials.
The resolution-of-B maps are quasi-isomorphisms after tensoring with the K-flat
first factors, so cancel them after localization. Resolving-class descent gives
the square for every N, including nonflat B. (4) Take N=Ru_* M and transpose the
restricted scalar mate using the ring-sheaf change adjunction. The square of step 3
and naturality of h identify its transpose with the pullback tensor comparison
followed by epsilon_M tensor identity and the coefficient identification v.
This is exactly the specified projection arrow, so adjunction injectivity gives
the first equality. (5) The mate-counit formula gives the second equality before
restriction. All constructions are natural in M; complexes and resolutions are
unbounded and neither flatness nor boundedness was used. -/
theorem proEtaleScalarMateNormalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {T V : Scheme.{u}} (f : T ⟶ V)
    (aV : Scheme.ProEtaleTensorModel V (Scheme.proEtaleConstantRing V A))
    (aT : Scheme.ProEtaleTensorModel T (Scheme.proEtaleConstantRing T A))
    (M : Scheme.proEtaleDerivedCategory T A) :
    ((scalarMateDerivedTensorIso φ V aV).inv.app ((directImageConstantPush A f).obj M) ≫
      (scalarMateRestriction φ V).mapDerivedCategory.map
        ((directImageScalarComparison φ f).app M) ≫
      (scalarMateRestrictionPush φ f).hom.app ((directImageScalarExtension φ T).obj M) ≫
      (directImageConstantPush A f).map ((scalarMateDerivedTensorIso φ T aT).hom.app M) =
    CategoryTheory.derivedProjectionFormulaMate
      (Scheme.proEtaleConstantRingDerivedPullback A f) (directImageConstantPush A f)
      (directImageConstantAdjunction A f) aV.tensor aT.tensor
      (Scheme.proEtaleCanonicalTensorComparison f
        (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
        (Scheme.proEtaleConstantRingComparison f A) aV aT)
      M (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ V)) ≫
      (directImageConstantPush A f).map
        (aT.tensor.map (Prod.mkHom (𝟙 M) (scalarMateDerivedCoefficientPullback φ f).hom))) ∧
    ((Scheme.proEtaleConstantRingDerivedPullback B f).map
      ((directImageScalarComparison φ f).app M) ≫
        (directImageConstantAdjunction B f).counit.app
          ((directImageScalarExtension φ T).obj M) =
      (directImageScalarPullbackIso φ f).hom.app ((directImageConstantPush A f).obj M) ≫
        (directImageScalarExtension φ T).map
          ((directImageConstantAdjunction A f).counit.app M)) := by
  sorry

end AlgebraicGeometry.ProEtale
