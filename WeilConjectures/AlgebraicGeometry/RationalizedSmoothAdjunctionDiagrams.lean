/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralSmoothAdjunctionPresentation
public import WeilConjectures.AlgebraicGeometry.IntegralAdjunctionBijection
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleLinear
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition
public import WeilConjectures.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower
public import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingUniverses
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.RationalLocalizedHom
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.CategoryTheory.SemilinearScalarLocalization
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.LinearRightAdjoint
import Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Raw rationalization of the smooth adjunction diagrams

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension, sole proof
paragraph, final sentence; sk-prop-sp-rational/sk-prop-sp-rational-adjunction.proof.md,
part (1) (blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).

The integral presentation retains the tower adjunction and its realized purity map.
Raw localization and the condensed realization remain different categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option Elab.async false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] CategoryTheory.ScalarLocalization.extensionHom
  CategoryTheory.ScalarLocalization.composition

universe u r v w x y
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open WeilConjectures AlgebraicGeometry.ProEtale

attribute [instance] WeilConjectures.sfIntegralConstructibleLinear
  WeilConjectures.sfIntegralCoefficientLinear

private def adjunctLinearEquiv {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Linear R]
    (a : F ⊣ G) (M : C) (K : D) : (F.obj M ⟶ K) ≃ₗ[R] (M ⟶ G.obj K) :=
  { a.homAddEquiv M K with
    map_smul' := fun b f ↦ by
      change a.homEquiv M K (b • f) = b • a.homEquiv M K f
      rw [a.homEquiv_unit, a.homEquiv_unit, G.map_smul, Linear.comp_smul] }

private theorem liftedNaturality {A C : Type*} [Category* A] [Category* C]
    (P : ObjectProperty C) (F G : A ⥤ C) (hF : ∀ K, P (F.obj K))
    (hG : ∀ K, P (G.obj K)) (t : F ⟶ G)
    (g : ∀ K, (P.lift F hF).obj K ⟶ (P.lift G hG).obj K)
    (hg : ∀ K, (g K).hom = t.app K) :
    ∀ (K L : A) (f : K ⟶ L),
      (P.lift F hF).map f ≫ g L = g K ≫ (P.lift G hG).map f := by
  intro K L f
  apply ObjectProperty.hom_ext
  change F.map f ≫ (g L).hom = (g K).hom ≫ G.map f
  rw [hg, hg]
  exact t.naturality f

private theorem normalizedHomChain {C D : Type*} [Category* C] [Category* D]
    {U U' K : D} {M V V' : C} {A B : Type*}
    (i : U ≅ U') (j : V ≅ V') (ry : A ≃ (U ⟶ K))
    (phi : A ≃ B) (rx : B ≃ (M ⟶ V)) (psi : A → B)
    (hp : ∀ a, phi a = psi a) (a : A) :
    ((Iso.homCongr i.symm (Iso.refl K)).trans
      (ry.symm.trans (phi.trans (rx.trans (Iso.homCongr (Iso.refl M) j)))))
        (i.inv ≫ ry a) = rx (psi a) ≫ j.hom := by
  simp [hp, ← Category.assoc]

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have hc (K) : HEq (c K).hom
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
    simp [c]
  have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
      F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
    obtain ⟨K⟩ := K
    obtain ⟨K'⟩ := K'
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg =>
      rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      rw [(conj_eqToHom_iff_heq _ _ (hF ⟨K⟩) (hF ⟨K'⟩)).mpr (mF K K' f a),
        (conj_eqToHom_iff_heq _ _ (hG ⟨K⟩) (hG ⟨K'⟩)).mpr (mG K K' f a)]
      dsimp [c]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have he : ScalarLocalization.composition S D v _ _ _
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
          ScalarLocalization.composition S D v _ _ _
            (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
        rw [e.hom.naturality f]
      have he' :
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
            (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
      simpa only [ScalarLocalization.localization, Category.assoc] using
        congrArg (fun z :
          (⟨F₀.obj K⟩ : ScalarLocalization S D v) ⟶ ⟨G₀.obj K'⟩ ↦
            eqToHom (hF ⟨K⟩) ≫ z ≫ eqToHom (hG ⟨K'⟩).symm) he'
  let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
  refine ⟨a, hc, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((ha' K).trans (hc K).symm)

private theorem app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X X' : C} (h : X = X') :
    HEq (α.app X) (α.app X') := by
  cases h
  rfl

private theorem comp_heq {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hX
  cases hY
  cases hZ
  cases hf
  cases hg
  rfl


namespace WeilConjectures.RationalizedSmoothAdjunction

section SingleCoefficient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)

variable (s : Presentation l E j p d)

/-- The realized purity components form the specified natural isomorphism.
Source: integral adjunction Purity
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: the reconstruction unit, source comparison and entire-tower gamma are natural.
Composition and the total-limit functor preserve their naturality equations.
The purity_realization clause gives invertibility of each displayed component;
full-subcategory inclusion reflects isomorphisms. -/
theorem gamma_laws :
    (∀ (K L : sfIntegralConstructibleCategory l E Y) (f : K ⟶ L),
      (H l E j p d s).map f ≫ gammaComponent l E j p d s L =
        gammaComponent l E j p d s K ≫ (J l E j p d s).map f) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y,
      IsIso (gammaComponent l E j p d s K)) := by
  let := s.realization.noetherianX
  let := s.realization.noetherianY
  let := s.normalizationX.forgetAdditive
  let := s.normalizationX.forgetLimits
  let := s.normalizationX.forgetColimits
  let src := SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))
  let red := ProEtale.SpIntegralAdjunction.reduce l E Y (s.coordinates.abelian Y)
    s.reductionY s.realization.reductionY
  let inc := ProEtale.SpTowerCalculus.inclusion l E s.base s.coordinates X
  let e := ProEtale.SpTowerCalculus.realization l E s.base X (s.coordinates.abelian X)
  let lim := ProEtale.SpIntegralAdjunction.limit l E X (s.coordinates.abelian X)
    s.reductionX s.normalizationX
  let g : ProEtale.SpTowerGamma.source l E s.base s.operations s.coordinates
      (j ≫ p) s.twists d ⟶
      ProEtale.SpTowerGamma.exceptional l E s.base s.coordinates s.right :=
    { app := fun K ↦ ProEtale.SpTowerGamma.gamma l E s.base s.operations s.coordinates
        (ProEtale.SpTowerGamma.factorization j p) s.twists d
        s.realization.purity.tensorX s.realization.purity.tensorY
        s.supportClosed s.right s.adjunction s.realization.purity.unit_mem
        s.realization.purity.orientation K
        (s.realization.purity.tensor_mem K) (s.realization.purity.projection_iso K)
      naturality := fun K L f ↦ s.realization.purity.naturality K L f }
  let beta := s.realization.sourceComparison.hom ≫ Functor.whiskerLeft red g
  let core : src ⋙ spCompletedReduction l E X (s.coordinates.abelian X) s.reductionX ⟶
      red ⋙ s.right ⋙ inc :=
    Functor.whiskerLeft
        (src ⋙ spCompletedReduction l E X (s.coordinates.abelian X) s.reductionX)
        e.unitIso.hom ≫ Functor.whiskerRight beta e.inverse ≫
      Functor.whiskerLeft (red ⋙ s.right ⋙ inc) e.unitIso.inv
  let total : src ⟶ red ⋙ s.right ⋙ inc ⋙ lim :=
    Functor.whiskerLeft src s.normalizationX.adjunction.unit ≫ Functor.whiskerRight core lim
  have comp (K : sfIntegralConstructibleCategory l E Y) :
      (gammaComponent l E j p d s K).hom = total.app K := by
    unfold gammaComponent
    rfl
  constructor
  · exact liftedNaturality (sfIntegralConstructible l E X) src
      (red ⋙ s.right ⋙ inc ⋙ lim) s.realization.source_complete
      s.realization.closed total (gammaComponent l E j p d s) comp
  · intro K
    apply (ObjectProperty.isIso_hom_iff (gammaComponent l E j p d s K)).mp
    unfold gammaComponent
    exact s.realization.purity_realization s.realization.sourceComparison K

/-- The canonical natural purity transformation, with the preceding actual components.
Source: integral adjunction Purity
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
@[irreducible]
def gammaTransformation : H l E j p d s ⟶ J l E j p d s where
  app := gammaComponent l E j p d s
  naturality K L f := (gamma_laws l E j p d s).1 K L f

/-- Componentwise invertibility of the fixed purity transformation.
Source: integral adjunction Purity
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: gamma_laws gives invertibility at every object; naturality assembles the inverses
into the inverse natural transformation. -/
theorem gammaTransformation_isIso : IsIso (gammaTransformation l E j p d s) := by
  let (K : sfIntegralConstructibleCategory l E Y) :
      IsIso ((gammaTransformation l E j p d s).app K) := by
    simpa only [gammaTransformation] using (gamma_laws l E j p d s).2 K
  exact NatIso.isIso_of_isIso_app _

/-- The specified purity isomorphism, with no choice of an unrelated right-adjoint map.
Source: integral adjunction Purity
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
@[irreducible]
def gamma : H l E j p d s ≅ J l E j p d s :=
  @asIso _ _ _ _ (gammaTransformation l E j p d s)
    (gammaTransformation_isIso l E j p d s)

/-- The transported integral smooth adjunction.
Source: field-extension proof and rational-adjunction proof (1)
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
@[irreducible]
def adjunction : P l E j p d s ⊣ H l E j p d s :=
  s.realization.adjunction.ofNatIsoRight (gamma l E j p d s).symm

/-- Integral linearity and the two specified transported unit/counit formulas.
Source: field-extension proof, derived limit and invert ell
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: give strict towers their componentwise constant-section scalar action.
Ordinary inverse limit is linear by testing against all limit projections.
The K-injective total-derived-linearity theorem makes its total derived functor linear.
Compose with the strict linear compact-support reduction tower and conjugate through
its normalized reconstruction comparison. The linear-right-adjoint theorem gives
linearity of J; conjugation by gamma gives linearity of H. The forward adjunct is
eta followed by J of the arrow, and its inverse is P of the arrow followed by epsilon.
Bilinearity of composition gives both additive and scalar equations. Transport the
adjunction through gamma; evaluating at identities gives the displayed formulas. -/
theorem integral_linear :
    (P l E j p d s).Additive ∧
    (P l E j p d s).Linear (Padic.coefficientExtensionIntegers l E) ∧
    (H l E j p d s).Additive ∧
    (H l E j p d s).Linear (Padic.coefficientExtensionIntegers l E) ∧
    (∀ M : sfIntegralConstructibleCategory l E X,
      (adjunction l E j p d s).unit.app M =
        s.realization.adjunction.unit.app M ≫ (gamma l E j p d s).inv.app _) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y,
      (adjunction l E j p d s).counit.app K =
        (P l E j p d s).map ((gamma l E j p d s).hom.app K) ≫
          s.realization.adjunction.counit.app K) := by
  sorry

/-- The constant-section additive structure on the compact-support functor.
Source: field-extension proof (blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
instance pAdditive : (P l E j p d s).Additive := (integral_linear l E j p d s).1

/-- The constant-section linear structure on the compact-support functor.
Source: field-extension proof (blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
instance pLinear : (P l E j p d s).Linear (Padic.coefficientExtensionIntegers l E) :=
  (integral_linear l E j p d s).2.1

/-- The additive structure on twisted pullback transported through its purity isomorphism.
Source: field-extension proof (blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
instance hAdditive : (H l E j p d s).Additive := (integral_linear l E j p d s).2.2.1

/-- The linear structure on twisted pullback transported through its purity isomorphism.
Source: field-extension proof (blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
instance hLinear : (H l E j p d s).Linear (Padic.coefficientExtensionIntegers l E) :=
  (integral_linear l E j p d s).2.2.2.1

/-- The integral smooth Hom equivalence is a linear equivalence in both directions.
Source: field-extension proof, linearity paragraph
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: use the unit and counit formulas for the two adjuncts. The functors are linear
by integral_linear, and composition is bilinear. The inverse of a bijective linear map
is linear, with no further hypotheses on the Hom modules. -/
theorem hom_linear (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E Y) :
    ∃ e : ((P l E j p d s).obj M ⟶ K) ≃ₗ[Padic.coefficientExtensionIntegers l E]
        (M ⟶ (H l E j p d s).obj K),
      e.toEquiv = (adjunction l E j p d s).homEquiv M K := by
  exact ⟨adjunctLinearEquiv (adjunction l E j p d s) M K, rfl⟩

/-- The original tower right adjoint and its two Hom directions have the same
constant-section linearity before transport by gamma.
Source: integral-adjunction-bijection and the linearity paragraph
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: P is linear by integral_linear. Apply the linear-right-adjoint theorem to
the supplied integral adjunction. Its inverse adjunct sends h to P(h) followed by
epsilonJ, so bilinear composition proves linearity. Bijectivity makes its inverse
linear as well, and the two underlying maps are the specified adjunction maps. -/
theorem tower_hom_linear :
    (J l E j p d s).Additive ∧
    (J l E j p d s).Linear (Padic.coefficientExtensionIntegers l E) ∧
    ∀ (M : sfIntegralConstructibleCategory l E X)
      (K : sfIntegralConstructibleCategory l E Y),
      ∃ e : ((P l E j p d s).obj M ⟶ K) ≃ₗ[Padic.coefficientExtensionIntegers l E]
        (M ⟶ (J l E j p d s).obj K),
        e.toEquiv = s.realization.adjunction.homEquiv M K := by
  let : Linear (Padic.coefficientExtensionIntegers l E)
      (sfIntegralConstructibleCategory l E X) := sfIntegralConstructibleLinear l E X
  let : Linear (Padic.coefficientExtensionIntegers l E)
      (sfIntegralConstructibleCategory l E Y) := sfIntegralConstructibleLinear l E Y
  let : (P l E j p d s).Additive := pAdditive l E j p d s
  let : (P l E j p d s).Linear (Padic.coefficientExtensionIntegers l E) :=
    pLinear l E j p d s
  obtain ⟨ha, hl⟩ :=
    s.realization.adjunction.right_adjoint_additive_linear
      (A := Padic.coefficientExtensionIntegers l E)
  let := ha
  let := hl
  exact ⟨ha, hl, fun M K ↦ ⟨adjunctLinearEquiv s.realization.adjunction M K, rfl⟩⟩


/-- The existing semilinear extension specialized to a linear functor between two
categories over the same integral coefficient ring. No new localization is defined.
Source: raw localization Hom formula
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def localized {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization R C t ⥤ ScalarLocalization R D t :=
  ScalarLocalization.extension t t (RingHom.id R)
    (IsLocalization.Away.algebraMap_isUnit t (S := Localization.Away t)) F
    (fun _ _ a f ↦ F.map_smul a f)

private theorem localized_tmul {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    {M N : ScalarLocalization R C t} (a : Localization.Away t) (f : M.obj ⟶ N.obj) :
    (localized t F).map (a ⊗ₜ[R] f : M ⟶ N) = a ⊗ₜ[R] F.map f := by
  let hF : ScalarLocalization.IsSemilinear (RingHom.id R) F :=
    fun _ _ b g ↦ F.map_smul b g
  have hc : ScalarLocalization.coefficientMap t t (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit t) = RingHom.id (Localization.Away t) :=
    ((ScalarLocalization.coefficientMap_unique t t (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit t) (RingHom.id _)).mp rfl).symm
  change ScalarLocalization.extensionHom t t (RingHom.id R)
    (IsLocalization.Away.algebraMap_isUnit t) F hF M.obj N.obj (a ⊗ₜ[R] f) = _
  rw [ScalarLocalization.extensionHom]
  rw [Classical.choose_spec
    (ScalarLocalization.existsUnique_semilinearHom t t (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit t) F hF M.obj N.obj).exists a f, hc]
  rfl

private instance localized_additive {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R] : (localized t F).Additive := by
  unfold localized
  infer_instance

private def localizedHom {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R] (M N : C) :
    (Localization.Away t ⊗[R] (M ⟶ N)) →+
      (Localization.Away t ⊗[R] (F.obj M ⟶ F.obj N)) :=
  ScalarLocalization.extensionHom t t (RingHom.id R)
    (IsLocalization.Away.algebraMap_isUnit t) F (fun _ _ a f ↦ F.map_smul a f) M N

private theorem localizedHom_tmul {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (M N : C) (a : Localization.Away t) (f : M ⟶ N) :
    localizedHom t F M N (a ⊗ₜ[R] f) = a ⊗ₜ[R] F.map f :=
  localized_tmul t F (M := ⟨M⟩) (N := ⟨N⟩) a f

private theorem localizedHom_smul {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R] (M N : C)
    (f : Localization.Away t ⊗[R] (M ⟶ N)) (a : Localization.Away t) :
    localizedHom t F M N (a • f) = a • localizedHom t F M N f := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul b f => simp only [TensorProduct.smul_tmul', localizedHom_tmul]
  | add f g hf hg => simp only [smul_add, map_add, hf, hg]

private instance localized_linear {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (localized t F).Linear (Localization.Away t) where
  map_smul {M N} f a := localizedHom_smul t F M.obj N.obj f a

@[irreducible]
private def localizedAdjunction {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G) :
    localized t F ⊣ localized t G where
  unit :=
    { app M := 1 ⊗ₜ[R] a.unit.app M.obj
      naturality {M N} f := by
        change ScalarLocalization.composition R C t _ _ _ (1 ⊗ₜ[R] a.unit.app N.obj) f =
          ScalarLocalization.composition R C t _ _ _
            (localizedHom t G _ _ (localizedHom t F _ _ f)) (1 ⊗ₜ[R] a.unit.app M.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | tmul b f =>
          rw [localizedHom_tmul, localizedHom_tmul, ScalarLocalization.composition_tmul,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ b ⊗ₜ[R] k) (a.unit.naturality f)
        | add f g hf hg =>
          simp only [map_add, LinearMap.add_apply, hf, hg] }
  counit :=
    { app K := 1 ⊗ₜ[R] a.counit.app K.obj
      naturality {K L} f := by
        change ScalarLocalization.composition R D t _ _ _ (1 ⊗ₜ[R] a.counit.app L.obj)
            (localizedHom t F _ _ (localizedHom t G _ _ f)) =
          ScalarLocalization.composition R D t _ _ _ f (1 ⊗ₜ[R] a.counit.app K.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | tmul b f =>
          rw [localizedHom_tmul, localizedHom_tmul, ScalarLocalization.composition_tmul,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ b ⊗ₜ[R] k) (a.counit.naturality f)
        | add f g hf hg =>
          simp only [map_add, LinearMap.add_apply, hf, hg] }
  left_triangle_components M := by
    change ScalarLocalization.composition R D t _ _ _
      (1 ⊗ₜ[R] a.counit.app (F.obj M.obj))
      ((localized t F).map (1 ⊗ₜ[R] a.unit.app M.obj)) = _
    rw [localized_tmul, ScalarLocalization.composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away t) ⊗ₜ[R] k)
      (a.left_triangle_components M.obj)
  right_triangle_components K := by
    change ScalarLocalization.composition R C t _ _ _
      ((localized t G).map (1 ⊗ₜ[R] a.counit.app K.obj))
      (1 ⊗ₜ[R] a.unit.app (G.obj K.obj)) = _
    rw [localized_tmul, ScalarLocalization.composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away t) ⊗ₜ[R] k)
      (a.right_triangle_components K.obj)

private theorem localizedAdjunction_unit {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G)
    (M : ScalarLocalization R C t) :
    (localizedAdjunction t F G a).unit.app M = 1 ⊗ₜ[R] a.unit.app M.obj := by
  unfold localizedAdjunction
  rfl

private theorem localizedAdjunction_counit {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G)
    (K : ScalarLocalization R D t) :
    (localizedAdjunction t F G a).counit.app K = 1 ⊗ₜ[R] a.counit.app K.obj := by
  unfold localizedAdjunction
  rfl

private theorem localizedAdjunction_hom_tmul {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G)
    (M : C) (K : D) (f : F.obj M ⟶ K) (b : Localization.Away t) :
    (localizedAdjunction t F G a).homEquiv ⟨M⟩ ⟨K⟩ (b ⊗ₜ[R] f) =
      b ⊗ₜ[R] a.homEquiv M K f := by
  change ScalarLocalization.composition R C t _ _ _
    ((localized t G).map (b ⊗ₜ[R] f))
    ((localizedAdjunction t F G a).unit.app ⟨M⟩) = _
  rw [localizedAdjunction_unit, localized_tmul,
    ScalarLocalization.composition_tmul, mul_one]
  rfl

private theorem localizedAdjunction_inv_tmul {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G)
    (M : C) (K : D) (f : M ⟶ G.obj K) (b : Localization.Away t) :
    ((localizedAdjunction t F G a).homEquiv ⟨M⟩ ⟨K⟩).symm (b ⊗ₜ[R] f) =
      b ⊗ₜ[R] (a.homEquiv M K).symm f := by
  change ScalarLocalization.composition R D t _ _ _
    ((localizedAdjunction t F G a).counit.app ⟨K⟩)
    ((localized t F).map (b ⊗ₜ[R] f)) = _
  rw [localizedAdjunction_counit, localized_tmul,
    ScalarLocalization.composition_tmul, one_mul]
  rfl

private theorem localizedAdjunction_hom_smul {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G)
    (M : ScalarLocalization R C t) (K : ScalarLocalization R D t)
    (b : Localization.Away t) (f : (localized t F).obj M ⟶ K) :
    (localizedAdjunction t F G a).homEquiv M K (b • f) =
      b • (localizedAdjunction t F G a).homEquiv M K f := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_smul, Linear.comp_smul]

/-- Rational compact support is the raw localization of the actual integral functor.
Source: compact-support and rationalization definitions
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev rationalP := localized (Padic.coefficientExtensionUniformizer l E) (P l E j p d s)

/-- Rational twisted pullback is the raw localization of the specified completed
pullback, Tate tensor and shift. Source: rationalization and derived operations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev rationalH := localized (Padic.coefficientExtensionUniformizer l E) (H l E j p d s)

/-- The data of a localized linear adjunction, over arbitrary linear categories.
Specializing this record retains all the tensor, additive, scalar and integral
unit/counit formulas without generating an inductive family over scheme data.
Source: rationalized smooth adjunction diagrams, raw localization step
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
structure LocalizedAdjunctionData {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G) where
  adjunction : localized t F ⊣ localized t G
  hom_tmul : ∀ (M : C) (K : D) (f : F.obj M ⟶ K) (b : Localization.Away t),
    adjunction.homEquiv ⟨M⟩ ⟨K⟩ (b ⊗ₜ[R] f) = b ⊗ₜ[R] a.homEquiv M K f
  inv_tmul : ∀ (M : C) (K : D) (f : M ⟶ G.obj K) (b : Localization.Away t),
    (adjunction.homEquiv ⟨M⟩ ⟨K⟩).symm (b ⊗ₜ[R] f) =
      b ⊗ₜ[R] (a.homEquiv M K).symm f
  hom_add : ∀ (M : ScalarLocalization R C t) (K : ScalarLocalization R D t)
    (f g : (localized t F).obj M ⟶ K),
    adjunction.homEquiv M K (f + g) = adjunction.homEquiv M K f + adjunction.homEquiv M K g
  hom_smul : ∀ (M : ScalarLocalization R C t) (K : ScalarLocalization R D t)
    (b : Localization.Away t) (f : (localized t F).obj M ⟶ K),
    adjunction.homEquiv M K (b • f) = b • adjunction.homEquiv M K f
  unit : ∀ M : C, adjunction.unit.app ⟨M⟩ = 1 ⊗ₜ[R] a.unit.app M
  counit : ∀ K : D, adjunction.counit.app ⟨K⟩ = 1 ⊗ₜ[R] a.counit.app K

private theorem generic_raw_exists {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G) :
    Nonempty (LocalizedAdjunctionData t F G a) := by
  let b := localizedAdjunction t F G a
  exact ⟨{
    adjunction := b
    hom_tmul := localizedAdjunction_hom_tmul t F G a
    inv_tmul := localizedAdjunction_inv_tmul t F G a
    hom_add := fun M K f g ↦ b.homAddEquiv_add M K f g
    hom_smul := localizedAdjunction_hom_smul t F G a
    unit := fun M ↦ localizedAdjunction_unit t F G a ⟨M⟩
    counit := fun K ↦ localizedAdjunction_counit t F G a ⟨K⟩ }⟩

/-- The raw smooth adjunction, its tensor formula and its specified unit and counit.
An Adjunction supplies naturality for all rational arrows and both triangle identities.
Source: field-extension proof, invert ell; rational-adjunction proof (1)
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev Raw := LocalizedAdjunctionData (Padic.coefficientExtensionUniformizer l E)
  (P l E j p d s) (H l E j p d s) (adjunction l E j p d s)

/-- Tensoring the integral Hom equivalence gives the specified raw smooth adjunction.
Source: field-extension proof, final sentence; rational-adjunction proof (1)
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: tensor the linear equivalence hom_linear and its inverse with the fraction ring.
The composites are identities on pure tensors, hence on all tensors. For integral s,t,u
and scalars a,b,c, the naturality equation on (b tensor t)(c tensor u)P(a tensor s)
is integral naturality tensored with bca. Extend by additivity in all three arguments.
Evaluate at identities tensored with one for unit and counit. Their triangles are images
of the integral triangles, so the natural Hom equivalence defines the claimed adjunction.
No objects or idempotents are adjoined. -/
theorem raw_exists : Nonempty (Raw l E j p d s) := by
  let : (P l E j p d s).Additive := pAdditive l E j p d s
  let : (P l E j p d s).Linear (Padic.coefficientExtensionIntegers l E) :=
    pLinear l E j p d s
  let : (H l E j p d s).Additive := hAdditive l E j p d s
  let : (H l E j p d s).Linear (Padic.coefficientExtensionIntegers l E) :=
    hLinear l E j p d s
  exact generic_raw_exists (Padic.coefficientExtensionUniformizer l E)
    (P l E j p d s) (H l E j p d s) (adjunction l E j p d s)

private theorem localized_obj {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R] (M : ScalarLocalization R C t) :
    (localized t F).obj M = ⟨F.obj M.obj⟩ := rfl

private theorem localized_map {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R] {M N : C} (f : M ⟶ N) :
    (localized t F).map ((ScalarLocalization.localization R C t).map f) =
      (ScalarLocalization.localization R D t).map (F.map f) :=
  localized_tmul t F 1 f

private theorem comp3_heq {C : Type*} [Category* C]
    {W W' X X' Y Y' Z Z' : C}
    (hW : W = W') (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : W ⟶ X} {f' : W' ⟶ X'} {g : X ⟶ Y} {g' : X' ⟶ Y'}
    {h : Y ⟶ Z} {h' : Y' ⟶ Z'} (hf : HEq f f') (hg : HEq g g') (hh : HEq h h') :
    HEq (f ≫ g ≫ h) (f' ≫ g' ≫ h') :=
  comp_heq hW hX hZ hf (comp_heq hX hY hZ hg hh)

private theorem iso_inv_heq {C : Type*} [Category* C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    (e : X ≅ Y) (e' : X' ≅ Y') (hh : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hX
  cases hY
  have he : e = e' := Iso.ext (eq_of_heq hh)
  cases he
  rfl

private theorem localized_square
    {R S : Type*} [CommRing R] [CommRing S]
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']
    [Linear R C] [Linear R D] [Linear S C'] [Linear S D']
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ : C ⥤ D) [F₀.Additive] [F₀.Linear R]
    (F₁ : C' ⥤ D') [F₁.Additive] [F₁.Linear S]
    (CX₀ : C ⥤ C') (CY₀ : D ⥤ D')
    (CX : ScalarLocalization R C t ⥤ ScalarLocalization S C' v)
    (CY : ScalarLocalization R D t ⥤ ScalarLocalization S D' v)
    [CX.Additive] [CY.Additive]
    (hX : ∀ K, CX.obj K = ⟨CX₀.obj K.obj⟩)
    (hY : ∀ K, CY.obj K = ⟨CY₀.obj K.obj⟩)
    (mX : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (CX.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] CX₀.map f :
          ScalarLocalization.mk (R := S) (p := v) (CX₀.obj K) ⟶ ⟨CX₀.obj K'⟩))
    (mY : ∀ (K K' : D) (f : K ⟶ K') (a : Localization.Away t),
      HEq (CY.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] CY₀.map f :
          ScalarLocalization.mk (R := S) (p := v) (CY₀.obj K) ⟶ ⟨CY₀.obj K'⟩))
    (e : F₀ ⋙ CY₀ ≅ CX₀ ⋙ F₁) :
    ∃ a : localized t F₀ ⋙ CY ≅ CX ⋙ localized v F₁,
      (∀ K, HEq (a.hom.app K)
        ((ScalarLocalization.localization S D' v).map (e.hom.app K.obj))) ∧
      (∀ K, HEq (a.inv.app K)
        ((ScalarLocalization.localization S D' v).map (e.inv.app K.obj))) := by
  have hleft (K) : (localized t F₀ ⋙ CY).obj K = ⟨(F₀ ⋙ CY₀).obj K.obj⟩ :=
    hY ((localized t F₀).obj K)
  have hright (K) : (CX ⋙ localized v F₁).obj K = ⟨(CX₀ ⋙ F₁).obj K.obj⟩ :=
    congrArg (localized v F₁).obj (hX K)
  obtain ⟨a, ha, _⟩ := localizedIso t v ψ (F₀ ⋙ CY₀) (CX₀ ⋙ F₁) e
    (localized t F₀ ⋙ CY) (CX ⋙ localized v F₁) hleft hright
    (fun K K' f b ↦
      (map_heq CY rfl rfl (heq_of_eq (localized_tmul t F₀ b f))).trans
        (mY _ _ (F₀.map f) b))
    (fun K K' f b ↦
      (map_heq (localized v F₁) (hX ⟨K⟩) (hX ⟨K'⟩) (mX K K' f b)).trans
        (heq_of_eq (localized_tmul v F₁ (ψ b) (CX₀.map f))))
  refine ⟨a, ha, fun K ↦ ?_⟩
  exact iso_inv_heq (hleft K) (hright K) (a.app K)
    ((ScalarLocalization.localization S D' v).mapIso (e.app K.obj)) (ha K)

private theorem raw_unit_map (r : Raw l E j p d s)
    (M : sfIntegralConstructibleCategory l E X) :
    r.adjunction.unit.app ⟨M⟩ = (sfRationalConstructibleLocalization l E X).map
      ((adjunction l E j p d s).unit.app M) := by
  simpa only [sfRationalConstructibleLocalization, ScalarLocalization.localization] using r.unit M

private theorem raw_counit_map (r : Raw l E j p d s)
    (K : sfIntegralConstructibleCategory l E Y) :
    r.adjunction.counit.app ⟨K⟩ = (sfRationalConstructibleLocalization l E Y).map
      ((adjunction l E j p d s).counit.app K) := by
  simpa only [sfRationalConstructibleLocalization, ScalarLocalization.localization] using r.counit K

private theorem raw_unit_heq (r : Raw l E j p d s)
    (M : sfIntegralConstructibleCategory l E X) :
    HEq (r.adjunction.unit.app ⟨M⟩) ((sfRationalConstructibleLocalization l E X).map
      ((adjunction l E j p d s).unit.app M)) :=
  heq_of_eq (raw_unit_map l E j p d s r M)

private theorem raw_counit_heq (r : Raw l E j p d s)
    (K : sfIntegralConstructibleCategory l E Y) :
    HEq (r.adjunction.counit.app ⟨K⟩) ((sfRationalConstructibleLocalization l E Y).map
      ((adjunction l E j p d s).counit.app K)) :=
  heq_of_eq (raw_counit_map l E j p d s r K)

end SingleCoefficient


set_option allowUnsafeReducibility true in
attribute [local irreducible] P H J
attribute [local instance] pAdditive pLinear hAdditive hLinear

/-- Compatibility of two adjunction units with a pair of comparison isomorphisms.
Source: field-extension proof, unit equation
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def UnitComparisonLaw {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F' ⊣ G') (CX : C ⥤ C') (CY : D ⥤ D')
    (b : F ⋙ CY ≅ CX ⋙ F') (c : G ⋙ CX ≅ CY ⋙ G') : Prop :=
  ∀ M : C, CX.map (a.unit.app M) ≫ c.hom.app (F.obj M) ≫ G'.map (b.hom.app M) =
    a'.unit.app (CX.obj M)

/-- Compatibility of two adjunction counits with a pair of comparison isomorphisms.
Source: field-extension proof, counit equation
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def CounitComparisonLaw {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F' ⊣ G') (CX : C ⥤ C') (CY : D ⥤ D')
    (b : F ⋙ CY ≅ CX ⋙ F') (c : G ⋙ CX ≅ CY ⋙ G') : Prop :=
  ∀ K : D, b.hom.app (G.obj K) ≫ F'.map (c.hom.app K) ≫ a'.counit.app (CY.obj K) =
    CY.map (a.counit.app K)

/-- The component equation for coefficient comparisons over a triple of fields.
Source: field-extension proof, composition equation
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def CoefficientCocycleLaw {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (T₀ : C₀ ⥤ D₀) (T₁ : C₁ ⥤ D₁) (T₂ : C₂ ⥤ D₂)
    (CX₀₁ : C₀ ⥤ C₁) (CX₁₂ : C₁ ⥤ C₂) (CX₀₂ : C₀ ⥤ C₂)
    (CY₀₁ : D₀ ⥤ D₁) (CY₁₂ : D₁ ⥤ D₂) (CY₀₂ : D₀ ⥤ D₂)
    (b₀₁ : T₀ ⋙ CY₀₁ ≅ CX₀₁ ⋙ T₁) (b₁₂ : T₁ ⋙ CY₁₂ ≅ CX₁₂ ⋙ T₂)
    (b₀₂ : T₀ ⋙ CY₀₂ ≅ CX₀₂ ⋙ T₂)
    (cX : CX₀₁ ⋙ CX₁₂ ≅ CX₀₂) (cY : CY₀₁ ⋙ CY₁₂ ≅ CY₀₂) : Prop :=
  ∀ M : C₀, CY₁₂.map (b₀₁.hom.app M) ≫ b₁₂.hom.app (CX₀₁.obj M) ≫
      T₂.map (cX.hom.app M) = cY.hom.app (T₀.obj M) ≫ b₀₂.hom.app M

/-- Identity normalization under the specified coefficient unitors.
Source: field-extension proof, identity normalization
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def CoefficientIdentityLaw {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ D) (CX : C ⥤ C) (CY : D ⥤ D) (b : T ⋙ CY ≅ CX ⋙ T)
    (uX : CX ≅ 𝟭 C) (uY : CY ≅ 𝟭 D) : Prop :=
  ∀ M : C, b.hom.app M = uY.hom.app (T.obj M) ≫ T.map (uX.inv.app M)

private structure LiftData {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    (QC : C ⥤ C') (QD : D ⥤ D') (F : C ⥤ D) (F' : C' ⥤ D') : Prop where
  obj_eq : ∀ X, F'.obj (QC.obj X) = QD.obj (F.obj X)
  map_eq : ∀ {X Y} (f : X ⟶ Y), HEq (F'.map (QC.map f)) (QD.map (F.map f))

private theorem LiftData.comp
    {C D E C' D' E' : Type*}
    [Category* C] [Category* D] [Category* E]
    [Category* C'] [Category* D'] [Category* E']
    {QC : C ⥤ C'} {QD : D ⥤ D'} {QE : E ⥤ E'}
    {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ E} {G' : D' ⥤ E'}
    (hF : LiftData QC QD F F') (hG : LiftData QD QE G G') :
    LiftData QC QE (F ⋙ G) (F' ⋙ G') where
  obj_eq X := (congrArg G'.obj (hF.obj_eq X)).trans (hG.obj_eq (F.obj X))
  map_eq f := (map_heq G' (hF.obj_eq _) (hF.obj_eq _) (hF.map_eq f)).trans
    (hG.map_eq (F.map f))

private theorem lifted_unit_law
    {C₀ D₀ C₁ D₁ C₀' D₀' C₁' D₁' : Type*}
    [Category* C₀] [Category* D₀] [Category* C₁] [Category* D₁]
    [Category* C₀'] [Category* D₀'] [Category* C₁'] [Category* D₁']
    (QX₀ : C₀ ⥤ C₀') (QY₀ : D₀ ⥤ D₀')
    (QX₁ : C₁ ⥤ C₁') (QY₁ : D₁ ⥤ D₁')
    (surj : Function.Surjective QX₀.obj)
    {F₀ : C₀ ⥤ D₀} {G₀ : D₀ ⥤ C₀} {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁}
    {F₀' : C₀' ⥤ D₀'} {G₀' : D₀' ⥤ C₀'}
    {F₁' : C₁' ⥤ D₁'} {G₁' : D₁' ⥤ C₁'}
    (a₀ : F₀ ⊣ G₀) (a₁ : F₁ ⊣ G₁) (a₀' : F₀' ⊣ G₀') (a₁' : F₁' ⊣ G₁')
    {CX : C₀ ⥤ C₁} {CY : D₀ ⥤ D₁} {CX' : C₀' ⥤ C₁'} {CY' : D₀' ⥤ D₁'}
    (hF₀ : LiftData QX₀ QY₀ F₀ F₀') (hG₀ : LiftData QY₀ QX₀ G₀ G₀')
    (hF₁ : LiftData QX₁ QY₁ F₁ F₁') (hG₁ : LiftData QY₁ QX₁ G₁ G₁')
    (hX : LiftData QX₀ QX₁ CX CX') (hY : LiftData QY₀ QY₁ CY CY')
    (b : F₀ ⋙ CY ≅ CX ⋙ F₁) (c : G₀ ⋙ CX ≅ CY ⋙ G₁)
    (b' : F₀' ⋙ CY' ≅ CX' ⋙ F₁') (c' : G₀' ⋙ CX' ≅ CY' ⋙ G₁')
    (hb : ∀ M, HEq (b'.hom.app (QX₀.obj M)) (QY₁.map (b.hom.app M)))
    (hc : ∀ K, HEq (c'.hom.app (QY₀.obj K)) (QX₁.map (c.hom.app K)))
    (hu₀ : ∀ M, HEq (a₀'.unit.app (QX₀.obj M)) (QX₀.map (a₀.unit.app M)))
    (hu₁ : ∀ M, HEq (a₁'.unit.app (QX₁.obj M)) (QX₁.map (a₁.unit.app M)))
    (h : UnitComparisonLaw a₀ a₁ CX CY b c) :
    UnitComparisonLaw a₀' a₁' CX' CY' b' c' := by
  intro M
  obtain ⟨M, rfl⟩ := surj M
  have h₁ := (map_heq CX' rfl ((hF₀.comp hG₀).obj_eq M) (hu₀ M)).trans
    (hX.map_eq (a₀.unit.app M))
  have h₂ := (app_heq c'.hom (hF₀.obj_eq M)).trans (hc (F₀.obj M))
  have h₃ := (map_heq G₁' ((hF₀.comp hY).obj_eq M)
    ((hX.comp hF₁).obj_eq M) (hb M)).trans (hG₁.map_eq (b.hom.app M))
  have hleft := comp3_heq (hX.obj_eq M) (((hF₀.comp hG₀).comp hX).obj_eq M)
    (((hF₀.comp hY).comp hG₁).obj_eq M) (((hX.comp hF₁).comp hG₁).obj_eq M)
    h₁ h₂ h₃
  have hright := (app_heq a₁'.unit (hX.obj_eq M)).trans (hu₁ (CX.obj M))
  have hi := congrArg QX₁.map (h M)
  rw [Functor.map_comp, Functor.map_comp] at hi
  exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

private theorem lifted_counit_law
    {C₀ D₀ C₁ D₁ C₀' D₀' C₁' D₁' : Type*}
    [Category* C₀] [Category* D₀] [Category* C₁] [Category* D₁]
    [Category* C₀'] [Category* D₀'] [Category* C₁'] [Category* D₁']
    (QX₀ : C₀ ⥤ C₀') (QY₀ : D₀ ⥤ D₀')
    (QX₁ : C₁ ⥤ C₁') (QY₁ : D₁ ⥤ D₁')
    (surj : Function.Surjective QY₀.obj)
    {F₀ : C₀ ⥤ D₀} {G₀ : D₀ ⥤ C₀} {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁}
    {F₀' : C₀' ⥤ D₀'} {G₀' : D₀' ⥤ C₀'}
    {F₁' : C₁' ⥤ D₁'} {G₁' : D₁' ⥤ C₁'}
    (a₀ : F₀ ⊣ G₀) (a₁ : F₁ ⊣ G₁) (a₀' : F₀' ⊣ G₀') (a₁' : F₁' ⊣ G₁')
    {CX : C₀ ⥤ C₁} {CY : D₀ ⥤ D₁} {CX' : C₀' ⥤ C₁'} {CY' : D₀' ⥤ D₁'}
    (hF₀ : LiftData QX₀ QY₀ F₀ F₀') (hG₀ : LiftData QY₀ QX₀ G₀ G₀')
    (hF₁ : LiftData QX₁ QY₁ F₁ F₁') (hG₁ : LiftData QY₁ QX₁ G₁ G₁')
    (hX : LiftData QX₀ QX₁ CX CX') (hY : LiftData QY₀ QY₁ CY CY')
    (b : F₀ ⋙ CY ≅ CX ⋙ F₁) (c : G₀ ⋙ CX ≅ CY ⋙ G₁)
    (b' : F₀' ⋙ CY' ≅ CX' ⋙ F₁') (c' : G₀' ⋙ CX' ≅ CY' ⋙ G₁')
    (hb : ∀ M, HEq (b'.hom.app (QX₀.obj M)) (QY₁.map (b.hom.app M)))
    (hc : ∀ K, HEq (c'.hom.app (QY₀.obj K)) (QX₁.map (c.hom.app K)))
    (he₀ : ∀ K, HEq (a₀'.counit.app (QY₀.obj K)) (QY₀.map (a₀.counit.app K)))
    (he₁ : ∀ K, HEq (a₁'.counit.app (QY₁.obj K)) (QY₁.map (a₁.counit.app K)))
    (h : CounitComparisonLaw a₀ a₁ CX CY b c) :
    CounitComparisonLaw a₀' a₁' CX' CY' b' c' := by
  intro K
  obtain ⟨K, rfl⟩ := surj K
  have h₁ := (app_heq b'.hom (hG₀.obj_eq K)).trans (hb (G₀.obj K))
  have h₂ := (map_heq F₁' ((hG₀.comp hX).obj_eq K)
    ((hY.comp hG₁).obj_eq K) (hc K)).trans (hF₁.map_eq (c.hom.app K))
  have h₃ := (app_heq a₁'.counit (hY.obj_eq K)).trans (he₁ (CY.obj K))
  have hleft := comp3_heq (((hG₀.comp hF₀).comp hY).obj_eq K)
    (((hG₀.comp hX).comp hF₁).obj_eq K) (((hY.comp hG₁).comp hF₁).obj_eq K)
    (hY.obj_eq K) h₁ h₂ h₃
  have hright := (map_heq CY' ((hG₀.comp hF₀).obj_eq K) rfl (he₀ K)).trans
    (hY.map_eq (a₀.counit.app K))
  have hi := congrArg QY₁.map (h K)
  rw [Functor.map_comp, Functor.map_comp] at hi
  exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

private theorem lifted_cocycle_law
    {C₀ C₁ C₂ D₀ D₁ D₂ C₀' C₁' C₂' D₀' D₁' D₂' : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    [Category* C₀'] [Category* C₁'] [Category* C₂']
    [Category* D₀'] [Category* D₁'] [Category* D₂']
    (QX₀ : C₀ ⥤ C₀') (QX₁ : C₁ ⥤ C₁') (QX₂ : C₂ ⥤ C₂')
    (QY₀ : D₀ ⥤ D₀') (QY₁ : D₁ ⥤ D₁') (QY₂ : D₂ ⥤ D₂')
    (surj : Function.Surjective QX₀.obj)
    {T₀ : C₀ ⥤ D₀} {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂}
    {T₀' : C₀' ⥤ D₀'} {T₁' : C₁' ⥤ D₁'} {T₂' : C₂' ⥤ D₂'}
    {CX₀₁ : C₀ ⥤ C₁} {CX₁₂ : C₁ ⥤ C₂} {CX₀₂ : C₀ ⥤ C₂}
    {CY₀₁ : D₀ ⥤ D₁} {CY₁₂ : D₁ ⥤ D₂} {CY₀₂ : D₀ ⥤ D₂}
    {CX₀₁' : C₀' ⥤ C₁'} {CX₁₂' : C₁' ⥤ C₂'} {CX₀₂' : C₀' ⥤ C₂'}
    {CY₀₁' : D₀' ⥤ D₁'} {CY₁₂' : D₁' ⥤ D₂'} {CY₀₂' : D₀' ⥤ D₂'}
    (hT₀ : LiftData QX₀ QY₀ T₀ T₀') (hT₁ : LiftData QX₁ QY₁ T₁ T₁')
    (hT₂ : LiftData QX₂ QY₂ T₂ T₂')
    (hX₀₁ : LiftData QX₀ QX₁ CX₀₁ CX₀₁') (hX₁₂ : LiftData QX₁ QX₂ CX₁₂ CX₁₂')
    (hX₀₂ : LiftData QX₀ QX₂ CX₀₂ CX₀₂')
    (hY₀₁ : LiftData QY₀ QY₁ CY₀₁ CY₀₁') (hY₁₂ : LiftData QY₁ QY₂ CY₁₂ CY₁₂')
    (hY₀₂ : LiftData QY₀ QY₂ CY₀₂ CY₀₂')
    (b₀₁ : T₀ ⋙ CY₀₁ ≅ CX₀₁ ⋙ T₁) (b₁₂ : T₁ ⋙ CY₁₂ ≅ CX₁₂ ⋙ T₂)
    (b₀₂ : T₀ ⋙ CY₀₂ ≅ CX₀₂ ⋙ T₂)
    (cX : CX₀₁ ⋙ CX₁₂ ≅ CX₀₂) (cY : CY₀₁ ⋙ CY₁₂ ≅ CY₀₂)
    (b₀₁' : T₀' ⋙ CY₀₁' ≅ CX₀₁' ⋙ T₁') (b₁₂' : T₁' ⋙ CY₁₂' ≅ CX₁₂' ⋙ T₂')
    (b₀₂' : T₀' ⋙ CY₀₂' ≅ CX₀₂' ⋙ T₂')
    (cX' : CX₀₁' ⋙ CX₁₂' ≅ CX₀₂') (cY' : CY₀₁' ⋙ CY₁₂' ≅ CY₀₂')
    (hb₀₁ : ∀ M, HEq (b₀₁'.hom.app (QX₀.obj M)) (QY₁.map (b₀₁.hom.app M)))
    (hb₁₂ : ∀ M, HEq (b₁₂'.hom.app (QX₁.obj M)) (QY₂.map (b₁₂.hom.app M)))
    (hb₀₂ : ∀ M, HEq (b₀₂'.hom.app (QX₀.obj M)) (QY₂.map (b₀₂.hom.app M)))
    (hcX : ∀ M, HEq (cX'.hom.app (QX₀.obj M)) (QX₂.map (cX.hom.app M)))
    (hcY : ∀ K, HEq (cY'.hom.app (QY₀.obj K)) (QY₂.map (cY.hom.app K)))
    (h : CoefficientCocycleLaw T₀ T₁ T₂ CX₀₁ CX₁₂ CX₀₂ CY₀₁ CY₁₂ CY₀₂
      b₀₁ b₁₂ b₀₂ cX cY) :
    CoefficientCocycleLaw T₀' T₁' T₂' CX₀₁' CX₁₂' CX₀₂' CY₀₁' CY₁₂' CY₀₂'
      b₀₁' b₁₂' b₀₂' cX' cY' := by
  intro M
  obtain ⟨M, rfl⟩ := surj M
  have h₁ := (map_heq CY₁₂' ((hT₀.comp hY₀₁).obj_eq M)
    ((hX₀₁.comp hT₁).obj_eq M) (hb₀₁ M)).trans (hY₁₂.map_eq (b₀₁.hom.app M))
  have h₂ := (app_heq b₁₂'.hom (hX₀₁.obj_eq M)).trans (hb₁₂ (CX₀₁.obj M))
  have h₃ := (map_heq T₂' ((hX₀₁.comp hX₁₂).obj_eq M)
    (hX₀₂.obj_eq M) (hcX M)).trans (hT₂.map_eq (cX.hom.app M))
  have hleft := comp3_heq (((hT₀.comp hY₀₁).comp hY₁₂).obj_eq M)
    (((hX₀₁.comp hT₁).comp hY₁₂).obj_eq M)
    (((hX₀₁.comp hX₁₂).comp hT₂).obj_eq M) ((hX₀₂.comp hT₂).obj_eq M) h₁ h₂ h₃
  have h₄ := (app_heq cY'.hom (hT₀.obj_eq M)).trans (hcY (T₀.obj M))
  have hright := comp_heq (((hT₀.comp hY₀₁).comp hY₁₂).obj_eq M)
    ((hT₀.comp hY₀₂).obj_eq M) ((hX₀₂.comp hT₂).obj_eq M) h₄ (hb₀₂ M)
  have hi := congrArg QY₂.map (h M)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp] at hi
  exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

private theorem lifted_identity_law
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (QX : C ⥤ C') (QY : D ⥤ D') (surj : Function.Surjective QX.obj)
    {T : C ⥤ D} {T' : C' ⥤ D'} {CX : C ⥤ C} {CY : D ⥤ D}
    {CX' : C' ⥤ C'} {CY' : D' ⥤ D'}
    (hT : LiftData QX QY T T') (hX : LiftData QX QX CX CX') (hY : LiftData QY QY CY CY')
    (b : T ⋙ CY ≅ CX ⋙ T) (uX : CX ≅ 𝟭 C) (uY : CY ≅ 𝟭 D)
    (b' : T' ⋙ CY' ≅ CX' ⋙ T') (uX' : CX' ≅ 𝟭 C') (uY' : CY' ≅ 𝟭 D')
    (hb : ∀ M, HEq (b'.hom.app (QX.obj M)) (QY.map (b.hom.app M)))
    (huX : ∀ M, HEq (uX'.hom.app (QX.obj M)) (QX.map (uX.hom.app M)))
    (huY : ∀ K, HEq (uY'.hom.app (QY.obj K)) (QY.map (uY.hom.app K)))
    (h : CoefficientIdentityLaw T CX CY b uX uY) :
    CoefficientIdentityLaw T' CX' CY' b' uX' uY' := by
  intro M
  obtain ⟨M, rfl⟩ := surj M
  have h₁ := (app_heq uY'.hom (hT.obj_eq M)).trans (huY (T.obj M))
  have h₂ := iso_inv_heq (hX.obj_eq M) rfl (uX'.app (QX.obj M))
    (QX.mapIso (uX.app M)) (huX M)
  have h₃ := (map_heq T' rfl (hX.obj_eq M) h₂).trans (hT.map_eq (uX.inv.app M))
  have hright := comp_heq ((hT.comp hY).obj_eq M) (hT.obj_eq M)
    ((hX.comp hT).obj_eq M) h₁ h₃
  have hi := congrArg QY.map (h M)
  rw [Functor.map_comp] at hi
  exact eq_of_heq ((hb M).trans ((heq_of_eq hi).trans hright.symm))

/-- A pair of comparisons with its two adjunction compatibility equations.
Source: rationalized smooth adjunction diagrams, coefficient comparison step
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
structure AdjunctionComparisonsData (B : Type r) (A : Type v)
    (unitLaw counitLaw : B → A → Prop) where
  b : B
  a : A
  unit : unitLaw b a
  counit : counitLaw b a

/-- Localized comparisons, retaining both inverse-component formulas and both
adjunction compatibility equations.
Source: rationalized smooth adjunction diagrams, raw coefficient localization step
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
structure LocalizedComparisonsData (B : Type r) (A : Type v)
    (bHom bInv : B → Prop) (aHom aInv : A → Prop)
    (unitLaw counitLaw : B → A → Prop) where
  b : B
  a : A
  b_hom : bHom b
  b_inv : bInv b
  a_hom : aHom a
  a_inv : aInv a
  unit : unitLaw b a
  counit : counitLaw b a


attribute [local irreducible] sfRationalScalarExtension sfRationalScalarComp
  sfRationalScalarUnit sfIntegralScalarComp sfIntegralScalarUnit
  sfConstructibleIntegralScalarExtension sfRationalCoefficientEquiv

section CoefficientData

attribute [local irreducible] instCategoryDerivedCategory
  Padic.coefficientExtensionIntegers sfIntegralConstructibleLinear
  sfIntegralCoefficientLinear DerivedCategory.instPreadditive sfIntegralConstructible
  Padic.coefficientExtensionUniformizer

section Coefficients

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (p₀ : ℕ) (hl : l ≠ p₀)
  {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)
  (s : ∀ B : Padic.FiniteCoefficientFields l Ω, Presentation l B.val j p d)

/-- The published completed integral coefficient functor, restricted to constructibles.
Source: def-weil-integral-scalar-extension and def-weil-rationalization-karoubi
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev integralC (W : Scheme.{u}) (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F) :=
  sfConstructibleIntegralScalarExtension p₀ l hl B.val F.val (IntermediateField.inclusion
    (E := B.val) (F := F.val) h) W

/-- The published rational coefficient functor, with its unchanged integral objects.
Source: def-weil-rationalization-karoubi
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev rationalC (W : Scheme.{u}) (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F) :=
  sfRationalScalarExtension l B.val W p₀ hl F.val (IntermediateField.inclusion
    (E := B.val) (F := F.val) h)

/-- Named component of the integral comparison specification.
Source: the unchanged comparison equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralForwardComparisons :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    P l B.val j p d (s B) ⋙ integralC l Ω p₀ hl Y B F h ≅
      integralC l Ω p₀ hl X B F h ⋙ P l F.val j p d (s F)

/-- Named component of the integral comparison specification.
Source: the unchanged comparison equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralBackwardComparisons :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    H l B.val j p d (s B) ⋙ integralC l Ω p₀ hl X B F h ≅
      integralC l Ω p₀ hl Y B F h ⋙ H l F.val j p d (s F)

/-- Named component of the integral comparison specification.
Source: the unchanged comparison equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralUnitCompatibility (b : IntegralForwardComparisons l Ω p₀ hl j p d s)
    (a : IntegralBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      UnitComparisonLaw (adjunction l B.val j p d (s B)) (adjunction l F.val j p d (s F))
        (integralC l Ω p₀ hl X B F h) (integralC l Ω p₀ hl Y B F h)
        (b B F h) (a B F h)

/-- Named component of the integral comparison specification.
Source: the unchanged comparison equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralCounitCompatibility (b : IntegralForwardComparisons l Ω p₀ hl j p d s)
    (a : IntegralBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      CounitComparisonLaw (adjunction l B.val j p d (s B)) (adjunction l F.val j p d (s F))
        (integralC l Ω p₀ hl X B F h) (integralC l Ω p₀ hl Y B F h)
        (b B F h) (a B F h)

/-- Exactly the two given integral natural isomorphisms and the two integral adjunction
comparison equations. No comparison is chosen or assumed invertible after localization.
Source: field-extension proof, coefficient comparisons
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev IntegralComparisons := AdjunctionComparisonsData
  (IntegralForwardComparisons l Ω p₀ hl j p d s)
  (IntegralBackwardComparisons l Ω p₀ hl j p d s)
  (IntegralUnitCompatibility l Ω p₀ hl j p d s)
  (IntegralCounitCompatibility l Ω p₀ hl j p d s)

variable (r : ∀ B : Padic.FiniteCoefficientFields l Ω, Raw l B.val j p d (s B))
  (c : IntegralComparisons l Ω p₀ hl j p d s)

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalForwardComparisons :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    rationalP l B.val j p d (s B) ⋙ rationalC l Ω p₀ hl Y B F h ≅
      rationalC l Ω p₀ hl X B F h ⋙ rationalP l F.val j p d (s F)

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalBackwardComparisons :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    rationalH l B.val j p d (s B) ⋙ rationalC l Ω p₀ hl X B F h ≅
      rationalC l Ω p₀ hl Y B F h ⋙ rationalH l F.val j p d (s F)

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalForwardHomLaw (b : RationalForwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    HEq ((b B F h).hom.app ⟨M⟩)
      ((sfRationalConstructibleLocalization l F.val Y).map ((c.b B F h).hom.app M))

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalForwardInvLaw (b : RationalForwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    HEq ((b B F h).inv.app ⟨M⟩)
      ((sfRationalConstructibleLocalization l F.val Y).map ((c.b B F h).inv.app M))

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalBackwardHomLaw (a : RationalBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    HEq ((a B F h).hom.app ⟨K⟩)
      ((sfRationalConstructibleLocalization l F.val X).map ((c.a B F h).hom.app K))

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalBackwardInvLaw (a : RationalBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    HEq ((a B F h).inv.app ⟨K⟩)
      ((sfRationalConstructibleLocalization l F.val X).map ((c.a B F h).inv.app K))

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalUnitCompatibility (b : RationalForwardComparisons l Ω p₀ hl j p d s)
    (a : RationalBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      UnitComparisonLaw (r B).adjunction (r F).adjunction
        (rationalC l Ω p₀ hl X B F h) (rationalC l Ω p₀ hl Y B F h)
        (b B F h) (a B F h)

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalCounitCompatibility (b : RationalForwardComparisons l Ω p₀ hl j p d s)
    (a : RationalBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      CounitComparisonLaw (r B).adjunction (r F).adjunction
        (rationalC l Ω p₀ hl X B F h) (rationalC l Ω p₀ hl Y B F h)
        (b B F h) (a B F h)

/-- The rational natural isomorphisms, with exactly the localized integral components,
the localized inverse components and both rational adjunction comparison equations.
HEq only transports the published coefficient functor's specified object equality.
Source: field-extension proof, raw localization of comparisons
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev RationalComparisons := LocalizedComparisonsData
  (RationalForwardComparisons l Ω p₀ hl j p d s)
  (RationalBackwardComparisons l Ω p₀ hl j p d s)
  (RationalForwardHomLaw l Ω p₀ hl j p d s c)
  (RationalForwardInvLaw l Ω p₀ hl j p d s c)
  (RationalBackwardHomLaw l Ω p₀ hl j p d s c)
  (RationalBackwardInvLaw l Ω p₀ hl j p d s c)
  (RationalUnitCompatibility l Ω p₀ hl j p d s r)
  (RationalCounitCompatibility l Ω p₀ hl j p d s r)

/-- The integral coefficient cocycles, with the actual completed-extension associators.
Source: field-extension proof, composition sentence
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralCocycles : Prop :=
  ∀ (B F L : Padic.FiniteCoefficientFields l Ω) (hBF : B ≤ F) (hFL : F ≤ L),
    CoefficientCocycleLaw
      (P l B.val j p d (s B)) (P l F.val j p d (s F))
      (P l L.val j p d (s L))
      (integralC l Ω p₀ hl X B F hBF) (integralC l Ω p₀ hl X F L hFL)
      (integralC l Ω p₀ hl X B L (le_trans hBF hFL))
      (integralC l Ω p₀ hl Y B F hBF) (integralC l Ω p₀ hl Y F L hFL)
      (integralC l Ω p₀ hl Y B L (le_trans hBF hFL))
      (c.b B F hBF) (c.b F L hFL) (c.b B L (le_trans hBF hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF) X
        p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF) Y
        p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL)) ∧
    CoefficientCocycleLaw
      (H l B.val j p d (s B)) (H l F.val j p d (s F))
      (H l L.val j p d (s L))
      (integralC l Ω p₀ hl Y B F hBF) (integralC l Ω p₀ hl Y F L hFL)
      (integralC l Ω p₀ hl Y B L (le_trans hBF hFL))
      (integralC l Ω p₀ hl X B F hBF) (integralC l Ω p₀ hl X F L hFL)
      (integralC l Ω p₀ hl X B L (le_trans hBF hFL))
      (c.a B F hBF) (c.a F L hFL) (c.a B L (le_trans hBF hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF) Y
        p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF) X
        p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))

/-- The same cocycles in raw rational categories, using the published rational associators.
Source: field-extension proof, invert ell in the composition identities
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalCocycles (q : RationalComparisons l Ω p₀ hl j p d s r c) : Prop :=
  ∀ (B F L : Padic.FiniteCoefficientFields l Ω) (hBF : B ≤ F) (hFL : F ≤ L),
    CoefficientCocycleLaw
      (rationalP l B.val j p d (s B)) (rationalP l F.val j p d (s F))
      (rationalP l L.val j p d (s L))
      (rationalC l Ω p₀ hl X B F hBF) (rationalC l Ω p₀ hl X F L hFL)
      (rationalC l Ω p₀ hl X B L (le_trans hBF hFL))
      (rationalC l Ω p₀ hl Y B F hBF) (rationalC l Ω p₀ hl Y F L hFL)
      (rationalC l Ω p₀ hl Y B L (le_trans hBF hFL))
      (q.b B F hBF) (q.b F L hFL) (q.b B L (le_trans hBF hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF) X
        p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF) Y
        p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL)) ∧
    CoefficientCocycleLaw
      (rationalH l B.val j p d (s B)) (rationalH l F.val j p d (s F))
      (rationalH l L.val j p d (s L))
      (rationalC l Ω p₀ hl Y B F hBF) (rationalC l Ω p₀ hl Y F L hFL)
      (rationalC l Ω p₀ hl Y B L (le_trans hBF hFL))
      (rationalC l Ω p₀ hl X B F hBF) (rationalC l Ω p₀ hl X F L hFL)
      (rationalC l Ω p₀ hl X B L (le_trans hBF hFL))
      (q.a B F hBF) (q.a F L hFL) (q.a B L (le_trans hBF hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF) Y
        p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF) X
        p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))

/-- Identity comparisons under the actual completed coefficient-extension unitors.
Source: field-extension proof, identity normalization
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralIdentity : Prop :=
  ∀ B : Padic.FiniteCoefficientFields l Ω,
    CoefficientIdentityLaw (P l B.val j p d (s B))
      (integralC l Ω p₀ hl X B B (le_refl B))
      (integralC l Ω p₀ hl Y B B (le_refl B)) (c.b B B (le_refl B))
      (sfIntegralScalarUnit l B.val X p₀ hl) (sfIntegralScalarUnit l B.val Y p₀ hl) ∧
    CoefficientIdentityLaw (H l B.val j p d (s B))
      (integralC l Ω p₀ hl Y B B (le_refl B))
      (integralC l Ω p₀ hl X B B (le_refl B)) (c.a B B (le_refl B))
      (sfIntegralScalarUnit l B.val Y p₀ hl) (sfIntegralScalarUnit l B.val X p₀ hl)

/-- Identity normalization with the actual rational coefficient-extension unitors.
Source: field-extension proof, raw identity normalization
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalIdentity (q : RationalComparisons l Ω p₀ hl j p d s r c) : Prop :=
  ∀ B : Padic.FiniteCoefficientFields l Ω,
    CoefficientIdentityLaw (rationalP l B.val j p d (s B))
      (rationalC l Ω p₀ hl X B B (le_refl B))
      (rationalC l Ω p₀ hl Y B B (le_refl B)) (q.b B B (le_refl B))
      (sfRationalScalarUnit l B.val X p₀ hl) (sfRationalScalarUnit l B.val Y p₀ hl) ∧
    CoefficientIdentityLaw (rationalH l B.val j p d (s B))
      (rationalC l Ω p₀ hl Y B B (le_refl B))
      (rationalC l Ω p₀ hl X B B (le_refl B)) (q.a B B (le_refl B))
      (sfRationalScalarUnit l B.val Y p₀ hl) (sfRationalScalarUnit l B.val X p₀ hl)

end Coefficients

section CoefficientLocalization

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  (p₀ : ℕ) (hl : l ≠ p₀)

private theorem coefficient_localized_map (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W V : Scheme.{u})
    (T : sfIntegralConstructibleCategory l E W ⥤ sfIntegralConstructibleCategory l E V)
    [T.Additive] [T.Linear (Padic.coefficientExtensionIntegers l E)]
    {M N : sfIntegralConstructibleCategory l E W} (f : M ⟶ N) :
    (localized (Padic.coefficientExtensionUniformizer l E) T).map
        ((sfRationalConstructibleLocalization l E W).map f) =
      (sfRationalConstructibleLocalization l E V).map (T.map f) := by
  unfold sfRationalConstructibleLocalization
  exact localized_map _ T f

private theorem coefficient_localized_heq (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W V : Scheme.{u})
    (T : sfIntegralConstructibleCategory l E W ⥤ sfIntegralConstructibleCategory l E V)
    [T.Additive] [T.Linear (Padic.coefficientExtensionIntegers l E)]
    {M N : sfIntegralConstructibleCategory l E W} (f : M ⟶ N) :
    HEq ((localized (Padic.coefficientExtensionUniformizer l E) T).map
        ((sfRationalConstructibleLocalization l E W).map f))
      ((sfRationalConstructibleLocalization l E V).map (T.map f)) :=
  heq_of_eq (coefficient_localized_map l E W V T f)

attribute [local irreducible] localized
attribute [local instance] localized_additive localized_linear

private theorem coefficient_obj (W : Scheme.{u})
    (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfRationalConstructibleCategory l B.val W) :
    (rationalC l Ω p₀ hl W B F h).obj K =
      ⟨(integralC l Ω p₀ hl W B F h).obj K.obj⟩ := by
  exact sfRationalScalarExtension_obj l B.val W p₀ hl F.val
    (IntermediateField.inclusion (E := B.val) (F := F.val) h) K

private theorem coefficient_map (W : Scheme.{u})
    (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    {K K' : sfIntegralConstructibleCategory l B.val W} (f : K ⟶ K') :
    HEq ((rationalC l Ω p₀ hl W B F h).map
      ((sfRationalConstructibleLocalization l B.val W).map f))
      ((sfRationalConstructibleLocalization l F.val W).map
        ((integralC l Ω p₀ hl W B F h).map f)) := by
  simpa only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
    map_one (sfRationalCoefficientEquiv l B.val),
    map_one (IntermediateField.inclusion (E := B.val) (F := F.val) h),
    map_one (sfRationalCoefficientEquiv l F.val).symm] using
      sfRationalScalarExtension_map_tmul l B.val W p₀ hl F.val
        (IntermediateField.inclusion (E := B.val) (F := F.val) h) K K' f 1

private theorem localizedLift (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W V : Scheme.{u})
    (T : sfIntegralConstructibleCategory l E W ⥤ sfIntegralConstructibleCategory l E V)
    [T.Additive] [T.Linear (Padic.coefficientExtensionIntegers l E)] :
    LiftData (sfRationalConstructibleLocalization l E W)
      (sfRationalConstructibleLocalization l E V) T
      (localized (Padic.coefficientExtensionUniformizer l E) T) where
  obj_eq M := localized_obj (Padic.coefficientExtensionUniformizer l E) T
    ((sfRationalConstructibleLocalization l E W).obj M)
  map_eq f := coefficient_localized_heq l E W V T f

private theorem coefficientLift (W : Scheme.{u})
    (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F) :
    LiftData (sfRationalConstructibleLocalization l B.val W)
      (sfRationalConstructibleLocalization l F.val W)
      (integralC l Ω p₀ hl W B F h) (rationalC l Ω p₀ hl W B F h) where
  obj_eq M := coefficient_obj l Ω p₀ hl W B F h ⟨M⟩
  map_eq f := coefficient_map l Ω p₀ hl W B F h f

private theorem coefficient_square (W V : Scheme.{u})
    (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (F₀ : sfIntegralConstructibleCategory l B.val W ⥤
      sfIntegralConstructibleCategory l B.val V)
    [F₀.Additive] [F₀.Linear (Padic.coefficientExtensionIntegers l B.val)]
    (F₁ : sfIntegralConstructibleCategory l F.val W ⥤
      sfIntegralConstructibleCategory l F.val V)
    [F₁.Additive] [F₁.Linear (Padic.coefficientExtensionIntegers l F.val)]
    (e : F₀ ⋙ integralC l Ω p₀ hl V B F h ≅
      integralC l Ω p₀ hl W B F h ⋙ F₁) :
    ∃ a : localized (Padic.coefficientExtensionUniformizer l B.val) F₀ ⋙
        rationalC l Ω p₀ hl V B F h ≅
      rationalC l Ω p₀ hl W B F h ⋙
        localized (Padic.coefficientExtensionUniformizer l F.val) F₁,
      (∀ K, HEq (a.hom.app K)
        ((sfRationalConstructibleLocalization l F.val V).map (e.hom.app K.obj))) ∧
      (∀ K, HEq (a.inv.app K)
        ((sfRationalConstructibleLocalization l F.val V).map (e.inv.app K.obj))) := by
  exact localized_square
    (R := Padic.coefficientExtensionIntegers l B.val)
    (S := Padic.coefficientExtensionIntegers l F.val)
    (C := sfIntegralConstructibleCategory l B.val W)
    (D := sfIntegralConstructibleCategory l B.val V)
    (C' := sfIntegralConstructibleCategory l F.val W)
    (D' := sfIntegralConstructibleCategory l F.val V)
    (Padic.coefficientExtensionUniformizer l B.val)
    (Padic.coefficientExtensionUniformizer l F.val)
    (fun a ↦ (sfRationalCoefficientEquiv l F.val).symm
      ((IntermediateField.inclusion
        (E := B.val) (F := F.val) h) (sfRationalCoefficientEquiv l B.val a)))
    F₀ F₁ (integralC l Ω p₀ hl W B F h) (integralC l Ω p₀ hl V B F h)
    (rationalC l Ω p₀ hl W B F h) (rationalC l Ω p₀ hl V B F h)
    (coefficient_obj l Ω p₀ hl W B F h) (coefficient_obj l Ω p₀ hl V B F h)
    (sfRationalScalarExtension_map_tmul l B.val W p₀ hl F.val
      (IntermediateField.inclusion (E := B.val) (F := F.val) h))
    (sfRationalScalarExtension_map_tmul l B.val V p₀ hl F.val
      (IntermediateField.inclusion (E := B.val) (F := F.val) h)) e

private theorem coefficient_comp (W : Scheme.{u})
    (B F L : Padic.FiniteCoefficientFields l Ω) (hBF : B ≤ F) (hFL : F ≤ L)
    (M : sfRationalConstructibleCategory l B.val W) :
    HEq ((sfRationalScalarComp l B.val F.val (IntermediateField.inclusion
      (E := B.val) (F := F.val) hBF)
      W p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL)).hom.app M)
      ((sfRationalConstructibleLocalization l L.val W).map
        ((sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion
          (E := B.val) (F := F.val) hBF)
          W p₀ hl L.val (IntermediateField.inclusion
            (E := F.val) (F := L.val) hFL)).hom.app M.obj)) := by
  unfold sfRationalScalarComp
  exact (sfRationalScalarComp_existsUnique l B.val F.val (IntermediateField.inclusion
    (E := B.val) (F := F.val) hBF)
    W p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL)).exists.choose_spec M

private theorem coefficient_unit (W : Scheme.{u})
    (B : Padic.FiniteCoefficientFields l Ω) (M : sfRationalConstructibleCategory l B.val W) :
    HEq ((sfRationalScalarUnit l B.val W p₀ hl).hom.app M)
      ((sfRationalConstructibleLocalization l B.val W).map
        ((sfIntegralScalarUnit l B.val W p₀ hl).hom.app M.obj)) := by
  unfold sfRationalScalarUnit
  exact (sfRationalScalarUnit_existsUnique l B.val W p₀ hl).exists.choose_spec M

attribute [local irreducible] ScalarLocalization.category
  ScalarLocalization.preadditive ScalarLocalization.linear ScalarLocalization.linearOriginal
  ObjectProperty.FullSubcategory.category Preadditive.fullSubcategory Linear.fullSubcategory

private theorem coefficient_cocycle (W V : Scheme.{u})
    (T : ∀ B : Padic.FiniteCoefficientFields l Ω,
      sfIntegralConstructibleCategory l B.val W ⥤ sfIntegralConstructibleCategory l B.val V)
    [∀ B, (T B).Additive] [∀ B, (T B).Linear (Padic.coefficientExtensionIntegers l B.val)]
    (e : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      T B ⋙ integralC l Ω p₀ hl V B F h ≅ integralC l Ω p₀ hl W B F h ⋙ T F)
    (a : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      localized (Padic.coefficientExtensionUniformizer l B.val) (T B) ⋙
          rationalC l Ω p₀ hl V B F h ≅
        rationalC l Ω p₀ hl W B F h ⋙
          localized (Padic.coefficientExtensionUniformizer l F.val) (T F))
    (ha : ∀ B F h M, HEq ((a B F h).hom.app M)
      ((sfRationalConstructibleLocalization l F.val V).map ((e B F h).hom.app M.obj)))
    (B F L : Padic.FiniteCoefficientFields l Ω) (hBF : B ≤ F) (hFL : F ≤ L)
    (he : CoefficientCocycleLaw (T B) (T F) (T L)
      (integralC l Ω p₀ hl W B F hBF) (integralC l Ω p₀ hl W F L hFL)
      (integralC l Ω p₀ hl W B L (le_trans hBF hFL))
      (integralC l Ω p₀ hl V B F hBF) (integralC l Ω p₀ hl V F L hFL)
      (integralC l Ω p₀ hl V B L (le_trans hBF hFL))
      (e B F hBF) (e F L hFL) (e B L (le_trans hBF hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF)
        W p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF)
        V p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))) :
    CoefficientCocycleLaw
      (localized (Padic.coefficientExtensionUniformizer l B.val) (T B))
      (localized (Padic.coefficientExtensionUniformizer l F.val) (T F))
      (localized (Padic.coefficientExtensionUniformizer l L.val) (T L))
      (rationalC l Ω p₀ hl W B F hBF) (rationalC l Ω p₀ hl W F L hFL)
      (rationalC l Ω p₀ hl W B L (le_trans hBF hFL))
      (rationalC l Ω p₀ hl V B F hBF) (rationalC l Ω p₀ hl V F L hFL)
      (rationalC l Ω p₀ hl V B L (le_trans hBF hFL))
      (a B F hBF) (a F L hFL) (a B L (le_trans hBF hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF)
        W p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion
        (E := B.val) (F := F.val) hBF)
        V p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL)) := by
  exact lifted_cocycle_law
    (C₀ := sfIntegralConstructibleCategory l B.val W)
    (C₁ := sfIntegralConstructibleCategory l F.val W)
    (C₂ := sfIntegralConstructibleCategory l L.val W)
    (D₀ := sfIntegralConstructibleCategory l B.val V)
    (D₁ := sfIntegralConstructibleCategory l F.val V)
    (D₂ := sfIntegralConstructibleCategory l L.val V)
    (C₀' := sfRationalConstructibleCategory l B.val W)
    (C₁' := sfRationalConstructibleCategory l F.val W)
    (C₂' := sfRationalConstructibleCategory l L.val W)
    (D₀' := sfRationalConstructibleCategory l B.val V)
    (D₁' := sfRationalConstructibleCategory l F.val V)
    (D₂' := sfRationalConstructibleCategory l L.val V)
    (sfRationalConstructibleLocalization l B.val W)
    (sfRationalConstructibleLocalization l F.val W)
    (sfRationalConstructibleLocalization l L.val W)
    (sfRationalConstructibleLocalization l B.val V)
    (sfRationalConstructibleLocalization l F.val V)
    (sfRationalConstructibleLocalization l L.val V)
    (fun ⟨M⟩ ↦ ⟨M, rfl⟩)
    (localizedLift l B.val W V (T B)) (localizedLift l F.val W V (T F))
    (localizedLift l L.val W V (T L))
    (coefficientLift l Ω p₀ hl W B F hBF) (coefficientLift l Ω p₀ hl W F L hFL)
    (coefficientLift l Ω p₀ hl W B L (le_trans hBF hFL))
    (coefficientLift l Ω p₀ hl V B F hBF) (coefficientLift l Ω p₀ hl V F L hFL)
    (coefficientLift l Ω p₀ hl V B L (le_trans hBF hFL))
    (e B F hBF) (e F L hFL) (e B L (le_trans hBF hFL))
    (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion (E := B.val) (F := F.val) hBF)
      W p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
    (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion (E := B.val) (F := F.val) hBF)
      V p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
    (a B F hBF) (a F L hFL) (a B L (le_trans hBF hFL))
    (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion (E := B.val) (F := F.val) hBF)
      W p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
    (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion (E := B.val) (F := F.val) hBF)
      V p₀ hl L.val (IntermediateField.inclusion (E := F.val) (F := L.val) hFL))
    (fun M ↦ ha B F hBF ⟨M⟩) (fun M ↦ ha F L hFL ⟨M⟩)
    (fun M ↦ ha B L (le_trans hBF hFL) ⟨M⟩)
    (fun M ↦ coefficient_comp l Ω p₀ hl W B F L hBF hFL ⟨M⟩)
    (fun M ↦ coefficient_comp l Ω p₀ hl V B F L hBF hFL ⟨M⟩) he

private theorem coefficient_identity (W V : Scheme.{u})
    (B : Padic.FiniteCoefficientFields l Ω)
    (T : sfIntegralConstructibleCategory l B.val W ⥤ sfIntegralConstructibleCategory l B.val V)
    [T.Additive] [T.Linear (Padic.coefficientExtensionIntegers l B.val)]
    (e : T ⋙ integralC l Ω p₀ hl V B B (le_refl B) ≅
      integralC l Ω p₀ hl W B B (le_refl B) ⋙ T)
    (a : localized (Padic.coefficientExtensionUniformizer l B.val) T ⋙
        rationalC l Ω p₀ hl V B B (le_refl B) ≅
      rationalC l Ω p₀ hl W B B (le_refl B) ⋙
        localized (Padic.coefficientExtensionUniformizer l B.val) T)
    (ha : ∀ M, HEq (a.hom.app M)
      ((sfRationalConstructibleLocalization l B.val V).map (e.hom.app M.obj)))
    (he : CoefficientIdentityLaw T
      (integralC l Ω p₀ hl W B B (le_refl B))
      (integralC l Ω p₀ hl V B B (le_refl B)) e
      (sfIntegralScalarUnit l B.val W p₀ hl) (sfIntegralScalarUnit l B.val V p₀ hl)) :
    CoefficientIdentityLaw (localized (Padic.coefficientExtensionUniformizer l B.val) T)
      (rationalC l Ω p₀ hl W B B (le_refl B))
      (rationalC l Ω p₀ hl V B B (le_refl B)) a
      (sfRationalScalarUnit l B.val W p₀ hl) (sfRationalScalarUnit l B.val V p₀ hl) := by
  exact lifted_identity_law
    (C := sfIntegralConstructibleCategory l B.val W)
    (D := sfIntegralConstructibleCategory l B.val V)
    (C' := sfRationalConstructibleCategory l B.val W)
    (D' := sfRationalConstructibleCategory l B.val V)
    (sfRationalConstructibleLocalization l B.val W)
    (sfRationalConstructibleLocalization l B.val V) (fun ⟨M⟩ ↦ ⟨M, rfl⟩)
    (localizedLift l B.val W V T)
    (coefficientLift l Ω p₀ hl W B B (le_refl B))
    (coefficientLift l Ω p₀ hl V B B (le_refl B)) e
    (sfIntegralScalarUnit l B.val W p₀ hl) (sfIntegralScalarUnit l B.val V p₀ hl) a
    (sfRationalScalarUnit l B.val W p₀ hl) (sfRationalScalarUnit l B.val V p₀ hl)
    (fun M ↦ ha ⟨M⟩) (fun M ↦ coefficient_unit l Ω p₀ hl W B ⟨M⟩)
    (fun M ↦ coefficient_unit l Ω p₀ hl V B ⟨M⟩) he

end CoefficientLocalization

section Coefficients

set_option allowUnsafeReducibility true in
attribute [local irreducible] integralC rationalC

attribute [local irreducible] localized ScalarLocalization.category
  ScalarLocalization.preadditive ScalarLocalization.linear ScalarLocalization.linearOriginal
  ObjectProperty.FullSubcategory.category Preadditive.fullSubcategory Linear.fullSubcategory
attribute [local instance] localized_additive localized_linear

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (p₀ : ℕ) (hl : l ≠ p₀)
  {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)
  (s : ∀ B : Padic.FiniteCoefficientFields l Ω, Presentation l B.val j p d)

variable (r : ∀ B : Padic.FiniteCoefficientFields l Ω, Raw l B.val j p d (s B))
  (c : IntegralComparisons l Ω p₀ hl j p d s)

/-- Localized coefficient comparisons, including all rational naturality squares,
both adjunction equations, both cocycles and identity normalization.
Source: field-extension proof, invert ell
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: integral scalar extension is additive and semilinear for the integer-ring map.
The source uniformizer has nonzero, hence invertible, image in the target coefficient
field. Apply lem-pur-semilinear-scalar-localization to both comparison transformations.
Their components and inverse components are Q of the integral ones. Pure-tensor
naturality follows by multiplying integral naturality by the coefficient scalar;
additivity extends it to every finite sum, including every rational isomorphism and
its inverse. Localize the two given integral unit/counit equations factor by factor.
For triples, apply Q to each integral cocycle; the localized completed associator is
sfRationalScalarComp by its component characterization. Apply the same argument to
sfIntegralScalarUnit and Q(id)=id for identity normalization. No integral inverse to a
rational isomorphism is used. -/
theorem coefficient_comparisons :
    ∃ q : RationalComparisons l Ω p₀ hl j p d s r c,
      (IntegralCocycles l Ω p₀ hl j p d s c →
        RationalCocycles l Ω p₀ hl j p d s r c q) ∧
      (IntegralIdentity l Ω p₀ hl j p d s c →
        RationalIdentity l Ω p₀ hl j p d s r c q) := by
  cases (inferInstance : IsAlgClosure (Padic l) Ω)
  classical
  have bdata (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F) :=
    coefficient_square l Ω p₀ hl X Y B F h
      (P l B.val j p d (s B)) (P l F.val j p d (s F)) (c.b B F h)
  have adata (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F) :=
    coefficient_square l Ω p₀ hl Y X B F h
      (H l B.val j p d (s B)) (H l F.val j p d (s F)) (c.a B F h)
  choose b hb_hom hb_inv using bdata
  choose a ha_hom ha_inv using adata
  have hq : Nonempty (RationalComparisons l Ω p₀ hl j p d s r c) := ⟨{
    b := b
    a := a
    b_hom := fun B F h M ↦ hb_hom B F h ⟨M⟩
    b_inv := fun B F h M ↦ hb_inv B F h ⟨M⟩
    a_hom := fun B F h K ↦ ha_hom B F h ⟨K⟩
    a_inv := fun B F h K ↦ ha_inv B F h ⟨K⟩
    unit := by
      intro B F h
      exact lifted_unit_law
        (C₀ := sfIntegralConstructibleCategory l B.val X)
        (D₀ := sfIntegralConstructibleCategory l B.val Y)
        (C₁ := sfIntegralConstructibleCategory l F.val X)
        (D₁ := sfIntegralConstructibleCategory l F.val Y)
        (C₀' := sfRationalConstructibleCategory l B.val X)
        (D₀' := sfRationalConstructibleCategory l B.val Y)
        (C₁' := sfRationalConstructibleCategory l F.val X)
        (D₁' := sfRationalConstructibleCategory l F.val Y)
        (sfRationalConstructibleLocalization l B.val X)
        (sfRationalConstructibleLocalization l B.val Y)
        (sfRationalConstructibleLocalization l F.val X)
        (sfRationalConstructibleLocalization l F.val Y)
        (fun ⟨M⟩ ↦ ⟨M, rfl⟩)
        (adjunction l B.val j p d (s B)) (adjunction l F.val j p d (s F))
        (r B).adjunction (r F).adjunction
        (localizedLift l B.val X Y (P l B.val j p d (s B)))
        (localizedLift l B.val Y X (H l B.val j p d (s B)))
        (localizedLift l F.val X Y (P l F.val j p d (s F)))
        (localizedLift l F.val Y X (H l F.val j p d (s F)))
        (coefficientLift l Ω p₀ hl X B F h) (coefficientLift l Ω p₀ hl Y B F h)
        (c.b B F h) (c.a B F h) (b B F h) (a B F h)
        (fun M ↦ hb_hom B F h ⟨M⟩) (fun M ↦ ha_hom B F h ⟨M⟩)
        (fun M ↦ raw_unit_heq l B.val j p d (s B) (r B) M)
        (fun M ↦ raw_unit_heq l F.val j p d (s F) (r F) M)
        (c.unit B F h)
    counit := by
      intro B F h
      exact lifted_counit_law
        (C₀ := sfIntegralConstructibleCategory l B.val X)
        (D₀ := sfIntegralConstructibleCategory l B.val Y)
        (C₁ := sfIntegralConstructibleCategory l F.val X)
        (D₁ := sfIntegralConstructibleCategory l F.val Y)
        (C₀' := sfRationalConstructibleCategory l B.val X)
        (D₀' := sfRationalConstructibleCategory l B.val Y)
        (C₁' := sfRationalConstructibleCategory l F.val X)
        (D₁' := sfRationalConstructibleCategory l F.val Y)
        (sfRationalConstructibleLocalization l B.val X)
        (sfRationalConstructibleLocalization l B.val Y)
        (sfRationalConstructibleLocalization l F.val X)
        (sfRationalConstructibleLocalization l F.val Y)
        (fun ⟨M⟩ ↦ ⟨M, rfl⟩)
        (adjunction l B.val j p d (s B)) (adjunction l F.val j p d (s F))
        (r B).adjunction (r F).adjunction
        (localizedLift l B.val X Y (P l B.val j p d (s B)))
        (localizedLift l B.val Y X (H l B.val j p d (s B)))
        (localizedLift l F.val X Y (P l F.val j p d (s F)))
        (localizedLift l F.val Y X (H l F.val j p d (s F)))
        (coefficientLift l Ω p₀ hl X B F h) (coefficientLift l Ω p₀ hl Y B F h)
        (c.b B F h) (c.a B F h) (b B F h) (a B F h)
        (fun M ↦ hb_hom B F h ⟨M⟩) (fun M ↦ ha_hom B F h ⟨M⟩)
        (fun M ↦ raw_counit_heq l B.val j p d (s B) (r B) M)
        (fun M ↦ raw_counit_heq l F.val j p d (s F) (r F) M)
        (c.counit B F h) }⟩
  obtain ⟨q⟩ := hq
  refine ⟨q, ?_, ?_⟩
  · intro h B F L hBF hFL
    exact ⟨coefficient_cocycle l Ω p₀ hl X Y
        (fun B ↦ P l B.val j p d (s B)) c.b q.b
        (fun B F h M ↦ q.b_hom B F h M.obj) B F L hBF hFL
        (h B F L hBF hFL).1,
      coefficient_cocycle l Ω p₀ hl Y X
        (fun B ↦ H l B.val j p d (s B)) c.a q.a
        (fun B F h M ↦ q.a_hom B F h M.obj) B F L hBF hFL
        (h B F L hBF hFL).2⟩
  · intro h B
    exact ⟨coefficient_identity l Ω p₀ hl X Y B (P l B.val j p d (s B))
        (c.b B B (le_refl B)) (q.b B B (le_refl B))
        (fun M ↦ q.b_hom B B (le_refl B) M.obj) (h B).1,
      coefficient_identity l Ω p₀ hl Y X B (H l B.val j p d (s B))
        (c.a B B (le_refl B)) (q.a B B (le_refl B))
        (fun M ↦ q.a_hom B B (le_refl B) M.obj) (h B).2⟩

end Coefficients


end CoefficientData

section CondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (p : Z ⟶ Y) [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (d : ℕ) (s : Presentation l E j p d)

/-- The tensor of the uniquely fixed integral Hom equivalence, in raw Hom coordinates.
Source: rational-adjunction proof (1), middle bijection
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
@[irreducible]
def tensorHom (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E Y) :
    ((rationalP l E j p d s).obj ⟨M⟩ ⟶ ⟨K⟩) ≃
      (⟨M⟩ ⟶ (rationalH l E j p d s).obj ⟨K⟩) :=
  (TensorProduct.congr
    (LinearEquiv.refl (Padic.coefficientExtensionIntegers l E)
      (Localization.Away (Padic.coefficientExtensionUniformizer l E)))
    (hom_linear l E j p d s M K).choose).toEquiv

/-- The source's three-bijection construction with its two specified endpoints.
Source: rational-adjunction proof (1), the displayed Hom chain
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
@[irreducible]
def threeHom (e : Endpoints l E j p d s) (rho : HomComparisons l E j p d s)
    (M : sfIntegralConstructibleCategory l E X) (K : sfIntegralConstructibleCategory l E Y) :
    ((condensedP l E j p).obj ((realizeX l E j p d s).obj M) ⟶
      (realizeY l E j p d s).obj K) ≃
    ((realizeX l E j p d s).obj M ⟶
      (condensedH l E j p d s).obj ((realizeY l E j p d s).obj K)) :=
  (Iso.homCongr (e.compactSupport.app M).symm (Iso.refl _)).trans
    ((rho.rhoY _ K).toEquiv.symm.trans
      ((tensorHom l E j p d s M K).trans
        ((rho.rhoX M _).toEquiv.trans
          (Iso.homCongr (Iso.refl _) (e.twistedPullback.app K)))))

/-- Three-bijection normalization of rational purity in the actual condensed endpoints.
It is characterized on every rational Hom arrow; hence it also fixes the unit obtained
by applying the equivalence to the identity, including changes of integral model.
Source: rational-adjunction proof (1), displayed three bijections
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: conjugate source Homs by the compact-support endpoint comparison, use rhoY
backwards, apply the tensor of the integral smooth Hom bijection, then apply rhoX and
postcompose with the twisted-pullback endpoint comparison. On a pure tensor, Raw.hom_tmul
identifies the middle map with Phi^H tensor 1. Additivity extends equality to every
finite sum. The canonical endpoint maps are the compactification reconstruction of
integral-direct-image-tower (2), and ordinary-line scalar comparison followed by derived
tensor associativity and t_(2d,0), whose sign is positive. Thus this is the source's
three-bijection construction; evaluating at identity gives the same rational purity unit.
No integral lift of a rational inverse is involved. -/
theorem realization_agreement (r : Raw l E j p d s)
    (e : Endpoints l E j p d s) (rho : HomComparisons l E j p d s)
    (M : sfIntegralConstructibleCategory l E X) (K : sfIntegralConstructibleCategory l E Y) :
    ∀ h : (rationalP l E j p d s).obj ⟨M⟩ ⟶ ⟨K⟩,
      threeHom l E j p d s e rho M K
        ((e.compactSupport.inv.app M) ≫ rho.rhoY _ K h) =
      rho.rhoX M _ (r.adjunction.homEquiv ⟨M⟩ ⟨K⟩ h) ≫
        e.twistedPullback.hom.app K := by
  intro h
  have hphi (f : (P l E j p d s).obj M ⟶ K) :
      (hom_linear l E j p d s M K).choose f =
        (adjunction l E j p d s).homEquiv M K f :=
    congrArg (fun e ↦ e f) (hom_linear l E j p d s M K).choose_spec
  let T := TensorProduct.congr
    (LinearEquiv.refl (Padic.coefficientExtensionIntegers l E)
      (Localization.Away (Padic.coefficientExtensionUniformizer l E)))
    (hom_linear l E j p d s M K).choose
  have ht (f : (rationalP l E j p d s).obj ⟨M⟩ ⟶ ⟨K⟩) :
      tensorHom l E j p d s M K f = r.adjunction.homEquiv ⟨M⟩ ⟨K⟩ f := by
    unfold tensorHom
    change T f = r.adjunction.homEquiv ⟨M⟩ ⟨K⟩ f
    induction f using TensorProduct.induction_on with
    | zero =>
      rw [map_zero]
      have hz := r.hom_smul ⟨M⟩ ⟨K⟩ 0 0
      simpa only [zero_smul] using hz.symm
    | tmul a f =>
      dsimp only [T]
      rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hphi, r.hom_tmul]
    | add f g hf hg => rw [map_add, r.hom_add, hf, hg]
  unfold threeHom
  exact normalizedHomChain (e.compactSupport.app M) (e.twistedPullback.app K)
    (rho.rhoY _ K).toEquiv (tensorHom l E j p d s M K) (rho.rhoX M _).toEquiv
    (r.adjunction.homEquiv ⟨M⟩ ⟨K⟩) ht h

/-- The full smooth-adjunction rationalization statement in the standing geometric
setting. The data s are the already constructed integral tower adjunctions and purity
realizations; c consists exactly of the assumed integral coefficient comparisons with
both adjunction equations. Rational cocycles and identity comparisons are conditional
on their stated integral counterparts. The last assertion compares bijections at the
actual condensed endpoints; it applies in particular to the canonical endpoint maps
of integral-direct-image-tower (2) and the derived pullback/line/shift comparisons.
Source: field-extension proof, final sentence; rational-adjunction proof (1)
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams).
Proof: (1) the strict compact-support reduction tower is linear, and the K-injective
computation makes its total derived limit linear. (2) transport the integral tower
adjunction along its specified gamma; bilinearity gives a linear Hom equivalence and
linear inverse. (3) tensor this equivalence with the localized coefficient field.
(4) tensor naturality and additivity prove naturality for every finite tensor sum;
the images of eta and epsilon obey both triangles. (5) semilinear scalar localization
extends b0 and a0, including their inverse components and all rational naturality
squares. (6) applying Q to the two integral adjunction equations gives both rational
ones. (7) apply Q to the integral cocycles and identity normalizations, using the
specified scalar associators. (8) the localized-Hom theorem supplies rho in the actual
continuous coefficient realization. (9) integral direct-image clause (2) identifies
the compact-support endpoint, and derived associativity with the ordinary Tate line
and shift identifies the other endpoint. (10) check the three-bijection equality on
pure tensors and extend by additivity. Applying it to the identity fixes the same
rational purity unit. All constructions stay in raw localization. -/
theorem rationalized_smooth_adjunction_diagrams
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [(j ≫ p).IsOver (Spec (.of D.k))] [SmoothOfRelativeDimension d (j ≫ p)]
    (t : ∀ B : Padic.FiniteCoefficientFields l Ω, Presentation l B.val j p d)
    (c : IntegralComparisons l Ω D.p hl j p d t) :
    (∀ B : Padic.FiniteCoefficientFields l Ω,
      (P l B.val j p d (t B)).Linear (Padic.coefficientExtensionIntegers l B.val)) ∧
    (∀ B : Padic.FiniteCoefficientFields l Ω,
      (J l B.val j p d (t B)).Linear (Padic.coefficientExtensionIntegers l B.val)) ∧
    (∀ (B : Padic.FiniteCoefficientFields l Ω)
      (M : sfIntegralConstructibleCategory l B.val X)
      (K : sfIntegralConstructibleCategory l B.val Y),
      ∃ e : ((P l B.val j p d (t B)).obj M ⟶ K) ≃ₗ[
          Padic.coefficientExtensionIntegers l B.val]
        (M ⟶ (H l B.val j p d (t B)).obj K),
        e.toEquiv = (adjunction l B.val j p d (t B)).homEquiv M K) ∧
    ∃ r : ∀ B : Padic.FiniteCoefficientFields l Ω, Raw l B.val j p d (t B),
      (∃ q : RationalComparisons l Ω D.p hl j p d t r c,
        (IntegralCocycles l Ω D.p hl j p d t c →
          RationalCocycles l Ω D.p hl j p d t r c q) ∧
        (IntegralIdentity l Ω D.p hl j p d t c →
          RationalIdentity l Ω D.p hl j p d t r c q)) ∧
      ∀ B : Padic.FiniteCoefficientFields l Ω,
      Nonempty (Endpoints l B.val j p d (t B)) ∧
      ∃ rho : HomComparisons l B.val j p d (t B),
      ∀ (e : Endpoints l B.val j p d (t B))
        (M : sfIntegralConstructibleCategory l B.val X)
        (K : sfIntegralConstructibleCategory l B.val Y)
        (h : (rationalP l B.val j p d (t B)).obj ⟨M⟩ ⟶ ⟨K⟩),
        threeHom l B.val j p d (t B) e rho M K
          (e.compactSupport.inv.app M ≫ rho.rhoY _ K h) =
        rho.rhoX M _ ((r B).adjunction.homEquiv ⟨M⟩ ⟨K⟩ h) ≫
          e.twistedPullback.hom.app K := by
  sorry

end CondensedRealization

end WeilConjectures.RationalizedSmoothAdjunction
