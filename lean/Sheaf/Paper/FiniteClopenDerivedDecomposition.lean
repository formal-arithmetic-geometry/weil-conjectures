/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.ConstantCoefficientObjectsConstructible
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Finite clopen decomposition of derived coefficient categories

Source: Stacks Project, Tag 04TS, and the finite-clopen argument in the blueprint
sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: lem-pur-finite-clopen-derived-decomposition).

Restrictions below are actual precomposition on the small pro-etale sites. The
coefficient rings are the published finite quotients and completed integral sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

/-- Finite or completed coefficients, with n denoting exponent n+1.
Source: Stacks 04TS and the section-invariant finite-clopen argument
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRing (X : Scheme.{u}) (n : ℕ) (integral : Bool) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  if integral then completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension X
  else integralCoefficientCommRingSheaf P.coefficients.l P.extension X n

/-- The actual inclusion of the component site: compose its structure map with j.
Source: Stacks 00XZ, 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenSiteInclusion {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

/-- Continuity of this concrete site inclusion, with no added assumption.
Source: Stacks 00XZ (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenSiteInclusionContinuous {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    (clopenSiteInclusion j).IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

/-- Restrict a coefficient ring by precomposition along the component site.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRingRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ((clopenSiteInclusion j).sheafPushforwardContinuous CommRingCat.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj R

/-- Forget commutativity only; this is the published module-sheaf encoding.
Source: Stacks Modules on Sites (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
abbrev clopenModules (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The canonical sectionwise module restriction, including its scalar action.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    clopenModules X R ⥤ clopenModules Y (clopenRingRestriction j R) :=
  SheafOfModules.pushforward (F := clopenSiteInclusion j) (𝟙 _)

/-- Exactness of restriction, required to descend the actual degreewise functor.
Source: Stacks 04TS and 015F (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: localize the small site at the open immersion (weakly-etale localization).
Restriction of module sheaves is exact; kernels and sheafified cokernels restrict
locally. Its formula is additive. This uses sheaf exactness, not sectionwise
surjectivity of epimorphisms. -/
theorem clopenRestriction_exact {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (clopenRestriction j R).Additive ∧ PreservesFiniteLimits (clopenRestriction j R) ∧
      PreservesFiniteColimits (clopenRestriction j R) := by
  sorry

/-- Additivity from exact sectionwise restriction. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionAdditive {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (clopenRestriction j R).Additive := (clopenRestriction_exact j R).1

/-- Left exactness from the preceding named theorem. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionLimits {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (clopenRestriction j R) := (clopenRestriction_exact j R).2.1

/-- Right exactness from the preceding named theorem. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionColimits {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (clopenRestriction j R) := (clopenRestriction_exact j R).2.2

/-- The standard unbounded localization of these abelian module categories.
Source: Stacks 05RU (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenHasDerived (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory (clopenModules X R) := HasDerivedCategory.standard _

/-- Restrict complexes degreewise and descend through quasi-isomorphisms.
Source: Stacks 015F, 05RU (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenDerivedRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  (clopenRestriction j R).mapDerivedCategory

/-- Invertibility of ell in a residue field over the fixed algebraically closed base.
Source: purity conventions (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: ell differs from p, so is nonzero in k. The structure map to the residue
field carries its inverse in k to an inverse there. No new geometric hypothesis
is required. -/
theorem clopenResidue_isUnit (Y : Over (Spec (CommRingCat.of P.field.k))) (y : Y.left) :
    IsUnit (P.coefficients.l : Y.left.residueField y) := by
  sorry

/-- The recorded constructible integral pullback, supplying only the source-implied
residue-field invertibility. Source: blueprint integral coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralPullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  constructibleIntegralPullback P.coefficients.l P.extension j.left

/-- The recorded raw rationalized pullback, without Karoubi completion.
Source: blueprint rational coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalPullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  rationalDerivedPullback P.coefficients.l P.extension j.left

/-- The recorded common-stage pullback, on the fixed algebraic coefficient closure.
Source: blueprint common-stage coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStagePullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar j.left


/-- The completed tensor on the constructible integral category, with the recorded
normalization on strict K-flat towers. Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  constructibleIntegralTensor P.coefficients.l P.extension Y.left

/-- The recorded rational tensor, extended linearly on morphisms.
Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  rationalDerivedTensor P.coefficients.l P.extension Y.left

/-- The common-stage tensor, formed at the coefficient compositum.
Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStageTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar Y.left

/-- The actual regular completed module in the intrinsic constructible category.
Only its membership proof comes from the published constant-coefficient theorem.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralUnit (Y : Scheme.{u}) :
    sfIntegralConstructibleCategory P.coefficients.l P.extension Y :=
  ⟨integralConstantCoefficientObject P.coefficients.l P.extension Y,
    (integralConstantCoefficient_constructible P.coefficients.l P.extension Y
      P.field P.coefficients.different).2.1⟩

/-- The raw rational image of the same regular integral module.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalUnit (Y : Scheme.{u}) :=
  (sfRationalConstructibleLocalization P.coefficients.l P.extension Y).obj (P.clopenIntegralUnit Y)

/-- The coefficient unit at any finite stage of the fixed algebraic closure.
Its small field model is the published one, and its integral representative is
the regular completed module in degree zero.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStageUnit (Y : Scheme.{u})
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar) :
    generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar Y :=
  ⟨B, (sfRationalConstructibleLocalization P.coefficients.l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    Y).obj
      ⟨integralConstantCoefficientObject P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B) Y,
        (integralConstantCoefficient_constructible P.coefficients.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
          Y P.field P.coefficients.different).2.1⟩⟩

/-- The existing canonical integral scalar/restriction comparison, on every finite
coefficient extension including identities. Source: blueprint coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralScalarComparison (L : Type u) [Field L]
    [Algebra (Padic P.coefficients.l) L] [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (K : sfIntegralConstructibleCategory P.coefficients.l P.extension X.left) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  integralPullbackScalarComparison P.coefficients.l P.extension L ι j.left K

/-- The same normalized comparison after raw rationalization. Its action is the
linear extension of the preceding integral map, exactly as in the recorded operations.
Source: blueprint coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalScalarComparison (L : Type u) [Field L]
    [Algebra (Padic P.coefficients.l) L] [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  rationalPullbackScalarComparison P.coefficients.l P.extension L ι j.left

section Decomposition
variable (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hft hqc hfinite hclosed hdisjoint hcover

/-- Exact module equivalence and its explicit sectionwise inverse.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: steps 1--3 of the node. The components cover the pro-etale site; distinct
intersections are empty. Glue modules and morphisms (module-sheaf gluing and set
sheaf morphism descent). On a test object V the inverse has sections the product
of the sections on V times_X Xi. Restriction maps and scalar actions are componentwise.
The sheaf axiom gives the unit and counit. Additivity is sectionwise and an additive
equivalence preserves kernels and cokernels. Empty components give zero factors;
the empty cover forces every section group to be zero. -/
theorem finiteClopen_module_equivalence (n : ℕ) (integral : Bool) :
    ∃ e : clopenModules X.left (P.clopenRing X.left n integral) ≌
        (∀ i, clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
      e.functor = Functor.pi' (fun i ↦
        clopenRestriction (j i).left (P.clopenRing X.left n integral)) ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      ∃ φ : ∀ (F : ∀ i, clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
          (V : X.left.ProEt),
        ((e.inverse.obj F).val.obj (op V)) ≃+
          (∀ i, (F i).val.obj (op ((Scheme.proEtaleBaseChange (j i).left).obj V))),
        (∀ F V (r : (P.clopenRing X.left n integral).obj.obj (op V))
          (x : (e.inverse.obj F).val.obj (op V)) (i : I),
          φ F V (r • x) i =
            ((P.clopenRing X.left n integral).obj.map
              (MorphismProperty.Over.homMk
                (A := (clopenSiteInclusion (j i).left).obj
                  ((Scheme.proEtaleBaseChange (j i).left).obj V)) (B := V)
                (pullback.fst V.hom (j i).left) pullback.condition).op r) • φ F V x i) ∧
        (∀ (F : ∀ i, clopenModules (Xi i).left
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
            (V W : X.left.ProEt) (f : V ⟶ W) (x : (e.inverse.obj F).val.obj (op W)),
          φ F V ((e.inverse.obj F).val.map f.op x) =
            fun i ↦ (F i).val.map ((Scheme.proEtaleBaseChange (j i).left).map f).op
              (φ F W x i)) ∧
        (∀ (F G : ∀ i, clopenModules (Xi i).left
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
            (a : F ⟶ G) (V : X.left.ProEt) (x : (e.inverse.obj F).val.obj (op V)),
          φ G V ((e.inverse.map a).val.app (op V) x) =
            fun i ↦ (a i).val.app
              (op ((Scheme.proEtaleBaseChange (j i).left).obj V)) (φ F V x i)) := by
  sorry

/-- The degreewise restrictions induce the product of the unbounded derived categories,
with componentwise cohomology, tensor and the regular coefficient unit.
Source: Stacks 04TS, 015F, 06YS, 0G7D
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node steps 4--6. Restriction and insertion into one coordinate are exact.
Their identities descend through quasi-isomorphisms, so the product here is the
product of derived categories. Exact restriction commutes with cohomology. The
bilinear universal property identifies ordinary tensors and the coefficient unit.
K-flatness is detected componentwise by testing against insertions of acyclic
complexes. Descending the pure-tensor comparison on K-flat resolutions gives
the natural tensor isomorphism, with the normalized existing tensor models. -/
theorem finiteClopen_unbounded_decomposition (n : ℕ) (integral : Bool) :
    (Functor.pi' (fun i ↦
      clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral))).IsEquivalence ∧
    (∀ (i : I) (m : ℤ), Nonempty
      (clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral) ⋙
          DerivedCategory.homologyFunctor _ m ≅
        DerivedCategory.homologyFunctor _ m ⋙
          clopenRestriction (j i).left (P.clopenRing X.left n integral))) ∧
    (∀ i : I, Nonempty
      ((clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (P.clopenRing X.left n integral)))) ≅
        (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))))) ∧
    ∀ (M : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology X.left)
        (P.clopenRing X.left n integral)) (i : I)
      (Mi : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology (Xi i).left)
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
      Nonempty (M.closed.tensor ⋙
          clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral) ≅
        ((clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral)).prod
          (clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral))) ⋙
            Mi.closed.tensor) := by
  sorry

/-- Strict towers and their functorial Roos complexes restrict termwise.
Source: Stacks 08TC (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node step 7. Restriction keeps sectionwise countable products and their
projections, including the transition endomorphism 1-s. It therefore commutes
with its functorial shifted mapping cone on objects and strict maps. Exactness
of countable pro-etale products identifies these products with derived products.
Applying the exact restriction to any Roos triangle gives the component Roos
triangle, with its original maps; no canonical uniqueness of bare cones is used. -/
theorem finiteClopen_strict_roos (n : ℕ) (integral : Bool) (i : I) :
    Nonempty (integralOperationsRoosFunctor ⋙
        (clopenRestriction (j i).left (P.clopenRing X.left n integral)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((clopenRestriction (j i).left (P.clopenRing X.left n integral)).mapHomologicalComplex
            (ComplexShape.up ℤ)) ⋙ integralOperationsRoosFunctor) := by
  sorry

/-- Finite constructibility, fixed cohomological intervals and fixed Tor intervals
are detected on the components; hence both finite-coefficient subcategories split.
Source: blueprint section-invariant well-definedness, finite stage
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node step 8. Intersect a finite stratification with the clopen pieces;
conversely unite their finitely many stratifications. Cohomology is componentwise,
so every common interval works. Test Tor against inserted degree-zero modules and
use componentwise derived tensor. Lifting the restriction functors to these full
subcategories and restricting the gluing inverse gives the two equivalences.
No nonempty-index hypothesis is needed; ordered intervals also work for zero objects. -/
theorem finiteClopen_finite_bounds (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))) :
    (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left K ↔
      ∀ i, Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K)) ∧
    (∀ a b : ℤ, a ≤ b →
      (Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
        ∀ i, Scheme.proEtaleCohomologicalSupport
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) ⊆
            Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      (Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) K a b ↔
        ∀ i, Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) a b)) := by
  sorry

/-- Restriction on the finite constructible full subcategory, with its actual
ambient pullback on both objects and arrows. Source: blueprint finite-clopen argument
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenFiniteConstructiblePullback (n : ℕ) (i : I) :=
  (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left).lift
    ((Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left).ι ⋙
        finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
    (fun K ↦ ((P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n K.obj).1.mp
      K.property) i)

/-- The finite-Tor condition is detected on the finite list of components.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: use finiteClopen_finite_bounds for constructibility and Tor in a fixed interval.
For the converse take the minimum and maximum of the finitely many component bounds.
For no components take [0,0]; vanishing is detected by the empty covering sheaf axiom. -/
theorem finiteClopen_finiteTor_iff (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))) :
    finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.left K ↔
      ∀ i, finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) := by
  sorry

/-- The finite-Tor restriction is the full-subcategory lift of the recorded pullback.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenFiniteTorPullback (n : ℕ) (i : I) :=
  (finiteTorConstructible P.coefficients.l P.extension (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left).lift
    ((finiteTorConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left).ι ⋙
        finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
    (fun K ↦ (P.finiteClopen_finiteTor_iff X Xi j hdisjoint hcover n K.obj).mp K.property i)

/-- Both finite coefficient full-subcategory equivalences use these exact restrictions.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: restrict the ambient derived equivalence using the componentwise predicates.
The inverse gluing preserves them by the converse parts of the two bound statements. -/
theorem finiteClopen_finite_equivalences (n : ℕ) :
    (Functor.pi' (fun i ↦ P.clopenFiniteConstructiblePullback X Xi j
      hdisjoint hcover n i)).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenFiniteTorPullback X Xi j
      hdisjoint hcover n i)).IsEquivalence := by
  sorry

/-- Integral finite-Tor restriction, including detection of each common interval
uniformly over every finite reduction.
Source: blueprint finite-clopen argument, step 9
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: commute restriction with derived reduction and the strict Roos functor.
Completeness is the Roos triangle with its canonical reduction unit, hence is
componentwise. Apply finiteClopen_finite_bounds at every positive exponent; the
same a,b is retained, so these bounds are uniform in all reductions. A finite
union of the component intervals supplies common bounds for the inverse. -/
theorem finiteClopen_integral_bounds (K : sfIntegralConstructibleCategory
    P.coefficients.l P.extension X.left) :
    (finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K.obj ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((P.clopenIntegralPullback (j i)).obj K).obj) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
            K.obj) ⊆ Set.Icc a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) ⊆ Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
            K.obj) a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) a b)) := by
  sorry

/-- Lift the canonical constructible pullback to the integral finite-Tor category.
Source: blueprint finite-clopen argument, step 9
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralTorPullback (i : I) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X.left ⥤
      finiteTorConstructibleIntegralCategory P.coefficients.l P.extension (Xi i).left :=
  (finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left).lift
    ((finiteTorConstructibleIntegral P.coefficients.l P.extension X.left).ι ⋙
      integralDerivedPullback P.coefficients.l P.extension (j i).left)
    (fun K ↦ (P.finiteClopen_integral_bounds X Xi j hdisjoint hcover
      ⟨K.obj, K.property.1⟩).1.mp K.property i)

/-- Integral, rationalized, and common-stage constructible restriction equivalences.
The finite-Tor field categories are the very same categories by definition.
Source: blueprint section-invariant well-definedness, coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node steps 9--11. The exact module equivalence preserves every reduction
and the strict Roos construction. Completeness, constructible reductions, and
bounds uniform in the positive level are thus componentwise. Finiteness of I
provides one common interval, both for cohomology and Tor. Restrict the integral
equivalence. Rationalization has unchanged objects and tensors each Hom with E;
finite products commute with that tensor via coordinate insertion and summation.
At the algebraically closed stage choose the finite compositum of all component
fields, glue there, and represent arrows there. Equality is checked after a further
finite compositum, proving full faithfulness and essential surjectivity. The empty
family gives the zero category, equivalent to the empty product category. -/
theorem finiteClopen_constructible_equivalences :
    (Functor.pi' (fun i ↦ P.clopenIntegralPullback (j i))).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenIntegralTorPullback X Xi j
      hdisjoint hcover i)).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenRationalPullback (j i))).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenCommonStagePullback (j i))).IsEquivalence := by
  sorry

/-- Tensor and integral reduction are componentwise for the actual coefficient functors.
Source: Stacks 06YS, 0G7D, 08TC; blueprint coefficient transport
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: steps 5--6 and 9--11. Restriction carries sheaf tensor generators to the
same pure tensors. Descend on K-flat representatives to obtain the finite natural
comparison. For integral tensor and reduction, restrict the strict towers and
use the natural Roos comparison. Extend the resulting maps linearly to rational
Homs and then represent them at the common finite coefficient compositum.
All maps commute with identity and composite coefficient changes because the
pure-tensor formulas and the strict tower maps do. -/
theorem finiteClopen_tensor_and_reduction (i : I) :
    (∀ n : ℕ, Nonempty
      (finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).prod
          (finiteDerivedPullback P.coefficients.l P.extension n (j i).left)) ⋙
            finiteIntrinsicDerivedTensor P.coefficients.l P.extension (Xi i).left n)) ∧
    Nonempty (P.clopenIntegralTensor X ⋙ P.clopenIntegralPullback (j i) ≅
      ((P.clopenIntegralPullback (j i)).prod (P.clopenIntegralPullback (j i))) ⋙
        P.clopenIntegralTensor (Xi i)) ∧
    Nonempty (P.clopenRationalTensor X ⋙ P.clopenRationalPullback (j i) ≅
      ((P.clopenRationalPullback (j i)).prod (P.clopenRationalPullback (j i))) ⋙
        P.clopenRationalTensor (Xi i)) ∧
    Nonempty (P.clopenCommonStageTensor X ⋙ P.clopenCommonStagePullback (j i) ≅
      ((P.clopenCommonStagePullback (j i)).prod (P.clopenCommonStagePullback (j i))) ⋙
        P.clopenCommonStageTensor (Xi i)) ∧
    (∀ n : ℕ, Nonempty
      ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          scalarReductionDerivedExtension P.coefficients.l P.extension X.left n ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ⋙
          scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n)) ∧
    (∀ (m n : ℕ) (h : n ≤ m), Nonempty
      (coefficientFiniteQuotientDerived P.coefficients.l P.extension X.left h ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        finiteDerivedPullback P.coefficients.l P.extension m (j i).left ⋙
          coefficientFiniteQuotientDerived P.coefficients.l P.extension (Xi i).left h)) := by
  sorry

/-- Scalar extension commutes with the same restrictions, for arbitrary finite
coefficient extensions, including the identity map. Rationalization is compatible
with the integral restriction equivalence.
Source: blueprint coefficient transport, steps 6 and 9--11
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: on strict K-flat representatives the two scalar/restriction composites
have identical pure-tensor maps at every quotient of the target coefficient
ring, with the same transition equations. Restricting Roos gives the natural
integral comparison. The rational comparison is its linear extension, and common
stages compute these same comparisons after a finite compositum. -/
theorem finiteClopen_scalar_extension (i : I)
    (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L) :
    Nonempty
      ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          integralScalarExtension P.coefficients.l P.extension L ι X.left ⋙
          integralDerivedPullback P.coefficients.l L (j i).left ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ⋙
          integralScalarExtension P.coefficients.l P.extension L ι (Xi i).left) ∧
    Nonempty (P.clopenIntegralPullback (j i) ⋙
        sfRationalConstructibleLocalization P.coefficients.l P.extension (Xi i).left ≅
      sfRationalConstructibleLocalization P.coefficients.l P.extension X.left ⋙
        P.clopenRationalPullback (j i)) := by
  sorry

/-- Restriction preserves the specified coefficient units at every stage.
Source: blueprint coefficient transports, steps 5--6 and 9--11
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: the sheaf-level coefficient ring restricts to the component coefficient
ring, by localization of constant sheafification and sectionwise integral limits.
The regular modules therefore restrict to regular modules. The finite K-flat
and integral strict Roos formulas preserve this identification in degree zero.
Rationalization and the common-stage representative functors preserve these
isomorphisms, with no restriction on the chosen finite coefficient stage. -/
theorem finiteClopen_coefficient_units (i : I) :
    (∀ n : ℕ, Nonempty
      ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj
          (finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) ≅
        finiteConstantCoefficientObject P.coefficients.l P.extension (Xi i).left n)) ∧
    Nonempty ((P.clopenIntegralPullback (j i)).obj (P.clopenIntegralUnit X.left) ≅
      P.clopenIntegralUnit (Xi i).left) ∧
    Nonempty ((P.clopenRationalPullback (j i)).obj (P.clopenRationalUnit X.left) ≅
      P.clopenRationalUnit (Xi i).left) ∧
    ∀ B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar,
      Nonempty ((P.clopenCommonStagePullback (j i)).obj (P.clopenCommonStageUnit X.left B) ≅
        P.clopenCommonStageUnit (Xi i).left B) := by
  sorry

/-- The empty family forces the empty scheme and has the terminal product category.
Source: Stacks 04TS and the empty covering sheaf axiom
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: the union of the empty family of images is empty, so the covering condition
makes X empty. Functions on an empty index type and their coordinatewise morphisms
are unique. The preceding equivalences identify each source category with that
product; this includes zero sheaves and complexes, with no chosen nonzero component. -/
theorem finiteClopen_empty [IsEmpty I] (n : ℕ) (integral : Bool) :
    IsEmpty X.left ∧
      Subsingleton (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))) ∧
      ∀ F G : (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
        Subsingleton (F ⟶ G) := by
  sorry

/-- The finite derived restriction above is the recorded intrinsic inverse image,
after identifying its restricted constant coefficient sheaf with the component's.
The normalization on Q specifies termwise coefficient transport, including maps.
Source: Stacks 00XZ, 04TS, 015F
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: constant sheafification commutes with localization; its unit identifies
constant sections. Transport modules by the inverse ring isomorphism. The
underlying sectionwise restriction is the inverse image for an open immersion.
Its exact termwise descent is the recorded finiteDerivedPullback. -/
theorem finiteClopen_finite_restriction_identification (n : ℕ) (i : I) :
    ∃ (c : clopenRingRestriction (j i).left (P.clopenRing X.left n false) ≅
        integralCoefficientCommRingSheaf P.coefficients.l P.extension (Xi i).left n)
      (e : DerivedCategory (clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n false))) ≌
        Scheme.proEtaleDerivedCategory (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))),
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            c.inv)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty (clopenDerivedRestriction (j i).left (P.clopenRing X.left n false) ⋙
        e.functor ≅ finiteDerivedPullback P.coefficients.l P.extension n (j i).left) := by
  sorry

/-- The completed coefficient identification and its constructible comparison.
It relates the module-derived equivalence to the actual completed pullback;
completed pullback on arbitrary unbounded objects is not asserted to be an equivalence.
Source: Stacks 04TS; blueprint integral finite-clopen transport
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: restriction preserves sectionwise inverse limits, so the compatible finite
constant-ring identifications give the completed ring identification. Transport
scalars along its inverse. On complete objects the normalized Roos construction
computes the original restriction, with the original canonical reduction units.
This identifies the two restrictions naturally on the full integral subcategory. -/
theorem finiteClopen_integral_restriction_identification (i : I) :
    ∃ (c : clopenRingRestriction (j i).left (P.clopenRing X.left 0 true) ≅
        completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension (Xi i).left)
      (e : DerivedCategory (clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left 0 true))) ≌
        DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)),
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            c.inv)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          clopenDerivedRestriction (j i).left (P.clopenRing X.left 0 true) ⋙ e.functor ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι) := by
  sorry

end Decomposition
end PurityFiniteSetting
end WeilConjectures
