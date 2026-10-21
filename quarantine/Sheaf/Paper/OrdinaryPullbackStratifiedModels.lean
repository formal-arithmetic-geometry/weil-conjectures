/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.Paper.OrdinaryCompletedIntegralPullback
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.SfImmersionCompletedPullbackComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback

/-!
# Ordinary pullback of stratified perfect models

Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15; Stacks Project,
Tags 0D6D, 04IF, 06YQ and 06YY
(blueprint: lem-tw-ordinary-pullback-stratified-models).

All functors below are ordinary ringed pullback, before completion. The published
ordinary coefficient map and its total derived functor are reused verbatim.
The comparisons retain their ordinary generators and derived computation counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings

namespace WeilConjectures.OrdinaryStratifiedModels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical completed coefficient map in inverse-image form.
Source: the projection formula defining c_f in the statement; Stacks 06YY
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleSheafInverseImage f RingCat.{u + 1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      completedIntegralCoefficientSheafUnrestricted l E X :=
  ((proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _).symm
    (ordinaryIntegralDirectRingMap l E f)

/-- The inverse-image compositor, the mate of fibre-product associativity on direct image.
Source: Stacks 03CB (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def inverseComp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z) :
    proEtaleSheafInverseImage (h ≫ k) RingCat.{u + 1} ≅
      proEtaleSheafInverseImage k RingCat.{u + 1} ⋙
        proEtaleSheafInverseImage h RingCat.{u + 1} :=
  ((conjugateIsoEquiv
    (proEtaleSheafAdjunction (h ≫ k) RingCat.{u + 1})
    ((proEtaleSheafAdjunction k RingCat.{u + 1}).comp
      (proEtaleSheafAdjunction h RingCat.{u + 1}))).symm
    (Functor.sheafPushforwardContinuousComp'
      (eFG := (MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).symm)
      RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).symm).symm

/-- Completed coefficient composition and all its finite projections.
Source: Stacks 03CB, 0H7J and the inverse limit defining B
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: apply constant-coefficient-composition at R/t^(n+1). Substitute the defining
projection equations for c_h and c_k. Naturality of the inverse-image compositor
identifies the result with the finite projection of c_(h k). Limit projections are
jointly monic, proving the coefficient equality. This also proves the displayed
projection equations. Apply this to the two equal composites of the pullback square. -/
theorem coefficientMap_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z) :
    coefficientMap l E (h ≫ k) =
      (inverseComp h k).hom.app (completedIntegralCoefficientSheafUnrestricted l E Z) ≫
        (proEtaleSheafInverseImage h RingCat.{u + 1}).map (coefficientMap l E k) ≫
          coefficientMap l E h ∧
    ∀ n : ℕ, coefficientMap l E (h ≫ k) ≫
        limit.π (integralCoefficientSheafSystem l E X) (op n) =
      (proEtaleSheafInverseImage (h ≫ k) RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E Z) (op n)) ≫
        ((proEtaleSheafAdjunction (h ≫ k) RingCat.{u + 1}).homEquiv _ _).symm
          (ordinaryIntegralFiniteDirectRingMap l E (h ≫ k) n) := by
  sorry

/-- The existing constant-to-completion map, retaining commutativity.
Source: the constant quotient cone in completed coefficients
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def scalar (T : Scheme.{u}) :
    adicLisseConstantRing T (PbcIntegralRing l E) ⟶
      completedIntegralCommRingSheafUnrestricted l E T :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
    (integralConstantToCompletionOfUniverses l E T)

/-- B_T tensor_R N, using the existing constant-module and scalar-extension functors.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelModule (T : Scheme.{u}) :
    ModuleCat.{u + 1} (PbcIntegralRing l E) ⥤ integralTowerModules l E T :=
  adicLisseConstantModules T (PbcIntegralRing l E) ⋙ completedConstantExtension T (scalar l E T)

/-- Additivity of the existing constant-module realization and scalar extension.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: the constant presheaf, its additive sheafification and extension of scalars
are additive. Their composite therefore preserves addition on module morphisms. -/
@[instance] theorem modelModule_additive (T : Scheme.{u}) :
    (modelModule l E T).Additive := by
  sorry

/-- Termwise realization of a scalar complex; this uses ordinary sheaf tensor product.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelComplex (T : Scheme.{u}) :
    CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ ⥤
      CochainComplex (integralTowerModules l E T) ℤ :=
  completedConstantMapComplex (modelModule l E T) inferInstance

/-- The published scalar-extension witness has exactly the sheaf tensor objects.
Source: Stacks 03EK, 06YY (blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: this is the object specification in derived-change-of-rings, applied to
scalar; compose that specification with the constant-module functor. -/
theorem modelModule_obj (T : Scheme.{u}) (N : ModuleCat.{u + 1} (PbcIntegralRing l E)) :
    (modelModule l E T).obj N = SheafOfModules.changeOfRings (scalar l E T)
      ((adicLisseConstantModules T (PbcIntegralRing l E)).obj N) := by
  sorry

/-- The actual section b tensor x of the ordinary constant realization.
Source: Stacks 03EK; Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelSection (T : Scheme.{u}) (N : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (W : T.ProEtᵒᵖ) (b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj W)
    (x : N) : ((modelModule l E T).obj N).val.obj W :=
  (eqToHom (modelModule_obj l E T N).symm).val.app W
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (scalar l E T)
        ((adicLisseConstantModules T (PbcIntegralRing l E)).obj N)).presheaf).app W
      (b ⊗ₜ[(adicLisseConstantRing T (PbcIntegralRing l E)).obj.obj W,
        ((scalar l E T).hom.app W).hom]
          completedConstantGenerator T (PbcIntegralRing l E) N W x))

/-- The ordinary model comparison, uniquely normalized on constant generators.
Its naturality applies to every splitting and every idempotent matrix over R, so
it restricts to precisely the same finite-projective summand.
Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15; Stacks 03EK
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: on a finite free module send b tensor (a e_j) to b c_f(a) e_j, with
inverse b e_j mapped to b tensor e_j. The coefficient map preserves every constant
R-scalar at every finite projection, hence preserves the matrix of an idempotent.
Restrict both inverse maps to its image. More generally the same balanced-tensor
formula works for every scalar module, and commutes with every scalar linear map.
Sheafification gives the natural isomorphism. The adjunction-unit images generate
pullback locally, proving uniqueness from the displayed equation. -/
theorem modelPullback_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! γ : modelModule l E Y ⋙ ordinaryIntegralModulePull l E f ≅ modelModule l E X,
      ∀ (N : ModuleCat.{u + 1} (PbcIntegralRing l E)) (W : Y.ProEt) (x : N),
        ((γ.hom.app N).val.app (op ((proEtaleBaseChange f).obj W)))
          ((((ordinaryIntegralModuleAdjunction l E f).unit.app
              ((modelModule l E Y).obj N)).val.app (op W))
            (modelSection l E Y N (op W) 1 x)) =
          modelSection l E X N (op ((proEtaleBaseChange f).obj W)) 1 x := by
  sorry

/-- The uniquely generator-normalized ordinary model isomorphism.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (modelPullback_existsUnique l E f).exists.choose

/-- Its degreewise application, retaining the same scalar differential and idempotents.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelPullbackComplex {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modelComplex l E Y ⋙ ordinaryIntegralPullComplex l E f ≅ modelComplex l E X :=
  NatIso.mapHomologicalComplex (modelPullback l E f) (.up ℤ)

/-- The last local isomorphism is the ordinary computation counit followed by
localization of the normalized termwise model isomorphism, before completion.
Source: Stacks 06YQ, 06YY; Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: each finite projective term is a retract of finite free modules. Its
realization is consequently a retract of a finite free B-module and is flat.
Boundedness makes the realized complex K-flat by bounded-above-flat-kflat-site.
Ringed-topoi-derived-pullback makes its specified computation counit invertible.
The termwise comparison is invertible by modelPullback_existsUnique; localization
preserves that isomorphism. The composite has exactly the required normalization. -/
theorem perfectModelPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (_hfinite : ∀ q : ℤ, Module.Finite (PbcIntegralRing l E) (L.X q))
    (_hprojective : ∀ q : ℤ, Module.Projective (PbcIntegralRing l E) (L.X q))
    (_hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (L.X q)) :
    IsIso (ordinaryIntegralPullComplexCounit l E f ((modelComplex l E Y).obj L)) ∧
      IsIso (ordinaryIntegralPullComplexCounit l E f ((modelComplex l E Y).obj L) ≫
        DerivedCategory.Q.map ((modelPullbackComplex l E f).hom.app L)) := by
  sorry

/-- The actual fibre-product associativity comparison on the two covering slices.
Source: Stacks 03CB, 04IF (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def squareSite {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    proEtaleBaseChange i ⋙ proEtaleBaseChange (pullback.snd f i) ≅
      proEtaleBaseChange f ⋙ proEtaleBaseChange (pullback.fst f i) :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    (pullback.snd f i) i (fg := pullback.fst f i ≫ f)
    (hfg := pullback.condition)).symm ≪≫
  MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) (pullback.fst f i) f

/-- The canonical inverse-image generator 1 tensor x, given by the module adjunction unit.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def pullGenerator {X Y : Scheme.{u}} (f : X ⟶ Y) (M : integralTowerModules l E Y)
    (W : Y.ProEt) (x : M.val.obj (op W)) :
    ((ordinaryIntegralModulePull l E f).obj M).val.obj
      (op ((proEtaleBaseChange f).obj W)) :=
  (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op W)) x

/-- The ordinary square comparison is uniquely fixed on iterated inverse-image generators.
Source: Stacks 03CB, 03D2 and 0D6D
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: coefficientMap_comp identifies the structural maps of the two equal composites,
including all finite projections. Compose the ordinary tensor pullback comparisons.
On iterated generators both composites insert one twice, and squareSite gives the
canonical restriction between the iterated fibre products. Tensor relations and
sheafification give the isomorphism. These generators locally span the pullback
module, so their displayed values determine its components and the natural isomorphism. -/
theorem moduleSquare_existsUnique {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    ∃! γ : ordinaryIntegralModulePull l E i ⋙
          ordinaryIntegralModulePull l E (pullback.snd f i) ≅
        ordinaryIntegralModulePull l E f ⋙
          ordinaryIntegralModulePull l E (pullback.fst f i),
      ∀ (M : integralTowerModules l E Y) (W : Y.ProEt) (x : M.val.obj (op W)),
        ((γ.hom.app M).val.app
            (op ((proEtaleBaseChange (pullback.snd f i)).obj ((proEtaleBaseChange i).obj W))))
          (pullGenerator l E (pullback.snd f i) ((ordinaryIntegralModulePull l E i).obj M)
            ((proEtaleBaseChange i).obj W) (pullGenerator l E i M W x)) =
          (((ordinaryIntegralModulePull l E (pullback.fst f i)).obj
              ((ordinaryIntegralModulePull l E f).obj M)).val.map
            ((squareSite f i).hom.app W).op)
              (pullGenerator l E (pullback.fst f i) ((ordinaryIntegralModulePull l E f).obj M)
                ((proEtaleBaseChange f).obj W) (pullGenerator l E f M W x)) := by
  sorry

/-- The generator-normalized square comparison of ordinary module functors.
Source: Stacks 03D2, 0D6D (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def moduleSquare {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :=
  (moduleSquare_existsUnique l E f i).exists.choose

/-- Its termwise action on cochain complexes.
Source: Stacks 0D6D (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def complexSquare {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    ordinaryIntegralPullComplex l E i ⋙ ordinaryIntegralPullComplex l E (pullback.snd f i) ≅
      ordinaryIntegralPullComplex l E f ⋙ ordinaryIntegralPullComplex l E (pullback.fst f i) :=
  NatIso.mapHomologicalComplex (moduleSquare l E f i) (.up ℤ)

/-- The ordinary derived square comparison retains its computation-counit equation.
Source: Stacks 0D6D and 06YY
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: choose a flat-term K-flat resolution. Ordinary ringed pullback preserves this
class. Apply the two ordinary derived composition comparisons and the two-isomorphism
transport for the equal composites, using moduleSquare for their termwise comparison.
The normalized comparison on representatives gives the displayed counit equation.
Descent gives it for arbitrary complexes. On good resolutions all computation maps
are invertible; every derived object has such a resolution. This proves uniqueness. -/
theorem derivedSquare_existsUnique {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    ∃! β : ordinaryIntegralDerivedPull l E f ⋙
          ordinaryIntegralDerivedPull l E (pullback.fst f i) ≅
        ordinaryIntegralDerivedPull l E i ⋙
          ordinaryIntegralDerivedPull l E (pullback.snd f i),
      ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        β.hom.app (DerivedCategory.Q.obj P) ≫
            (ordinaryIntegralDerivedPull l E (pullback.snd f i)).map
              (ordinaryIntegralPullComplexCounit l E i P) ≫
            ordinaryIntegralPullComplexCounit l E (pullback.snd f i)
              ((ordinaryIntegralPullComplex l E i).obj P) ≫
            DerivedCategory.Q.map ((complexSquare l E f i).hom.app P) =
          (ordinaryIntegralDerivedPull l E (pullback.fst f i)).map
              (ordinaryIntegralPullComplexCounit l E f P) ≫
            ordinaryIntegralPullComplexCounit l E (pullback.fst f i)
              ((ordinaryIntegralPullComplex l E f).obj P) := by
  sorry

/-- The unique ordinary derived square comparison with this representative normalization.
Source: Stacks 0D6D (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def derivedSquare {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :=
  (derivedSquare_existsUnique l E f i).exists.choose

/-- For immersions ordinary pullback is exact restriction, with its ordinary counit.
Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: immersion-completed-pullback-comparison identifies the projection-defined
coefficient map with the canonical immersion coefficient isomorphism. Its ordinary
module functor is exact inverse image. Thus every complex computes the left derived
functor; the ordinary computation counit is invertible without completeness. -/
theorem immersionExact {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i] :
    PreservesFiniteLimits (ordinaryIntegralModulePull l E i) ∧
      PreservesFiniteColimits (ordinaryIntegralModulePull l E i) ∧
      ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        IsIso (ordinaryIntegralPullComplexCounit l E i P) := by
  sorry

/-- Restriction to a pro-etale covering object is exact ordinary pullback.
This identifies the site-of-U notation used below with the corresponding slice
restriction, retaining the same ordinary computation counit.
Source: Stacks 04IF and proetale localization; Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: weakly-etale-localization identifies the small site of U with the slice.
Constant rings restrict by the identity on constant sections. Limits on the slice
are sectionwise, so the completed ring and every finite projection restrict to
those on U. The projection-defined ring map is therefore this identification.
Module restriction is exact, and exact termwise restriction computes its derived
functor on every complex; its ordinary computation counit is invertible. -/
theorem weaklyEtaleExact {X Y : Scheme.{u}} (i : X ⟶ Y) [WeaklyEtale i] :
    PreservesFiniteLimits (ordinaryIntegralModulePull l E i) ∧
      PreservesFiniteColimits (ordinaryIntegralModulePull l E i) ∧
      ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        IsIso (ordinaryIntegralPullComplexCounit l E i P) := by
  sorry

/-- The canonical local composition and covering-slice restriction comparison.
The covering object U is a weakly etale scheme over the stratum S; its pullback
is literally the chart V = (X times_Y S) times_S U.
Source: Stacks 0D6D, 04IF; Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def localExchange {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y)
    (U : S.ProEt) (K : DerivedCategory (integralTowerModules l E Y)) :
    (ordinaryIntegralDerivedPull l E
        (pullback.fst (pullback.snd f i) U.hom)).obj
      ((ordinaryIntegralDerivedPull l E (pullback.fst f i)).obj
        ((ordinaryIntegralDerivedPull l E f).obj K)) ≅
    (ordinaryIntegralDerivedPull l E
        (pullback.snd (pullback.snd f i) U.hom)).obj
      ((ordinaryIntegralDerivedPull l E U.hom).obj
        ((ordinaryIntegralDerivedPull l E i).obj K)) :=
  (ordinaryIntegralDerivedPull l E (pullback.fst (pullback.snd f i) U.hom)).mapIso
      ((derivedSquare l E f i).app K) ≪≫
    (derivedSquare l E (pullback.snd f i) U.hom).app
      ((ordinaryIntegralDerivedPull l E i).obj K)

/-- The specified local-model map: composition and slice comparisons, the given
chart isomorphism, the ordinary K-flat counit, and the termwise tensor comparison.
Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def localComparison {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y)
    (U : S.ProEt) (K : DerivedCategory (integralTowerModules l E Y))
    (L : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (e : (ordinaryIntegralDerivedPull l E U.hom).obj
          ((ordinaryIntegralDerivedPull l E i).obj K) ≅
        DerivedCategory.Q.obj ((modelComplex l E U.left).obj L)) :
    (ordinaryIntegralDerivedPull l E
        (pullback.fst (pullback.snd f i) U.hom)).obj
      ((ordinaryIntegralDerivedPull l E (pullback.fst f i)).obj
        ((ordinaryIntegralDerivedPull l E f).obj K)) ⟶
      DerivedCategory.Q.obj
        ((modelComplex l E (pullback (pullback.snd f i) U.hom)).obj L) :=
  (localExchange l E f i U K).hom ≫
    (ordinaryIntegralDerivedPull l E (pullback.snd (pullback.snd f i) U.hom)).map e.hom ≫
    ordinaryIntegralPullComplexCounit l E (pullback.snd (pullback.snd f i) U.hom)
      ((modelComplex l E U.left).obj L) ≫
    DerivedCategory.Q.map
      ((modelPullbackComplex l E (pullback.snd (pullback.snd f i) U.hom)).hom.app L)

/-- Ordinary pullback transports the given stratification, covers and perfect local
models. The index bijection deletes exactly the empty base-changed strata. The
map asserted invertible is localComparison, with its prescribed basis/idempotent
and ordinary computation-counit normalization, rather than a comparison after completion.

Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-tw-ordinary-pullback-stratified-models).

Proof (the eight steps of the DAG):
1. Base change the finite locally closed stratification. Constructible-preimage
makes its images constructible; the ranges are disjoint and cover X. Delete
empty images and enumerate the remaining finite index set. Weakly etale and
fpqc base change preserve the given covering families.
2. Constant-coefficient-composition at every finite R/t^(n+1), followed by the
limit universal property, gives coefficientMap_comp for both equal composites.
3. Weakly-etale-localization identifies the pro-etale slice at U with the site
of its underlying scheme, and similarly for V. Constant rings and their limit
projections agree there. Localize-ringed-site-morphism identifies the restricted
structural map with the projection-defined map for v.
4. Ringed-derived-monoidal-comparisons gives the two ordinary composition
isomorphisms and their two-isomorphism transport. Immersion-completed-pullback-
comparison is used only for unconditional exact immersion restriction. This
is derivedSquare, with the displayed ordinary counit equation.
5. The ordinary unbounded sheaf-slice comparison, pro-etale subcanonicity and
site-representable-algebraic-pullback identify the pulled representable h_U with
h_V. Localizing the comparison gives localExchange; apply P_v to the given e.
6. Split each finite projective scalar term off finite free R-modules. Tensoring
its realization with an exact sequence is a split summand of a finite direct
sum of that sequence, hence exact: the terms are flat B-modules.
7. The realized bounded flat complex is K-flat by bounded-above-flat-kflat-site.
Ringed-topoi-derived-pullback makes the ordinary computation counit invertible.
8. On free bases the termwise balanced-tensor map sends b tensor (a e_j) to
b c_v(a) e_j; its inverse inserts one. Constant scalar preservation makes this
commute with the same idempotent and every differential, yielding modelPullback.
Its localization, composed with the counit and localExchange, is precisely the
map in the conclusion. No flatness of c_f or completeness of P_f K is used. -/
theorem ordinaryPullbackStratifiedModels
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (K : DerivedCategory (integralTowerModules l E Y))
    (s : FiniteLocallyClosedStratification Y)
    (_hs : ∀ i : Fin s.n, Topology.IsConstructible (s.stratum i))
    (A : Fin s.n → Type v) (U : ∀ i : Fin s.n, A i → (s.domain i).ProEt)
    (_hcover : ∀ i : Fin s.n,
      Sieve.generate (Presieve.ofArrows (U i) (fun a ↦ terminal.from (U i a))) ∈
        ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt))
    (L : ∀ (i : Fin s.n) (a : A i),
      CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (_hfinite : ∀ (i : Fin s.n) (a : A i) (q : ℤ),
      Module.Finite (PbcIntegralRing l E) ((L i a).X q))
    (_hprojective : ∀ (i : Fin s.n) (a : A i) (q : ℤ),
      Module.Projective (PbcIntegralRing l E) ((L i a).X q))
    (_hbounded : ∀ (i : Fin s.n) (a : A i),
      ∃ b c : ℤ, ∀ q : ℤ, q < b ∨ c < q → IsZero ((L i a).X q))
    (e : ∀ (i : Fin s.n) (a : A i),
      (ordinaryIntegralDerivedPull l E (U i a).hom).obj
          ((ordinaryIntegralDerivedPull l E (s.immersion i)).obj K) ≅
        DerivedCategory.Q.obj ((modelComplex l E (U i a).left).obj (L i a))) :
    (∃ sX : FiniteLocallyClosedStratification X,
      ∃ b : Fin sX.n ≃ {i : Fin s.n // Nonempty (pullback f (s.immersion i) : Scheme.{u})},
        (∀ k : Fin sX.n, Topology.IsConstructible (sX.stratum k)) ∧
        (∀ k : Fin sX.n, sX.stratum k = f.base ⁻¹' s.stratum (b k).val) ∧
        ∀ k : Fin sX.n,
          ∃ α : sX.domain k ≅ pullback f (s.immersion (b k).val),
            α.hom ≫ pullback.fst f (s.immersion (b k).val) = sX.immersion k) ∧
      ∀ i : Fin s.n, Nonempty (pullback f (s.immersion i) : Scheme.{u}) →
        (Sieve.generate (Presieve.ofArrows
          (fun a : A i ↦ (proEtaleBaseChange (pullback.snd f (s.immersion i))).obj (U i a))
          (fun a : A i ↦ terminal.from
            ((proEtaleBaseChange (pullback.snd f (s.immersion i))).obj (U i a)))) ∈
          ProEt.topology (pullback f (s.immersion i)) (⊤_ (pullback f (s.immersion i)).ProEt)) ∧
        ∀ a : A i, IsIso (localComparison l E f (s.immersion i) (U i a) K (L i a) (e i a)) := by
  sorry

end WeilConjectures.OrdinaryStratifiedModels
