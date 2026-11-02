/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-! # Finite coefficient site transport for the intrinsic compact-support comparison

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.proof.md`, Charts
(blueprint: lem-sp-finite-ctf-site-coefficient-square).

The ambient functors and the coefficient arrow are the recorded intrinsic
`scalarExtensionFunctor`, `reductionCompactSupport`, and `reductionDirectImageComparison`.
Etale presentations use the existing ULift coefficient and sfIntrinsicDerivedEquivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- The finite site presentation used by this statement, built from the live comparison
functor and the canonical intrinsic realization.
Source: Stacks 099R and 00YV
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSite (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

/-- Identity-on-sections identification of the two ordinary direct images.
Source: Stacks 03D1, adjunction triangle identity
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfDirectImageIso (A : Type u) [CommRing A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    directImageConstantPush A p ≅ proEtaleConstantDerivedDirectImage p A :=
  Functor.rightDerivedFunctorNatIso
    (SheafOfModules.pushforwardCongr
      (congrArg (fun g : proEtaleConstantRing Y A ⟶
          (proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj
            (proEtaleConstantRing Z A) ↦
        (sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
        ((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
          |>.apply_symm_apply (proEtaleCoefficientDirectImageMap p A))))

-- Import the proved elementary helper by its private numerical name, as in
-- the library's other `import all` users; no source declaration is copied.

/-- Sectionwise identity between realization and coefficient restriction.
The data come from the existing unique linear lift of the identity of abelian sheaves.
Source: Stacks 00YV and 03DA, `realization_restrict_existsUnique`
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
@[no_expose] def finiteCtfRealizationRestriction {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicModuleEquivalence T B).functor ⋙
      proEtaleCoefficientRestrictScalars T φ ≅
      Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
          (sfIntrinsicModuleEquivalence T A).functor := by
  let φ' : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B :=
    RingHom.ulift.{u + 1, u + 1, u, u} φ
  let δ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ'))
  refine (finiteCtfRestrictionData (ProEt.topology T) _ _
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
    (ProEtale.finiteCoefficientIntrinsicScalarMap T B) φ' δ ?_).exists.choose
  exact (congrArg (fun q ↦ Functor.whiskerRight q
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (toSheafify_naturality (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ')))).symm

/-- Exact descent of the sectionwise restriction identity in intrinsic coordinates.
Source: Stacks 03D2 and 06YY
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteRestrictionIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    finiteCtfSite B T ⋙ scalarRestriction φ T ≅
      Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙ finiteCtfSite A T :=
  by
  let CA := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory
  let CB := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).mapDerivedCategory
  let EA := (sfIntrinsicDerivedEquivalence T A).functor
  let EB := (sfIntrinsicDerivedEquivalence T B).functor
  let Up := @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
    (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
    (RingHom.ulift.{u + 1, u + 1, u, u} φ)
  let Ue := Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology
    (RingHom.ulift.{u + 1, u + 1, u, u} φ)
  let eR : (sfIntrinsicModuleEquivalence T B).functor ⋙
      proEtaleCoefficientRestrictScalars T φ ≅
      Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
          (sfIntrinsicModuleEquivalence T A).functor :=
    finiteCtfRealizationRestriction φ T
  let e : EB ⋙ scalarRestriction φ T ≅ Up ⋙ EA :=
    (Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence T B).functor
      (proEtaleCoefficientRestrictScalars T φ)).symm ≪≫
      Functor.mapDerivedCategoryNatIso eR ≪≫
      Functor.mapDerivedCategoryCompIso
        (Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
          (RingHom.ulift.{u + 1, u + 1, u, u} φ))
        (sfIntrinsicModuleEquivalence T A).functor
  exact Functor.associator CB EB (scalarRestriction φ T) ≪≫
    Functor.isoWhiskerLeft CB e ≪≫
    (Functor.associator CB Up EA).symm ≪≫
    Functor.isoWhiskerRight
      (comparisonRestrictScalarsIso T (ULift.{u + 1, u} A)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)).symm EA ≪≫
    Functor.associator Ue CA EA

/-- The coefficient/site tensor map, defined as the mate of exact restriction.
Source: Stacks 07A4, 0G7E; the scalar specialization of the canonical ringed-topos
comparison (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteScalarMap {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    finiteCtfSite A T ⋙ scalarExtensionFunctor φ T ⟶
      Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙
        finiteCtfSite B T :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ))).symm
      (TwoSquare.mk _ _ _ _ (finiteCtfSiteRestrictionIso φ T).inv)).natTrans

/-- The canonical scalar specialization of the recorded tensor comparison is invertible.
Source: Stacks 07A4 and 0G7E; lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
`ringedTopoiCanonicalDerivedTensorComparison`
(blueprint: lem-sp-finite-ctf-site-coefficient-square).
Proof: specialize the recorded ringed-topos comparison to the etale/pro-etale
comparison and the constant B coefficient in degree zero. Use its pure-tensor
and ordinary-unit normalization, and the normalized scalar/tensor identifications.
On flat-term K-flat representatives this is the balanced scalar/site map. Taking
its restriction adjunct gives precisely the identity-on-sections square defining
finiteCtfSiteRestrictionIso. The scalar adjunction bijection therefore identifies
its map with finiteCtfSiteScalarMap. The recorded comparison is an isomorphism;
its canonical scalar specialization is thus invertible. No flatness of B is used. -/
theorem finiteCtfSiteScalarMap_isIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    IsIso (finiteCtfSiteScalarMap φ T) := by
  sorry

/-- The canonical tensor comparison in intrinsic finite-site coordinates.
Its map is the explicit restriction mate, not a chosen natural isomorphism.
Source: Stacks 07A4 (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteScalarIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    finiteCtfSite A T ⋙ scalarExtensionFunctor φ T ≅
      Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙
        finiteCtfSite B T :=
  haveI := finiteCtfSiteScalarMap_isIso φ T
  asIso (finiteCtfSiteScalarMap φ T)

/-- The compact-support presentation, formed from the live intrinsic extension-by-zero,
its normalized direct-image comparison, and the fixed proper/open comparison.
Source: Stacks 00YV, 03D1 and 07A5
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfCompactSupportFixedIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ reductionCompactSupport A j p ≅
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        j).mapDerivedCategory ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence X A).functor
      (Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero j A).mapDerivedCategory
        (finiteCtfDirectImageIso A p)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
            (ProEtale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
                (sfIntrinsicModuleEquivalence Z A).functor)) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        j).mapDerivedCategory (sfIntrinsicDerivedDirectImageComparison p A)

/-- The counit-normalized proper mate followed by exact open comparison,
transported through the canonical intrinsic realization.
Source: Stacks 09A6 and 09AF
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteCompactSupportIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    [IsProper p] :
    DerivedCategory.Plus.ι ⋙ finiteCtfSite A X ⋙ reductionCompactSupport A j p ≅
      DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⋙
            finiteCtfSite A Y := by
  let c : Compactification (j ≫ p) :=
    ⟨Z, p, j, rfl, inferInstance, inferInstance⟩
  exact
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (finiteCtfCompactSupportFixedIso A j p) ≪≫
        (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (fixedCompactSupportComparisonIso (ULift.{u + 1, u} A) c) _ ≪≫
    Functor.associator _ _ _

/-- The five-factor finite-site coefficient computation: inverse compact-support
comparison, tensor comparison at Y, etale coefficient mate, compact-support
comparison at B, and inverse tensor comparison at X.
Source: latest blueprint Charts; Stacks 07A4, 09A6 and 09AF
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteCoefficientTransport
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r]
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hLB : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L)) :
    (scalarExtensionFunctor φ Y).obj
        ((reductionCompactSupport A j r).obj ((finiteCtfSite A X).obj L)) ⟶
      (reductionCompactSupport B j r).obj
        ((scalarExtensionFunctor φ X).obj ((finiteCtfSite A X).obj L)) :=
  (scalarExtensionFunctor φ Y).map
      ((finiteCtfSiteCompactSupportIso A j r).hom.app ⟨L, hL⟩) ≫
    (finiteCtfSiteScalarIso φ Y).hom.app _ ≫
    (finiteCtfSite B Y).map
      ((Etale.compactScalarMap (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ r))).app L) ≫
    (finiteCtfSiteCompactSupportIso B j r).inv.app
      ⟨(Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L, hLB⟩ ≫
    (reductionCompactSupport B j r).map ((finiteCtfSiteScalarIso φ X).inv.app L)

/-- Finite-site computation agrees with the specified intrinsic pro-etale proper/open
coefficient map, for every etale presentation and naturally in the intrinsic input.
Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
`sk-lem-sp-reduction-exceptional.proof.md`, Charts
(blueprint: lem-sp-finite-ctf-site-coefficient-square).

Proof: (1) The finite-ctf site equivalence, followed by sfIntrinsicDerivedEquivalence,
gives etale presentations with ULift coefficients. The common Tor interval of L,
tested on the degree-zero B-module sheaf, bounds its scalar extension L_B. Thus
both displayed lower-bound witnesses exist, without flatness or finite projective
dimension of B. Exact open extension preserves their lower bounds. Properness
makes r qcqs. (2) The proper site comparison is the counit-normalized mate and is
invertible at these bounded-below inputs; the exact open comparison is invertible.
Their existing composite is finiteCtfSiteCompactSupportIso in the reverse direction.
Its realization factors are fixed by sfIntrinsicDerivedEquivalence and the uniquely
section-normalized direct-image comparison, so they introduce no arbitrary map.
(3) Express the inverse open site and scalar-balancing maps by their open-unit
adjuncts. (4) The normalized scalar/site/pullback cube identifies those adjuncts;
injectivity of the B-linear open adjunction gives the open square. (5) The proper
scalar/site mate equation applies at j_!L and its bounded-below scalar extension.
The intrinsic proper scalar map in reductionDirectImageComparison is exactly the
B-linear transpose of extension of the A-counit. The existing realization and site
comparisons preserve that counit normalization. (6) Paste the proper and open
squares. Naturality of the proper mate and open balancing gives T_Y(c_A), then
b(C_X L), then F_B(delta_X), equal to delta_Y, C_Y(beta), then c_B. (7) Invert only
c_A and delta_X and conjugate by the given eta. This yields the five-factor formula
for the actual reductionDirectImageComparison at M. All presentations equal this
same morphism, proving independence. Naturality of the actual ambient natural
transformation gives the final equation. Proof irrelevance removes any dependence
on the two lower-bound witnesses. -/
theorem finiteCtfSiteCoefficientSquare_statement
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ell)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (r : Z ⟶ Y) [IsProper r] [r.IsOver (Spec (.of k))] (_hf : j ≫ r = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    (M : proEtaleDerivedCategory X A) (_hM : spFiniteConstructibleTor X A M) :
    (∀ (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
      (_hctf : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X L)
      (η : (finiteCtfSite A X).obj L ≅ M),
      ∃ (hL : _root_.DerivedCategory.TStructure.t.plus L)
        (hLB : _root_.DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L)),
        IsIso ((finiteCtfSiteCompactSupportIso A j r).inv.app ⟨L, hL⟩) ∧
        IsIso ((finiteCtfSiteCompactSupportIso B j r).inv.app
          ⟨(Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L, hLB⟩) ∧
        (reductionDirectImageComparison φ j r).app M =
          (scalarExtensionFunctor φ Y).map ((reductionCompactSupport A j r).map η.inv) ≫
          finiteCtfSiteCoefficientTransport φ j r L hL hLB ≫
          (reductionCompactSupport B j r).map ((scalarExtensionFunctor φ X).map η.hom)) ∧
    ∀ (M' : proEtaleDerivedCategory X A) (_hM' : spFiniteConstructibleTor X A M')
      (g : M ⟶ M'),
      (scalarExtensionFunctor φ Y).map ((reductionCompactSupport A j r).map g) ≫
          (reductionDirectImageComparison φ j r).app M' =
        (reductionDirectImageComparison φ j r).app M ≫
          (reductionCompactSupport B j r).map ((scalarExtensionFunctor φ X).map g) := by
  sorry

end AlgebraicGeometry
