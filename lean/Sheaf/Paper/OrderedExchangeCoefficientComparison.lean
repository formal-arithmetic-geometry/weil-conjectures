/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-! # Coefficient normalization of the raw ordered completed exchange

Source: main-20261015 blueprint, proper base change, completed-exchange-coherence,
second proof paragraph; strict coefficient supplement, Stacks Tags 099M, 099N,
0A07 and 0E48 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).

The maps below retain their ordinary-section, universal-derived-counit and completion-unit
normalizations. The ambient constant and completed module categories remain distinct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

-- Prefer the concrete pro-etale site and module instances to abstract corner projections.
attribute [local instance 0] SheafOfModules.RingedTensorCorner.category
  SheafOfModules.RingedTensorCorner.derived

private theorem orderedAbSheafify (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private theorem orderedAbLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T


private theorem orderedRestrictLimits (T : Scheme.{t})
    {R B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ B) :
    PreservesLimitsOfShape ℕᵒᵖ (reductionRestrict T φ) := by
  let := orderedAbSheafify T
  let := orderedAbLocallyBijective T
  let r := reductionRestrict T φ
  let F := SheafOfModules.forget.{t + 1} (reductionModuleRing T R) ⋙
    PresheafOfModules.toPresheaf (reductionModuleRing T R).obj
  have : PreservesLimitsOfShape ℕᵒᵖ (r ⋙ F) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (SheafOfModules.forget.{t + 1} (reductionModuleRing T B) ⋙
        PresheafOfModules.toPresheaf (reductionModuleRing T B).obj))
  have : ReflectsLimitsOfShape ℕᵒᵖ F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves r F

set_option backward.isDefEq.respectTransparency.types true in
private theorem uniqueLimitComparison {C E : Type*} [Category C] [Category E]
    [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ E]
    (r : C ⥤ E) [PreservesLimitsOfShape ℕᵒᵖ r] :
    ∃! e : lim ⋙ r ≅ (Functor.whiskeringRight ℕᵒᵖ C E).obj r ⋙ lim,
      ∀ (Z : ℕᵒᵖ ⥤ C) (n : ℕ),
        e.hom.app Z ≫ limit.π (Z ⋙ r) (op n) = r.map (limit.π Z (op n)) := by
  refine ⟨preservesLimitNatIso (J := ℕᵒᵖ) r, ?_, ?_⟩
  · intro Z n
    exact preservesLimitIso_hom_π r Z (op n)
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    apply limit.hom_ext
    intro n
    exact (he Z n.unop).trans (preservesLimitIso_hom_π r Z n).symm

private theorem unitIsoComparison {C : Type*} [Category C] {M N M' N' : C}
    (j : M ⟶ N) (j' : M' ⟶ N') (a : M ≅ M') (p : N ≅ N')
    (h : j ≫ p.hom = a.hom ≫ j') : j' ≫ p.inv = a.inv ≫ j :=
  a.eq_inv_comp.mpr
    ((Category.assoc a.hom j' p.inv).symm.trans (p.comp_inv_eq.mpr h.symm))

private theorem mappedUnitIsoComparison {C E : Type*} [Category C] [Category E]
    (r : C ⥤ E) {M N Z : C} {M' N' : E}
    (j : M ⟶ N) (j' : M' ⟶ N') (a : r.obj M ≅ M') (p : r.obj N ≅ N')
    (h : r.map j ≫ p.hom = a.hom ≫ j') (f : N ⟶ Z) :
    j' ≫ p.inv ≫ r.map f = a.inv ≫ r.map (j ≫ f) := by
  rw [← Category.assoc, unitIsoComparison _ _ a p h,
    Category.assoc, Functor.map_comp]

attribute [local irreducible] completedAdicChangeData completedAdicDerivedChange
  HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  completedAdicChange reductionChange reductionDerivedChange reductionHomotopy
  completedReductionTower reduction

attribute [local instance 3000] orderedAbSheafify orderedAbLocallyBijective
  reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
  reductionRingModulesHasDerivedCategory

-- Normalize the two ordinary presentations of scalar restriction before matching complexes.
set_option allowUnsafeReducibility true in
attribute [local reducible] reductionRestrict completedReductionComplexTowerFunctor

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Derived restriction along the existing compatible-residue coefficient map.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
abbrev res (T : Scheme.{t}) := reductionDerivedRestrict T (exchangeScalar d T)

/-- The canonical balancing isomorphism on the single ordinary strict quotient diagram.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: flatness of the completed ring over the constant ring identifies its finite
quotients with the specified finite constant sheaves. On pure tensors the comparison
sends s tensor x to s tensor x. Balancing and sheafification make this an isomorphism,
natural in modules and quotient coefficients. The section formulas specify it uniquely
and ensure compatibility with all quotient transitions, including identity transitions. -/
theorem ordinaryRho_existsUnique (T : Scheme.{t}) :
    ∃! e : reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
        completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T,
      ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
        ((e.hom.app M).app (op n)).val.app U
            (reductionTensorSection T (quotient d T n)
              ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
          reductionTensorSection T (d.projection T n) M U s x := by
  sorry

/-- Ordinary strict balancing, with its prescribed tensor normalization.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def ordinaryRho (T : Scheme.{t}) :
    reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
      completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T :=
  (ordinaryRho_existsUnique d T).exists.choose

attribute [local irreducible] ordinaryRho reductionModule completedReductionModuleTowerFunctor
  completedReductionCoefficient constantSheaf AdicCoefficients.coefficientRing
  SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex-level normalization of the specified rho comparison.
Source: Stacks 099M, 06YY
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def RhoNormalization (T : Scheme.{t})
    (e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T) : Prop :=
  ∀ P : CochainComplex (reductionModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing T) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d T).map
              ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit d T
              (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
            (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
              ((completedReductionComplexTowerFunctor T d).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P)

attribute [local irreducible] RhoNormalization

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived strict-tower comparison is fixed on K-flat representatives before evaluation.
Source: Stacks 099M, 06YY
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: flatness makes restriction preserve flat-term K-flat representatives. Apply
ordinaryRho to one such representative and conjugate by the two universal reduction
counits and exact-restriction factorization maps. The formula descends through resolving
quasi-isomorphisms, giving the isomorphism. Every derived object has a representative
of this kind, so the formula determines the natural isomorphism uniquely. -/
theorem rho_existsUnique (T : Scheme.{t}) :
    ∃! e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T,
      RhoNormalization d T e := by
  sorry

/-- The specified comparison rho, natural on all ambient inputs.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def rho (T : Scheme.{t}) :
    completedReductionTower T d ⋙ exchangeTowerRes d T ≅ res d T ⋙ reduction d T :=
  (rho_existsUnique d T).exists.choose

/-- The chosen rho retains its complex-level normalization.
Source: Stacks 099M, 06YY
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: use the existence clause of the unique normalized comparison. -/
theorem rho_normalization (T : Scheme.{t}) : RhoNormalization d T (rho d T) :=
  (rho_existsUnique d T).exists.choose_spec

/-- The actual ordinary limit/scalar comparison, fixed by all its projections.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: restriction leaves the underlying additive sheaf unchanged. Its right-adjoint
limit comparison is the identity on compatible families. Every projection commutes
with it, giving its inverse and uniqueness by the limit universal property. -/
theorem ordinaryLambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedTowerLimit T (d.completedRing T) ⋙
          reductionRestrict T (exchangeScalar d T) ≅
        exchangeTowerModuleRes d T ⋙ completedTowerLimit T (exchangeConstantRing T A),
      ∀ (Z : d.towers T) (n : ℕ),
        e.hom.app Z ≫ limit.π ((exchangeTowerModuleRes d T).obj Z) (op n) =
          (reductionRestrict T (exchangeScalar d T)).map (limit.π Z (op n)) := by
  let := orderedAbSheafify T
  let := orderedAbLocallyBijective T
  have := orderedRestrictLimits T (exchangeScalar d T)
  exact uniqueLimitComparison (reductionRestrict T (exchangeScalar d T))

/-- The identity on compatible families, with its projection equations retained.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def ordinaryLambda (T : Scheme.{t}) :
    completedTowerLimit T (d.completedRing T) ⋙ reductionRestrict T (exchangeScalar d T) ≅
      exchangeTowerModuleRes d T ⋙ completedTowerLimit T (exchangeConstantRing T A) :=
  (ordinaryLambda_existsUnique d T).exists.choose

attribute [local irreducible] ordinaryLambda Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit

/-- The universal right-derived limit unit at a cochain complex.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def limitComplexUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :
    DerivedCategory.Q.obj
        (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (completedRlim T R).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
    (completedTowerLimit T R).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    (completedRlim T R).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

attribute [local irreducible] limitComplexUnit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex-level normalization of the specified lambda comparison.
Source: Stacks 0A07
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def LambdaNormalization (T : Scheme.{t})
    (e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T) : Prop :=
  ∀ P : CochainComplex (d.towers T) ℤ,
        (res d T).map (limitComplexUnit T (d.completedRing T) P) ≫
            e.hom.app (DerivedCategory.Q.obj P) ≫
            (rlim (A := A) T).map
              ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P) =
          (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app
              (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryLambda d T) (.up ℤ)).hom.app P) ≫
            limitComplexUnit T (exchangeConstantRing T A)
              (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj P)

attribute [local irreducible] LambdaNormalization

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Restriction commutes with derived strict limit on arbitrary towers, with the
K-injective comparison fixed by its ordinary compatible-family map and universal units.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: flat scalar extension is an exact left adjoint to restriction. Termwise
restriction therefore preserves K-injectives on the small diagram site. On a
K-injective tower, apply ordinaryLambda and the invertible derived units. This
defines a natural isomorphism. Universality extends its equation to every complex;
K-injective resolutions prove uniqueness. No finite-reduction condition is used. -/
theorem lambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T,
      LambdaNormalization d T e := by
  sorry

/-- The canonical restriction/derived-limit comparison on actual strict towers.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def lambda (T : Scheme.{t}) :
    completedRlim T (d.completedRing T) ⋙ res d T ≅ exchangeTowerRes d T ⋙ rlim (A := A) T :=
  (lambda_existsUnique d T).exists.choose

/-- The chosen lambda retains its complex-level normalization.
Source: Stacks 0A07
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: use the existence clause of the unique normalized comparison. -/
theorem lambda_normalization (T : Scheme.{t}) : LambdaNormalization d T (lambda d T) :=
  (lambda_existsUnique d T).exists.choose_spec

variable {U V : Scheme.{t}} (u : U ⟶ V)

/-- The ambient direct-image/scalar comparison, with its universal unit normalization.
Source: Stacks 0E48 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def chi : d.push u ⋙ res d V ≅ res d U ⋙ push (A := A) u :=
  proEtaleRingRestrictionDerivedDirectImage u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)

/-- The ambient pullback/scalar comparison is exact descent of the ordinary normalized mate.
Source: Stacks 0D6D (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def alpha : d.pull u ⋙ res d U ≅ res d V ⋙ pull (A := A) u :=
  proEtaleRingRestrictionDerivedPullback u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)

/-- The quotient-tower complete category over completed coefficients.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
abbrev AComplete (T : Scheme.{t}) := ObjectProperty.FullSubcategory (d.TowerComplete T)

/-- The inclusion of the full completed-coefficient complete category.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
abbrev inclusion (T : Scheme.{t}) := ObjectProperty.ι (d.TowerComplete T)

/-- Restriction identifies the two complete predicates and is an equivalence on the full
complete categories; it does not assert an ambient equivalence.
Source: Stacks 099M, 099I
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: on the small site apply the flat ringed-ideal complete equivalence. Its finite
reduction comparison identifies the strict quotient diagrams by rho. The specified
limit comparison lambda respects quotient units. The Koszul reconstruction identifies
unit-invertibility with local derived completeness on both sides. Consequently the
ambient restriction functor, restricted to these full subcategories, is an equivalence. -/
theorem restriction_complete (T : Scheme.{t}) :
    (∀ K : d.derived T, d.TowerComplete T K ↔ IsComplete d T ((res d T).obj K)) ∧
      ∃ e : AComplete d T ≌ Complete d T,
        Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete d T) ≅
          inclusion d T ⋙ res d T) := by
  sorry

/-- The scalar comparison for completed pullback is fixed by the actual completion units.
Source: Stacks 099M, 099N
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: completed pullback is the reflection of ordinary pullback. Restriction identifies
the complete categories and their units by rho and lambda. The ordinary comparison
alpha therefore extends uniquely across the completed pullback unit. The two hom-set
bijections give inverse extensions, so this is an isomorphism. Naturality and uniqueness
hold on the full complete category, not only on constructible or bounded objects. -/
theorem phi_existsUnique :
    ∃! e : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
        inclusion d V ⋙ res d V ⋙ completePull d u,
      ∀ K : AComplete d V,
        (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e.hom.app K =
          (alpha d u).hom.app K.obj ≫
            (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj)) := by
  sorry

/-- The completed pullback/scalar isomorphism, retaining its completion-unit equation.
Source: Stacks 099N (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def phi : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
    inclusion d V ⋙ res d V ⋙ completePull d u := (phi_existsUnique d u).exists.choose


variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The specified completed-coefficient source reconstruction.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def sourceReconstruction (K : d.derived X) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    ((d.reductionTowerPullbackIso g).app ((d.push f).obj K))

/-- The source comparison s a is exactly the ordered projection-formula comparison.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def sourceA (K : d.derived X) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    (d.towerH (f := f) (f' := f') (g := g) (g' := g') K)

/-- The specified direct-image/limit comparison c a.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def targetA (K : d.derived X) :=
  (d.directImageRlimIso f').app
    ((d.towerPull g').obj ((completedReductionTower X d).obj K))

/-- The left corner comparison includes the image of the same strict reduction rho.
Source: Stacks 0E48 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def beta (K : d.derived X) :=
  (exchangeCornerB d f g).app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPull (A := A) g).mapIso
      ((exchangeConstantPush (A := A) f).mapIso ((rho d X).app K))

/-- The right corner comparison includes the image of that same strict reduction rho.
Source: Stacks 0E48 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def delta (K : d.derived X) :=
  (exchangeCornerD d g' f').app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPush (A := A) f').mapIso
      ((exchangeConstantPull (A := A) g').mapIso ((rho d X).app K))

/-- The scalar comparison at M uses finite reduction, ordinary pullback and chi f.
Source: Stacks 099M, 0E48
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def rhoM (K : d.derived X) :=
  (rho d Y').app ((d.pull g).obj ((d.push f).obj K)) ≪≫
    (reduction d Y').mapIso ((alpha d g).app ((d.push f).obj K)) ≪≫
    (reduction d Y').mapIso ((pull (A := A) g).mapIso ((chi d f).app K))

/-- The pulled-back strict reduction comparison retains its full diagram, not just levels.
Source: Stacks 099M, 0E48
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def rhoPull (K : d.derived X) :=
  (exchangeResPull d g').app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPull (A := A) g').mapIso ((rho d X).app K)

/-- The source scalar identification, with phi evaluated at the complete direct image.
Source: Stacks 099N (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def iotaS (K : d.derived X) (hK : d.TowerComplete X K) :=
  (phi d g).app ⟨(d.push f).obj K, d.push_complete f K hK⟩ ≪≫
    (completePull d g).mapIso ((chi d f).app K)

/-- The target scalar identification is chi followed by direct image of phi.
Source: Stacks 099N (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def iotaT (K : d.derived X) (hK : d.TowerComplete X K) :=
  (chi d f').app ((d.completedPull g').obj K) ≪≫
    (push (A := A) f').mapIso ((phi d g').app ⟨K, hK⟩)


/-- Ordinary scalar restriction commutes with constant diagrams by identity components.
Source: Stacks 0E48 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def ordinaryScalarDiagonal (T : Scheme.{t}) :
    d.constantTower T ⋙ exchangeTowerModuleRes d T ≅
      reductionRestrict T (exchangeScalar d T) ⋙ (Functor.const ℕᵒᵖ) :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp))
    (fun _ ↦ by ext n; simp)

/-- Exact descent of the identity scalar/diagonal comparison.
Source: Stacks 0E48 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def scalarDiagonal (T : Scheme.{t}) :
    d.derivedConstantTower T ⋙ exchangeTowerRes d T ≅ res d T ⋙ diagonal (A := A) T :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryScalarDiagonal d T) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Restriction respects the strict quotient unit, not just its evaluations.
Source: Stacks 099M (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: on an ordinary flat-term K-flat model both augmentations send x to 1 tensor x
in the same strict quotient diagram. ordinaryRho preserves this formula. Descent by
the universal counits gives the first equality before derived limit. Apply lambda,
its diagonal normalization and the diagonal adjunction unit to obtain the second. -/
theorem rho_unit (T : Scheme.{t}) (K : d.derived T) :
    (exchangeTowerRes d T).map ((completedReductionAugmentation d T).app K) ≫
        (rho d T).hom.app K =
      (scalarDiagonal d T).hom.app K ≫ (augmentation d T).app ((res d T).obj K) ∧
    (res d T).map (d.completionUnit T K) ≫
        (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
        (rlim (A := A) T).map ((rho d T).hom.app K) =
      (unit d T).app ((res d T).obj K) := by
  sorry

/-- The completed Hom bijections agree under chi and phi; hence so do their units,
counits and all adjunction conjugates of direct-image identity and composition.
Source: Stacks 099N, 07A6
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: the ordinary restricted adjunction has the normalized transpose formula of
proEtaleRingSheafChangeAdjunction. Precompose with the completed pullback unit.
The defining phi equation identifies this with precomposition by the constant
completion unit. On complete targets both unit precompositions are bijective by
reflection. This proves equality of the completed Hom bijections, fixing both units
and counits. Adjunction conjugation is a bijection computed from those units and
counits. Therefore the direct-image identity and composition conjugates agree too. -/
theorem completedHom_normalization {U V : Scheme.{t}} (u : U ⟶ V)
    (K : d.derived V) (hK : d.TowerComplete V K)
    (L : d.derived U) (_hL : d.TowerComplete U L)
    (a : (d.completedPull u).obj K ⟶ L) :
    (proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)).homEquiv _ _
      ((unit d U).app ((pull (A := A) u).obj ((res d V).obj K)) ≫
        (phi d u).inv.app ⟨K, hK⟩ ≫ (res d U).map a) =
      (res d V).map ((proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
        (d.integralRingIso u)).homEquiv _ _ (d.ordinaryToCompleted u K ≫ a)) ≫
        (chi d u).hom.app L := by
  have hphi := (phi_existsUnique d u).exists.choose_spec (⟨K, hK⟩ : AComplete d V)
  change (res d U).map (d.ordinaryToCompleted u K) ≫
    (phi d u).hom.app ⟨K, hK⟩ = (alpha d u).hom.app K ≫
      (unit d U).app ((pull (A := A) u).obj ((res d V).obj K)) at hphi
  have heq := mappedUnitIsoComparison (res d U) (d.ordinaryToCompleted u K) _
    ((alpha d u).app K) ((phi d u).app ⟨K, hK⟩) hphi a
  exact (congrArg
    ((proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso u A)).homEquiv _ _) heq).trans
    ((proEtaleRingSheafChangeAdjunction u
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
      (d.integralRingIso u) (exchangeScalar_comm d u)).2.2 K L
        (d.ordinaryToCompleted u K ≫ a))


/-- Source functor for the normalized equation, on the full derived-complete category.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def normalizedSource := inclusion d X ⋙ d.push f ⋙ d.completedPull g ⋙ res d Y'

/-- Target functor for the normalized equation in constant coefficients.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def normalizedTarget := inclusion d X ⋙ res d X ⋙ completePull d g' ⋙ push (A := A) f'

/-- The restricted raw ordered construction followed by the specified target comparison.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def rawComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (res d Y').map (d.completedExchange sq K.obj) ≫
    (iotaT (g' := g') (f' := f') d K.obj K.property).hom

/-- The specified constant strict mate, conjugated by s, t and the source scalar map.
Source: Stacks 099M, 0E48
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def constantComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (iotaS (f := f) (g := g) d K.obj K.property).hom ≫
    (S (f := f) (g := g) d ((res d X).obj K.obj)).hom ≫
    (rlim (A := A) Y').map ((exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
      ((reduction d X).obj ((res d X).obj K.obj))) ≫
    (T (f' := f') (g' := g') d ((res d X).obj K.obj)).inv

/-- Both displayed composites are natural for every morphism of complete inputs.
Source: Stacks 0E48 (blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).
Proof: the raw strict exchange is the composite H inverse, reduction of the ambient
mate, H prime. All its terms are natural in the ambient input. The scalar comparisons
are natural isomorphisms defined by ordinary sections or universal model comparisons.
Their completed extensions are natural by uniqueness under the completion unit. The
constant mate and its reconstruction and direct-limit comparisons are natural as well.
Compose these naturality equations. Fullness allows every morphism between complete
objects, with no boundedness or finite-origin restriction. -/
theorem normalized_naturality (sq : ChosenCartesianSquare g' f' f g)
    (K L : AComplete d X) (a : K ⟶ L) :
    (normalizedSource (f := f) (g := g) d).map a ≫ rawComponent d sq L =
      rawComponent d sq K ≫ (normalizedTarget (g' := g') (f' := f') d).map a ∧
    (normalizedSource (f := f) (g := g) d).map a ≫ constantComponent d sq L =
      constantComponent d sq K ≫ (normalizedTarget (g' := g') (f' := f') d).map a := by
  let piA (U V : Scheme.{t}) (u : U ⟶ V) :
      d.push u ⋙ completedReductionTower V d ≅
        completedReductionTower U d ⋙ d.towerPush u :=
    NatIso.ofComponents (fun K ↦ asIso (d.towerProjection u K))
      (fun {K L} a ↦ (d.towerProjection_properties u K).2.1 L a)
  let e : d.push f ⋙ d.completedPull g ⟶ d.completedPull g' ⋙ d.push f' :=
    Functor.whiskerRight (Functor.isoWhiskerRight (piA X Y f) (d.towerPull g)).hom
        (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerRight (exchangeStrictNatTrans d sq)
        (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
        (d.directImageRlimIso f').inv
  let it : inclusion d X ⋙ d.completedPull g' ⋙ d.push f' ⋙ res d Y' ≅
      normalizedTarget (g' := g') (f' := f') d :=
    Functor.isoWhiskerLeft (inclusion d X ⋙ d.completedPull g') (chi d f') ≪≫
      Functor.isoWhiskerRight (phi d g') (push (A := A) f')
  constructor
  · exact (Functor.whiskerLeft (inclusion d X)
      (Functor.whiskerRight e (res d Y')) ≫ it.hom).naturality a
  · let aj := exchangeTowerAdjunction f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A)
    let ar := proEtaleRingDerivedAdjunction f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A)
    let pi0 := (mateEquiv ar aj
      (TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom)).natTrans
    have hpi (M : D (A := A) X) : pi0.app M = projection d f M := by
      apply (aj.homEquiv _ _).symm.injective
      change (aj.homEquiv _ _).symm (pi0.app M) =
        (aj.homEquiv _ _).symm ((aj.homEquiv _ _)
          ((reductionPullIso d f).hom.app ((push (A := A) f).obj M) ≫
            (reduction d X).map (ar.counit.app M)))
      rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      exact mateEquiv_counit ar aj
        (TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom) M
    let p0 : push (A := A) f ⋙ reduction d Y ≅
        reduction d X ⋙ exchangeConstantPush (A := A) f :=
      NatIso.ofComponents (fun M ↦ asIso (projection d f M)) (by
        intro M N b
        simpa only [asIso_hom, ← hpi] using pi0.naturality b)
    let h0 := Functor.isoWhiskerLeft (push (A := A) f) (reductionPullIso d g).symm ≪≫
      Functor.isoWhiskerRight p0 (exchangeConstantPull (A := A) g)
    let s0 := Functor.isoWhiskerRight h0 (rlim (A := A) Y')
    let t0 := Functor.isoWhiskerLeft (reduction d X)
      (Functor.isoWhiskerLeft (exchangeConstantPull (A := A) g')
        (directLimitIso (A := A) f'))
    let rec0 : completePull d g' ≅
        reduction d X ⋙ exchangeConstantPull (A := A) g' ⋙ rlim (A := A) X' :=
      Functor.isoWhiskerRight (reductionPullIso d g').symm (rlim (A := A) X')
    let tt := Functor.isoWhiskerRight rec0 (push (A := A) f') ≪≫ t0
    let pushed : AComplete d X ⥤ AComplete d Y :=
      ObjectProperty.lift (d.TowerComplete Y) (inclusion d X ⋙ d.push f)
        (fun M ↦ d.push_complete f M.obj M.property)
    let src : normalizedSource (f := f) (g := g) d ≅
        inclusion d X ⋙ res d X ⋙ push (A := A) f ⋙ completePull d g :=
      Functor.isoWhiskerLeft pushed (phi d g) ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft (inclusion d X) (chi d f))
          (completePull d g)
    let cc := src.hom ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X) s0.hom ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X ⋙ reduction d X)
        (Functor.whiskerRight
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate (rlim (A := A) Y')) ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X) tt.inv
    exact cc.naturality a

/-- The raw ordered exchange as an actual natural transformation after scalar restriction.
Source: blueprint completed-exchange-coherence, paragraph 2
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def rawNormalized (sq : ChosenCartesianSquare g' f' f g) :
    normalizedSource (f := f) (g := g) d ⟶ normalizedTarget (g' := g') (f' := f') d where
  app K := rawComponent d sq K
  naturality K L a := (normalized_naturality d sq K L a).1

/-- The specified constant-coefficient ordered expression as a natural transformation.
Source: Stacks 099M, 0E48
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison). -/
def constantNormalized (sq : ChosenCartesianSquare g' f' f g) :
    normalizedSource (f := f) (g := g) d ⟶ normalizedTarget (g' := g') (f' := f') d where
  app K := constantComponent d sq K
  naturality K L a := (normalized_naturality d sq K L a).2

/-- All specified strict coefficient, reconstruction and direct-image/limit normalizations,
including equality of the ordered maps as natural transformations on the full complete category.
Source: main-20261015 blueprint, completed-exchange-coherence, second proof paragraph;
strict coefficient supplement, Stacks 099M, 099N, 0A07 and 0E48
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).

Proof, following the fourteen steps of the DAG node:

1. Write $r_T=\operatorname{Res}_T$, and distinguish the one-object indexing category from
$J=\mathbf N_{\geq1}^{op}$. The coefficient maps commute with $\underline A\to A_T$: on constant
sections both composites send $a$ to its image, and the finite projections determine the map to
$A_U$. The profinite inverse-image lemma supplies both the coefficient isomorphisms and their
composition/transition compatibility. Flatness of $A_T$ over $\underline A_T$ is supplied by the
constant-completion equivalence. Apply the flat ringed diagram restriction theorem first with
the one-object category and then with $J$. All sites are small; its scalar-square and flatness
hypotheses have just been checked. In the first application it gives $a_u:r_ULu_a^*\simeq
G_ur_V$ and $\chi_u:r_VRu_*\simeq R_u^0r_U$ on AMBIENT module complexes, with the stated adjunct
compatibility. In the second it gives $p_u:r_U\mathscr L_u\simeq G_ur_V$ and $d_u:r_V\mathscr
R_u\simeq R_u^{\mathcal T}r_U$. These use the identified underlying inverse image and direct
image on a K-injective model. Explicitly the left adjoint of restriction is
$A_T\otimes_{\underline A_T}-$, exact by flatness; the right-adjoint K-injective theorem applies
for this reason, not merely because restriction itself is exact.

2. For an ARBITRARY completed-coefficient tower $Z$, apply the ringed tower pushforward/limit
comparison to the identity geometric morphism with structure map $\underline A_T\to A_T$. Its
module direct image is restriction; restriction is exact, so its derived functor is $r_T$. This
gives $\lambda_Z:r_T\mathcal L^aZ\simeq\mathcal Lr_TZ$, without a finite-reduction hypothesis.
Check its normalization together with direct image as follows. Choose a K-injective tower $Z\to
J_Z$; such resolutions exist since the small module diagram categories are Grothendieck.
Restriction preserves its K-injectivity by Step 1. Also $\lim J_Z$ is K-injective: $\lim$ is
right adjoint to the exact constant-diagram functor, so the right-adjoint theorem applies. For
each edge the ordinary and diagram direct images preserve K-injectives, since their identified
inverse images are exact. Thus $J_Z,rJ_Z,u_*J_Z,\lim J_Z$ compute the required derived
composites. Denote their direct-image/limit comparisons by $\kappa_u^a,\kappa_u^0$. On these
models the two routes below are the SAME equality of complexes, $r_Vu_*\lim J_Z=\lim u_*r_UJ_Z$:
$$\mathcal L(d_{u,Z})\lambda_{\mathscr
R_uZ}r_V(\kappa_u^a(Z))=\kappa_u^0(r_UZ)R_u^0(\lambda_Z)\chi_{u,\mathcal L^aZ}.$$ The
K-injective total-derived theorem identifies these models with the canonical derived functors.
This proves compatibility of the specified comparisons, not uniqueness from their finite
projections.

3. The diagram-site realization identifies strict towers with modules on one small ringed site,
with ring $\Delta A_T$. For this $J$, object $1$ is terminal, so
$\operatorname{colim}_J=\operatorname{ev}_1$ is exact. Its right adjoint $\Delta$ therefore
preserves K-injectives by the right-adjoint theorem. An ambient K-injective representative $I_K$
consequently computes $\mathscr R_f\Delta K=\Delta Rf_*K$ by the same complex $\Delta f_*I_K$;
the same argument applies to $f'$ and any ambient input $E$. A diagonal flat-term K-flat
representative is K-flat on the diagram site: its tensor with an acyclic diagram is acyclic at
every level, hence acyclic by levelwise cohomology. Existence of the ambient representative and
the derived tensor comparison are supplied by the K-flat resolution and tensor-descent nodes. On
these representatives the diagonal adjunction bijections are the componentwise ordinary ones.
The characterization of the derived bijection on fraction representatives therefore identifies
diagonal units and counits with the ambient ones. Pullback composition is termwise as well. By
the mate's transpose formula the diagram exchange on $\Delta K$ is $\Delta e$. This comparison
uses no properness or finite-origin witnesses.

4. On the diagram site, the constant-completion equivalence applies to $\Delta\underline
A_T\to\Delta A_T$: constant sheaves and limits are fiberwise under the diagram-site equivalence.
Apply its finite-reduction comparison to $\Delta K$. The strict tensor construction gives
$$\rho_K:r_X\mathcal R_X^aK\simeq\mathcal R_X\bar K.$$ On a flat-term K-flat representative $P$,
both sides are the SAME quotient diagram $(P/I^nP)_n$ with its quotient transitions; the map
sends the class of $p$ to itself. Thus it respects the quotient unit as well. The derived
tensor/pullback comparison and the coefficient identities identify $\mathcal R_U^aLu_a^*L$ with
$\mathscr L_u\mathcal R_V^aL$. Combining this with $p_u$ and the preceding balancing map gives
$\rho_{u,L}:r_U\mathscr L_u\mathcal R_V^aL\simeq G_u\mathcal R_Vr_VL$. These are strict-diagram
comparisons, natural in $L$. Define $$\beta=(G_gR_f^{\mathcal T}\rho_K)(G_gd_f)p_g,\qquad
\delta=(R_{f'}^{\mathcal T}G_{g'}\rho_K)(R_{f'}^{\mathcal T}p_{g'})d_{f'}.$$ Finally $\rho_M$ is
the same reduction comparison for $M$, followed by $\mathcal R(a_g)$ and $\mathcal
R(G_g\chi_f)$. These formulas give exactly the source, target and coefficient identifications
specified in (2).

5. Check the projection-formula equation by transposition, rather than by evaluations. On each
coefficient diagram the projection map is the adjunct of $(\varepsilon_{f,K}\otimes1)t_f$. The
adjunct clause of flat diagram restriction identifies its restricted adjunct with the adjunct of
its restricted transpose, and in particular identifies the restricted counit with the
constant-coefficient counit. Under $\rho$, the tensor factor in that transpose is a quotient: on
a K-flat representative the comparison is $p\otimes\bar a\mapsto p\otimes\bar a$, and the
pullback/tensor comparison sends it to $(p\otimes1)\otimes\bar a$. Applying a morphism $h$
before or after either map sends it to $(h(p)\otimes1)\otimes\bar a$. Use this with the counit
and the identified pullback. Hence the restricted transpose is exactly $(\varepsilon^0_{f,\bar
K}\otimes1)t_f^0$. Bijectivity of the adjunct correspondence identifies the two projection maps.
Apply $G_g$ and use the formulas for $\beta,\rho_M$ in Step 4 to obtain
$$\beta\,r(H^a)=H^0\rho_M.$$ This is an equality of derived diagram morphisms: the tensor
comparisons come from natural maps on the resolving class, and tensor descent makes their
equality an equality after localization. No general monoidal identification of the two ambient
scalar categories is used.

6. Let $W$ be the completed-coefficient strict-diagram exchange at $\mathcal R_X^aK$, defined by
its adjunction mate. Apply ringed exchange/tensor coherence on the completed ringed diagram
sites with object $\Delta K$ and coefficient object $Q_{Y,\bullet}=(\underline{P_n}_Y)_n$. This
theorem allows arbitrary ringed topoi and needs no properness. The coefficient isomorphisms give
$\mathscr L_uQ_{V,\bullet}\simeq Q_{U,\bullet}$, respecting the full quotient diagram and the
square. Step 3 identifies exchange at $\Delta K$ with $\Delta e$. Thus the first composite in
the coherence theorem is $WH^a$, while the second is $H'^a\mathcal R_{Y'}^a(e)$. Its stated
equality gives $$WH^a=H'^a\mathcal R_{Y'}^a(e),\qquad W=v^a.$$ Here right composition with the
specified inverse of $H^a$ gives the second equation. The inverses in the item exist: their
evaluations are perfect projection-formula isomorphisms; their cones have zero evaluated
cohomology and hence zero cohomology diagram. This uses conservativity for isomorphisms from
levelwise exactness, never faithfulness of evaluations on morphisms.

7. Before composing with $\rho_K$, let $b,d$ be the two composites of $p_u,d_u$ for the corners
at $r_X\mathcal R_X^aK$. Transpose $d\,r(W)b^{-1}$ under $G_{f'}\dashv R_{f'}^{\mathcal T}$. The
adjunct clause of flat diagram restriction replaces its counit by the constant-coefficient
counit. Pullback composition is also identified: its K-flat representative multiplies nested
extension scalars, and after restriction both routes are the same composite inverse-image
identification; the coefficient composition compatibility identifies their ring actions.
Consequently its transpose is $$G_{g'}\varepsilon_f^{\mathcal T}\circ\theta^{\mathcal
T}_{\square,R_f^{\mathcal T}r_X\mathcal R_X^aK}.$$ This is precisely the transpose defining
$E^{\mathcal T}_{r_X\mathcal R_X^aK}$. The adjunction bijection gives $d\,r(W)=E^{\mathcal T}b$.
Compose with $R_{f'}^{\mathcal T}G_{g'}\rho_K$ and use naturality of this mate for $\rho_K$;
with Step 6 and the definitions of $\beta,\delta$ this is $$\delta\,r(v^a)=E^{\mathcal
T}_{\mathcal R_X\bar K}\beta.$$ All equalities are in the derived strict-diagram category and
hold for every complete $K$.

8. Only now assume the additional properness and the levelwise etale-origin witnesses in the
strict-tower exchange normalization lemma. Its statement specifies $B_\bullet,D_\bullet$ as
precisely $B^a,D^a$ and $v'_\bullet=H'^a\mathcal R^a(e)(H^a)^{-1}=v^a$. Its $b,d$ are normalized
by the same restricted inverse images and the same K-injective direct images as Step 1.
Therefore the $\beta,\delta$ of Step 4 are those $b,d$ followed by the images of $\rho_K$. The
ordered completed base-change definition has source map $\mathcal L^a(H^a)r_S=s^a$, tower map
$v^a$, and target comparison $c^a$ with the same direction. Substitution gives exactly
$x^a_K=(c^a)^{-1}\mathcal L^a(v^a)s^a$. Since this expression was constructed before witnesses,
it is independent of which witnesses are supplied. No assertion of that lemma was applied to an
unwitnessed input.

9. We fix the completed comparison by its unit. Let $L$ be complete on $V$, and put
$j^a_{u,L}:Lu_a^*L\to F_u^aL$. By the completed-pullback definition and Koszul reconstruction,
this is quotient completion, with its canonical unit. The constant-completion equivalence
identifies this unit with the constant coefficient completion unit. With the strict
pullback/reduction comparison of Step 4 and $\lambda$ of Step 2, set $$\Psi_{u,L}=\mathcal
L(\rho_{u,L})\lambda\,r_U(r_{u,L}):r_UF_u^aL\longrightarrow\mathcal L G_u\mathcal
R_Vr_VL=F_u^0r_VL.$$ Here $r_{u,L}$ is the defining reconstruction into $\mathcal L^a\mathscr
L_u\mathcal R_V^aL$. All factors are isomorphisms. The two maps out of the uncompleted pullback
satisfy $$\Psi_{u,L}\,r_U(j^a_{u,L})=j^0_{u,r_VL}\,a_{u,L}.$$ Indeed they arise from the
identical strict map from the constant representative to its quotient diagram: Step 4 sends $p$
to its same class at every level WITH its transitions, and Step 2 takes the same limit after
restriction. Thus this is equality of induced completion-unit maps, not an argument from
evaluated equalities. The reflector node supplies bijectivity of precomposition with this unit
for maps into any complete object; Koszul reconstruction identifies its unit with the quotient
unit being used.

10. The unit identity in Step 9 identifies $\Psi_{u,L}$ with the stipulated $\phi_{u,L}$, as
follows. For complete $N$ on $U$, the two completed-adjunction Hom bijections first precompose
with $j^a_{u,L}$ or $j^0_{u,r_VL}$ and then use the ambient adjunction. Step 1's adjunct clause
says the second operations agree under $a_u,\chi_u$; Step 9's identity says the first operations
agree under $\Psi_u$. Equivalences on complete objects are fully faithful by constant-completion
equivalence. Hence $\Psi_u$ respects exactly these Hom bijections and is the isomorphism
defining $\phi_u$ in (1). Uniqueness also follows directly from the reflector's injective
precomposition map. Taking identities under these Hom bijections identifies the units and
counits. Direct image preserves completeness by the direct-image-limits node (and on the
constant side by completed-pullback-adjunction); thus the adjunctions are on the full complete
subcategories as required. Finally the explicit conjugate formula, using just the identified
units and counits, carries the specified direct-image composition and identity maps to their
corresponding completed pullback comparisons. This proves all of (1).

11. Apply $\Psi=\phi$ from Steps 9–10 to $(u,L)=(g',K)$. Its defining formula is precisely
$$\mathcal L(\rho_{g',K})\lambda\,r(r_{g',K})=r_{g',K}^0\phi_{g'}.$$ For the source apply it to
$(u,L)=(g,Rf_*K)$; this input is complete by direct-image-limits. Replace $r_YRf_*K$ by
$R_f^0\bar K$ through $\chi_f$. Naturality of the completion unit and of its strict quotient
diagram gives the comparison $F_g^0\chi_f$ on completed pullbacks and $\mathcal R(G_g\chi_f)$ on
the reduction diagram. By Step 4 their composite on the latter diagram is exactly $\rho_M$. With
the source reconstruction $r_S$ this yields $$\mathcal L(\rho_M)\lambda_{\mathcal
R^aM}\,r(r_S)=r_S^0(F_g^0\chi_f)\phi_g=r_S^0\iota_S.$$ For clarity the equality of these
extensions can be tested by precomposing with the completion unit, where both maps are the
strict quotient map followed by $G_g\chi_f$; injectivity of unit precomposition into a complete
target, supplied by the reflector, proves the equality. This derives both fixed reconstruction
equations in (3).

12. The source normalization now follows by functoriality. Since $s^a=\mathcal L^a(H^a)r_S$,
naturality of $\lambda$ and Step 5 give $$\begin{aligned} \mathcal L(\beta)\lambda_{B^a}r(s^a)
&=\mathcal L(\beta\,r(H^a))\lambda_{\mathcal R^aM}r(r_S)\\ &=\mathcal L(H^0)\mathcal
L(\rho_M)\lambda_{\mathcal R^aM}r(r_S)\\ &=\mathcal L(H^0)r_S^0\iota_S=s^0\iota_S.
\end{aligned}$$ The last equality uses exactly the definition of $s$ in
completion-mate-comparison, so an arbitrary source isomorphism has not been substituted.

13. For the target put $u=f'$ and $Z=\mathscr L_{g'}\mathcal R_X^aK$, and abbreviate
$\rho_{g',K}$ to $q$. The definitions give $$c^a=\kappa_u^a(Z)Ru_*(r_{g',K}),\quad
\delta=(R_u^{\mathcal T}q)d_{u,Z},\quad t^0=\kappa_u^0(G_{g'}\mathcal R_X\bar
K)R_u^0(r_{g',K}^0).$$ Use the comparison square of Step 2, followed by naturality of
$\kappa_u^0$ for $q$ and of $\chi_u$ for $r_{g',K}$. It gives, in the written order,
$$\begin{aligned} \mathcal L(\delta)\lambda_{D^a}r(c^a) &=\kappa_u^0(G_{g'}\mathcal R_X\bar K)\,
R_u^0\bigl(\mathcal L(q)\lambda_Zr(r_{g',K})\bigr)\chi_{u,F_{g'}^aK}\\
&=\kappa_u^0(G_{g'}\mathcal R_X\bar K)R_u^0(r_{g',K}^0\phi_{g'})\chi_{u,F_{g'}^aK}\\
&=t^0(R_u^0\phi_{g'})\chi_{u,F_{g'}^aK}=t^0\iota_T. \end{aligned}$$ The second equality is the
target reconstruction identity of Step 11. The direct-image-limits statement and
completion-mate-comparison specify their $c^a,t^0$ by the K-injective direct-image/limit
comparison used in Step 2. Thus this calculation proves compatibility of those specified
comparisons, including $\chi,\lambda,\delta$, rather than assuming a finite-reduction
normalization.

14. Apply $\mathcal L$ to Step 7 and use naturality of $\lambda$. Substitute the source and
target normalizations of Steps 12–13 into $x_K^a=(c^a)^{-1}\mathcal L^a(v^a)s^a$ and cancel the
isomorphisms in order: $$\begin{aligned} \iota_Tr(x_K^a) &=(t^0)^{-1}\mathcal
L(\delta)\lambda_{D^a}\,r(\mathcal L^a(v^a))r(s^a)\\ &=(t^0)^{-1}\mathcal
L(\delta\,r(v^a))\lambda_{B^a}r(s^a)\\ &=(t^0)^{-1}\mathcal L(E^{\mathcal T})\mathcal
L(\beta)\lambda_{B^a}r(s^a)\\ &=(t^0)^{-1}\mathcal L(E^{\mathcal T})s^0\iota_S. \end{aligned}$$
All transformations in the construction are natural: the scalar and finite-reduction
comparisons, the adjuncts, completion units, and the K-injective limit comparisons. The
displayed derivations are operations on those transformations, hence hold naturally for every
morphism of complete $K$. Completed pullback lands in the complete category by its reflector
description, and direct image preserves that category; the same proof therefore applies to those
intermediate complete inputs. Completion-mate-comparison identifies the right-hand expression
with the completed constant-coefficient mate; its Noetherian and perfect-quotient hypotheses are
those of the datum. No identity-square or pasting law is used.
-/
theorem coefficientComparison (sq : ChosenCartesianSquare g' f' f g) :
    (∀ (K : d.derived X) (hK : d.TowerComplete X K),
      (d.towerV' sq K =
        (exchangeRealizationH (f := f) (g := g) d K).inv ≫
          (completedReductionTower Y' d).map ((d.integralExchange sq).app K) ≫
          (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) ∧
      ((exchangeTowerRes d Y').map
          (exchangeRealizationH (f := f) (g := g) d K).hom ≫
            (beta (f := f) (g := g) d K).hom =
        (rhoM (f := f) (g := g) d K).hom ≫
          (H (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((exchangeTowerRes d Y').map (d.towerV' sq K) ≫
          (delta (f' := f') (g' := g') d K).hom =
        (beta (f := f) (g := g) d K).hom ≫
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
            ((reduction d X).obj ((res d X).obj K))) ∧
      ((res d Y').map (sourceReconstruction (f := f) (g := g) d K).hom ≫
          (lambda d Y').hom.app
            ((completedReductionTower Y' d).obj ((d.pull g).obj ((d.push f).obj K))) ≫
          (rlim (A := A) Y').map (rhoM (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom) ∧
      ((lambda d X').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K)) ≫
          (rlim (A := A) X').map (rhoPull (g' := g') d K).hom =
        (phi d g').hom.app ⟨K, hK⟩ ≫
          (reconstruction d g' ((res d X).obj K)).hom) ∧
      ((res d Y').map (sourceA (f := f) (f' := f') (g := g) (g' := g') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (beta (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom ≫
          (S (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((res d Y').map (targetA (g' := g') (f' := f') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (delta (f' := f') (g' := g') d K).hom =
        (iotaT (f' := f') (g' := g') d K hK).hom ≫
          (T (f' := f') (g' := g') d ((res d X).obj K)).hom)) ∧
    rawNormalized d sq = constantNormalized d sq ∧
    (∀ [IsProper f] (K : d.derived X) (hK : d.TowerComplete X K)
      (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj K)),
      d.completedExchange sq K = d.completedBaseChangeMap sq K hK W) := by
  sorry

end AlgebraicGeometry.Scheme.OrderedExchange
