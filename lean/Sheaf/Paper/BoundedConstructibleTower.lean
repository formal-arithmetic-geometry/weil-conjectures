/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.Paper.AdicLisseModule
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.Topology.Stratification
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Uniformly bounded constructible adic towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-bounded-constructible-tower, order 1250; Stacks Tags 09AI and 09BT
(blueprint: def-weil-pbc-bounded-constructible-tower).

Positive level n+1 is indexed by n : ℕ. Normalizations are stored for every comparable
pair; their cocycle determines the nonconsecutive ones from the consecutive ones.
Compatibility is expressed on their adjoints M_b→Res(M_a). The tensor-unit normalized
scalar-extension adjunction makes this equivalent to the displayed normalization
identities in the blueprint. This permits restrictions to retain their actual
inverse-image coefficients, without choosing a tensor/pullback comparison.

## Main definitions

* `AdicTower`: a derived strict tower with quotient-linear normalized levels.
* `AdicTowerLocalModel`: one bounded local complex and its compatible reductions.
* `IsUniformlyBoundedConstructibleAdicTower`: common bounds, finite strata and local models.
* `pbcLevelConstantComparison` and `pbcCompletedComparison`: canonical coefficient
  presentation comparisons fixed on constant sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- Finite lissity over an inverse-image constant ring. A covering sieve on the final
object trivializes F as a module sheaf; on each member the constant is a finite module.
The coefficient ring is exactly the inverse image, so the module isomorphism is linear
with the restricted coefficient action, including when g is the identity.
Source: Stacks Tags 09AI and 099Y (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def IsRelativelyFiniteLisseModule {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    (F : ringedSiteModules.{u + 1} ((adicLisseForget Y).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X A)))) :
    Prop :=
  ∃ S : Sieve (⊤_ Y.ProEt), S ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
    ∀ (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt), S f →
      ∃ M : ModuleCat.{u + 1} A, Finite M ∧
        Nonempty ((SheafOfModules.overFunctor _ V).obj F ≅
          (SheafOfModules.overFunctor _ V).obj
            ((proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj
              ((adicLisseConstantModules X A).obj M)))


variable (X : Scheme.{u})

/-- The module category over a commutative ring sheaf on the small site.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcModules (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((adicLisseForget X).obj R)

/-- Strict inverse sequences, reindexed by n ↦ n+1.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcTowers (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ℕᵒᵖ ⥤ pbcModules X R

/-- The standard derived localization for strict towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcTowers_hasDerivedCategory
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory (pbcTowers X R) := HasDerivedCategory.standard _

/-- Exact termwise evaluation in the derived tower category.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcTowerEvaluation (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (n : ℕ) :=
  ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X R)).obj (op n)).mapDerivedCategory

variable {X} {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)

/-- Restrict scalar actions along the given ring-sheaf map.
Source: Stacks Tag 03CZ (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcRestrict :=
  proEtaleRingRestrictScalars φ

/-- Exact restriction preserves finite limits. Source: Stacks Tag 03DA
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcRestrict_limits : PreservesFiniteLimits (pbcRestrict φ) :=
  (proEtaleRingRestrictScalars_properties φ).1

/-- Exact restriction preserves finite colimits. Source: Stacks Tag 03DA
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcRestrict_colimits : PreservesFiniteColimits (pbcRestrict φ) :=
  (proEtaleRingRestrictScalars_properties φ).2.1

/-- Restriction of scalars is additive on pro-etale module sheaves.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcRestrict_additive : (pbcRestrict φ).Additive := by
  dsimp [pbcRestrict, proEtaleRingRestrictScalars]
  infer_instance

/-- Exact scalar restriction on unbounded derived categories.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcDerivedRestrict := (pbcRestrict φ).mapDerivedCategory

set_option linter.defProp false in
/-- The existing universal scalar-extension theorem, including its fixed objects,
fixed maps and K-flat computation. Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcExtensionExistence :=
  completedAdicChangeData X φ

/-- Ordinary sheafified tensor extension, determined on both objects and maps.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcExtend : pbcModules X R ⥤ pbcModules X S := completedAdicChange X φ

/-- Tensor extension is additive. Source: Stacks Tag 03EK
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcExtend_additive : (pbcExtend φ).Additive :=
  (pbcExtensionExistence φ).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The universal derived pair supplied by the existing K-flat scalar-extension theorem.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcDerivedExtensionExistence :=
  (pbcExtensionExistence φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived scalar extension, determined up to unique comparison compatible with its
universal counit. Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcDerivedExtend : DerivedCategory (pbcModules X R) ⥤
    DerivedCategory (pbcModules X S) := completedAdicDerivedChange X φ

/-- The universal comparison, invertible on K-flat complexes.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcExtensionCounit : DerivedCategory.Qh ⋙ pbcDerivedExtend φ ⟶
    (pbcExtend φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (pbcDerivedExtensionExistence φ).choose_spec.choose

/-- A sheafified pure tensor, using the object equality in the scalar-extension witness.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcTensorSection (M : pbcModules X R) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) : ((pbcExtend φ).obj M).val.obj U :=
  completedAdicChangeTensor X φ M U s x


/-- The tensor-unit normalized ordinary adjunction is unique.
Source: Stacks Tags 03EK and 06YY (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: the sheafification universal property and sectionwise tensor adjunction identify
maps out of E(M) with maps M→Res(N), by precomposition with m↦1⊗m. These bijections are
natural. They give the adjunction, and their formula determines it uniquely. -/
theorem pbcScalarAdjunction_exists :
    ∃! adj : pbcExtend φ ⊣ pbcRestrict φ,
      ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (adj.unit.app M).val.app U x = pbcTensorSection φ M U 1 x := by
  sorry

/-- The ordinary adjunction with its actual tensor unit.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcScalarAdjunction : pbcExtend φ ⊣ pbcRestrict φ :=
  (pbcScalarAdjunction_exists φ).exists.choose

/-- The universal derived counit expressed on cochain representatives.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcComplexCounit (P : CochainComplex (pbcModules X R) ℤ) :
    (pbcDerivedExtend φ).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcDerivedExtend φ).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)

/-- The derived adjunction is uniquely fixed by its tensor-unit computation on K-flats.
Source: Stacks Tags 06YY and 0DVC (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: exact restriction has its termwise derived functor. Derive the ordinary adjunction
using K-flat resolutions on the left. Its unit on a K-flat P is the localization of
P→Res(E(P)), transported by the invertible universal counit. Every object has a K-flat
representative; the Hom adjunction and naturality follow from the ordinary bijections
and localization. The formula fixes the unit everywhere and therefore the adjunction. -/
theorem pbcDerivedScalarAdjunction_exists :
    ∃! adj : pbcDerivedExtend φ ⊣ pbcDerivedRestrict φ,
      ∀ (P : CochainComplex (pbcModules X R) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R) P →
        adj.unit.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
            (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
              (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P) := by
  sorry

/-- Canonical derived scalar extension/restriction adjunction.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcDerivedScalarAdjunction : pbcDerivedExtend φ ⊣ pbcDerivedRestrict φ :=
  (pbcDerivedScalarAdjunction_exists φ).exists.choose

variable {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)

include h in
/-- Composition of ordinary scalar restrictions is identity on underlying sections.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: the actions coincide by h; identity on sections is linear and natural, and its
inverse is identity. Sectionwise faithfulness gives uniqueness. -/
theorem pbcRestrictComp_exists :
    ∃! e : pbcRestrict ψ ⋙ pbcRestrict φ ≅ pbcRestrict χ,
      ∀ (M : pbcModules X B) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (e.hom.app M).val.app U x = x := by
  sorry

/-- The canonical ordinary restriction comparison.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcRestrictComp : pbcRestrict ψ ⋙ pbcRestrict φ ≅ pbcRestrict χ :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose

/-- Composition of exact derived scalar restrictions, with its canonical section maps.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcDerivedRestrictComp : pbcDerivedRestrict ψ ⋙ pbcDerivedRestrict φ ≅
    pbcDerivedRestrict χ :=
  (Functor.mapDerivedCategoryCompIso (pbcRestrict ψ) (pbcRestrict φ)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pbcRestrictComp φ ψ χ h)

/-- The reduction transition is the adjunct of the direct scalar-extension unit.
This formula is the derived version of b⊗x↦ψ(b)⊗x.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcReductionTransition (K : DerivedCategory (pbcModules X R)) :
    (pbcDerivedExtend φ).obj K ⟶
      (pbcDerivedRestrict ψ).obj ((pbcDerivedExtend χ).obj K) :=
  ((pbcDerivedScalarAdjunction φ).homEquiv _ _).symm
    ((pbcDerivedScalarAdjunction χ).unit.app K ≫
      (pbcDerivedRestrictComp φ ψ χ h).inv.app ((pbcDerivedExtend χ).obj K))

/-- Its adjunct along ψ is the canonical quotient-reduction normalization map.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcReductionNormalizationHom (K : DerivedCategory (pbcModules X R)) :
    (pbcDerivedExtend ψ).obj ((pbcDerivedExtend φ).obj K) ⟶
      (pbcDerivedExtend χ).obj K :=
  ((pbcDerivedScalarAdjunction ψ).homEquiv _ _).symm
    (pbcReductionTransition φ ψ χ h K)

/-- Derived balancing is invertible, without flatness of either coefficient map.
Source: blueprint order 1239; Stacks Tag 06YY
(blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: resolve K by a K-flat P. Scalar extension Eφ(P) is K-flat over S, since tensoring
it with an acyclic B-complex is P tensored with that complex after restriction. Thus
both derived sides are computed by Eψ(Eφ(P)) and Eχ(P). The displayed adjunct is the
ordinary balancing map s⊗(r⊗x)↦sψ(r)⊗x, by the fixed tensor units. Its inverse sends
s⊗x to s⊗(1⊗x). The balancing relations prove the inverse identities. Local tensor
generation and sheafification give inverse chain maps, hence an isomorphism on localization. -/
theorem pbcReductionNormalization_isIso (K : DerivedCategory (pbcModules X R)) :
    IsIso (pbcReductionNormalizationHom φ ψ χ h K) := by
  sorry

/-- Canonical normalization, retaining its balancing and unit characterization.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcReductionNormalization (K : DerivedCategory (pbcModules X R)) :
    (pbcDerivedExtend ψ).obj ((pbcDerivedExtend φ).obj K) ≅
      (pbcDerivedExtend χ).obj K :=
  letI := pbcReductionNormalization_isIso φ ψ χ h K
  asIso (pbcReductionNormalizationHom φ ψ χ h K)



/-- The already constructed quotient coefficient system; n means positive exponent n+1.
A constant sheaf is canonically also the sheafification of continuous maps from connected
components to the discrete ring: every such function is locally constant on its open
fibres, which form a Zariski, hence pro-etale, cover. Constant sections give the comparison.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcAdicRings (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :=
  AdicCoefficients.ringSystem X d.ideal d.quotientFinite

/-- The completed coefficient sheaf is the actual inverse limit of the quotient sheaves.
Limits of sheaves are sectionwise compatible families, with pointwise operations.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcAdicCompletion (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :=
  AdicCoefficients.completedRing X d.ideal d.quotientFinite

/-- All quotient maps in the coefficient diagram, including equal indices.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcAdicQuotient (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (b a : ℕ) (hab : a ≤ b) :=
  (pbcAdicRings X d).map (homOfLE hab).op

/-- The n-th coordinate of a compatible family in the completed ring.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcAdicProjection (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (n : ℕ) : pbcAdicCompletion X d ⟶ (pbcAdicRings X d).obj (op n) :=
  limit.π (pbcAdicRings X d) (op n)

set_option linter.defProp false in
/-- Projection followed by quotient reduction is the lower projection.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: apply the naturality equation of the limit cone to the arrow b→a. -/
theorem pbcAdicProjection_comp (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (hab : a ≤ b) :
    pbcAdicProjection X d b ≫ pbcAdicQuotient X d b a hab = pbcAdicProjection X d a := by
  sorry

set_option linter.defProp false in
/-- Quotient maps satisfy the full quotient cocycle.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: the coefficient diagram preserves composition, and the opposite poset has a unique
arrow between its comparable endpoints. This includes every equal-index case. -/
theorem pbcAdicQuotient_comp (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    pbcAdicQuotient X d c b hbc ≫ pbcAdicQuotient X d b a hab =
      pbcAdicQuotient X d c a (hab.trans hbc) := by
  sorry

/-- The natural derived transition between any two evaluations of a strict tower.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcTowerTransition (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (b a : ℕ) (hab : a ≤ b) :
    pbcTowerEvaluation X R b ⟶ pbcTowerEvaluation X R a :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcTowers X R) (.up ℤ)) _ _
    (pbcTowerEvaluation X R b) (pbcTowerEvaluation X R a)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X R)).map (homOfLE hab).op) (.up ℤ))
        DerivedCategory.Q)


/-- The quotient continuous-function presheaf with its prescribed discrete topology.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcQuotientPresheaf (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} :=
  letI := d.quotientFinite n
  AdicCoefficients.functionPresheaf X (A ⧸ d.ideal ^ (n + 1))

/-- The constant continuous component function used by the coefficient comparison.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
noncomputable def pbcQuotientConstant (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    (U : X.ProEtᵒᵖ) (b : A ⧸ d.ideal ^ (n + 1))
    (τ : TopologicalSpace (A ⧸ d.ideal ^ (n + 1))) :
    @ContinuousMap (ConnectedComponents U.unop.left) (A ⧸ d.ideal ^ (n + 1))
      inferInstance τ :=
  @ContinuousMap.const (ConnectedComponents U.unop.left) (A ⧸ d.ideal ^ (n + 1))
    inferInstance τ b

/-- The constant-section comparison with the recorded continuous-function coefficient.
Source: blueprint order 1250; Stacks Tags 03CY and 00W1
(blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: send each constant section to the same constant continuous component function.
Its level sets give a Zariski, hence pro-etale, cover. Thus this map is locally bijective
and sheafification makes it an isomorphism. Local constant sections generate, giving
uniqueness even for the empty scheme or zero ring. -/
theorem pbcLevelConstantComparison_exists (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃! e : adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)) ≅
        (pbcAdicRings X d).obj (op n),
      ∀ (U : X.ProEtᵒᵖ) (b : A ⧸ d.ideal ^ (n + 1)),
        e.hom.hom.app U
          ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))).app U b) =
          (toSheafify (ProEt.topology X) (pbcQuotientPresheaf X d n)).app U
            (pbcQuotientConstant X d n U b (⊥ : TopologicalSpace (A ⧸ d.ideal ^ (n + 1)))) := by
  sorry

/-- The canonical finite coefficient identification, fixed on constant sections.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcLevelConstantComparison (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)) ≅ (pbcAdicRings X d).obj (op n) :=
  (pbcLevelConstantComparison_exists X d n).exists.choose

/-- Constant comparisons intertwine the entire recorded quotient diagram.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: on constant sections both routes apply the same quotient homomorphism.
Local generation gives the equality at consecutive indices. Every poset arrow is a
composite of consecutive arrows, so induction gives the result for all indices. -/
theorem pbcConstantSystemComparison_naturality (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (adicLisseRingSystem X d.ideal).map f ≫
        (pbcLevelConstantComparison X d n.unop).hom =
      (pbcLevelConstantComparison X d m.unop).hom ≫
        (pbcAdicRings X d).map f := by
  sorry

/-- The comparison of constant and continuous-function quotient coefficient diagrams.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcConstantSystemComparison (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    adicLisseRingSystem X d.ideal ≅ AdicCoefficients.ringSystem X d.ideal d.quotientFinite :=
  NatIso.ofComponents (fun n ↦ pbcLevelConstantComparison X d n.unop)
    (fun f ↦ pbcConstantSystemComparison_naturality X d f)

/-- The completed-coefficient comparison is induced by the quotient diagram.
No completed coefficient sheaf is identified with a constant sheaf.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcCompletedComparison (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    adicLisseCompletedRing X d.ideal ≅ pbcAdicCompletion X d :=
  HasLimit.isoOfNatIso (pbcConstantSystemComparison X d)

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- A normalization's semilinear transition, obtained by its canonical scalar-extension
unit and restriction of its R_a-linear isomorphism.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def adicTowerSemilinearTransition
    (M : ∀ n : ℕ, DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (ρ : ∀ (b a : ℕ) (hab : a ≤ b),
      (pbcDerivedExtend (pbcAdicQuotient X d b a hab)).obj (M b) ≅ M a)
    (b a : ℕ) (hab : a ≤ b) :
    M b ⟶ (pbcDerivedRestrict (pbcAdicQuotient X d b a hab)).obj (M a) :=
  (pbcDerivedScalarAdjunction (pbcAdicQuotient X d b a hab)).unit.app (M b) ≫
    (pbcDerivedRestrict (pbcAdicQuotient X d b a hab)).map (ρ b a hab).hom

/-- An object of D(Tow_A(X)), quotient-linear levels identified with its evaluations,
and normalized derived reductions compatible with its actual transitions. The cocycle
is written on the semilinear adjuncts; the canonical restriction comparison identifies
the two successive scalar restrictions with direct restriction. Invertible normalization
and the equal-index cocycle also force the usual identity normalization.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
structure AdicTower where
  /-- The derived object of strict completed-coefficient towers. -/
  tower : DerivedCategory (pbcTowers X (pbcAdicCompletion X d))
  /-- Each level retains its quotient-ring action. -/
  level : ∀ n : ℕ, DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))
  /-- The scalar restriction is the actual derived evaluation. -/
  evaluation : ∀ n : ℕ,
    (pbcDerivedRestrict (pbcAdicProjection X d n)).obj (level n) ≅
      (pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj tower
  /-- Normalization at all pairs, including the consecutive normalizations of the source. -/
  normalization : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedExtend (pbcAdicQuotient X d b a hab)).obj (level b) ≅ level a
  /-- The restricted scalar-extension/normalization composite is the tower transition. -/
  transition : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedRestrict (pbcAdicProjection X d b)).map
        (adicTowerSemilinearTransition X d level normalization b a hab) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection X d b)
        (pbcAdicQuotient X d b a hab) (pbcAdicProjection X d a)
        (pbcAdicProjection_comp X d b a hab)).hom.app (level a) ≫
      (evaluation a).hom =
    (evaluation b).hom ≫
      (pbcTowerTransition X (pbcAdicCompletion X d) b a hab).app tower
  /-- Direct reduction agrees with reduction through every intermediate level. -/
  cocycle : ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
    adicTowerSemilinearTransition X d level normalization c a (hab.trans hbc) =
      adicTowerSemilinearTransition X d level normalization c b hbc ≫
        (pbcDerivedRestrict (pbcAdicQuotient X d c b hbc)).map
          (adicTowerSemilinearTransition X d level normalization b a hab) ≫
        (pbcDerivedRestrictComp (pbcAdicQuotient X d c b hbc)
          (pbcAdicQuotient X d b a hab)
          (pbcAdicQuotient X d c a (hab.trans hbc))
          (pbcAdicQuotient_comp X d c b a hab hbc)).hom.app (level a)

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- Restrict any coefficient sheaf by its actual inverse image along the scheme map.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev adicTowerInverseImage := proEtaleSheafInverseImage g CommRingCat.{u + 1}

/-- Exact derived inverse image with exactly the inverse-image coefficient sheaf.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev adicTowerPullback (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedPullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _)

/-- The local reduction of a common completed-coefficient complex, retaining the
inverse image of the completed ring rather than completing again after restriction.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def adicTowerLocalReduction
    (L : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ) (n : ℕ) :=
  (pbcDerivedExtend ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).obj
    (DerivedCategory.Q.obj L)

/-- The canonical semilinear transition of the local reduction model. It is the adjunct
of the balancing normalization N_b⊗ᴸR_a≅N_a, as specified by the coefficient datum.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def adicTowerLocalTransition
    (L : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ)
    (b a : ℕ) (hab : a ≤ b) :
    adicTowerLocalReduction d g L b ⟶
      (pbcDerivedRestrict ((adicTowerInverseImage g).map
        (pbcAdicQuotient X d b a hab))).obj (adicTowerLocalReduction d g L a) :=
  pbcReductionTransition
    ((adicTowerInverseImage g).map (pbcAdicProjection X d b))
    ((adicTowerInverseImage g).map (pbcAdicQuotient X d b a hab))
    ((adicTowerInverseImage g).map (pbcAdicProjection X d a))
    (((adicTowerInverseImage g).map_comp _ _).symm.trans
      (congrArg (adicTowerInverseImage g).map (pbcAdicProjection_comp X d b a hab)))
    (DerivedCategory.Q.obj L)

/-- Restriction of semilinear transitions, using the existing canonical comparison for
exact inverse image and scalar restriction. It is the mate of identity on sections,
so no arbitrary map or coefficient identification occurs.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def adicTowerRestrictedTransition (M : AdicTower X d) (b a : ℕ) (hab : a ≤ b) :
    (adicTowerPullback g ((pbcAdicRings X d).obj (op b))).obj (M.level b) ⟶
      (pbcDerivedRestrict ((adicTowerInverseImage g).map
        (pbcAdicQuotient X d b a hab))).obj
          ((adicTowerPullback g ((pbcAdicRings X d).obj (op a))).obj (M.level a)) :=
  (adicTowerPullback g ((pbcAdicRings X d).obj (op b))).map
      (adicTowerSemilinearTransition X d M.level M.normalization b a hab) ≫
    (proEtaleRingRestrictionDerivedPullback g
      ((pbcAdicRings X d).obj (op b)) ((pbcAdicRings X d).obj (op a))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op b)))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op a)))
      (pbcAdicQuotient X d b a hab)
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d b a hab))
      (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).inv.app (M.level a)

/-- A common local bounded model with adic-lisse finite-type terms, finite-lisse
cohomology in every finite reduction, and compatible quotient-linear identifications.
The compatibility equation is the adjoint form of e_aρ=σ(Le_b); scalar-extension Hom
bijections make it equivalent to the blueprint's equation.
Source: blueprint order 1250; Stacks Tags 09AI and 09BT
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
structure AdicTowerLocalModel (M : AdicTower X d) (d₀ d₁ : ℤ) where
  /-- One complex over the restricted completed coefficients, independent of the level. -/
  complex : CochainComplex (pbcModules Y
    ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ
  /-- A uniform termwise window, rather than just cohomological bounds. -/
  bounded : ∀ q : ℤ, (q < d₀ ∨ d₁ < q) → IsZero (complex.X q)
  /-- Terms are completed adic-lisse modules of finite type, without a finite-set condition. -/
  adicLisse : ∀ q : ℤ,
    @IsRelativelyAdicLisseModule _ _ g A _ d.noetherian d.ideal
      ((pbcRestrict ((adicTowerInverseImage g).map
        (pbcCompletedComparison X d).hom)).obj (complex.X q))
  /-- Every cohomology sheaf at every finite level is locally a finite constant module. -/
  finiteLisse : ∀ (n : ℕ) (q : ℤ),
    IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage g).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj (adicTowerLocalReduction d g complex n)))
  /-- The level identifications are linear over the inverse-image finite coefficient ring. -/
  identification : ∀ n : ℕ,
    (adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n) ≅
      adicTowerLocalReduction d g complex n
  /-- Every reduction agrees with the normalization of the same common local model. -/
  compatible : ∀ (b a : ℕ) (hab : a ≤ b),
    adicTowerRestrictedTransition d g M b a hab ≫
        (pbcDerivedRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d b a hab))).map (identification a).hom =
      (identification b).hom ≫ adicTowerLocalTransition d g complex b a hab

/-- Uniformly bounded constructibility means one window and one finite locally closed
stratification, with a pro-etale cover on each stratum carrying common local models.
The coefficient restrictions are along the composite of the stratum immersion and the
covering morphism. The finite-lisse cohomology covers can depend on both level and degree.
Source: blueprint order 1250; Stacks Tags 09AI and 09BT
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
def IsUniformlyBoundedConstructibleAdicTower (M : AdicTower X d) : Prop :=
  ∃ (d₀ d₁ : ℤ), d₀ ≤ d₁ ∧ ∃ S : LocallyClosedStratification X,
    ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
      V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
      ∀ (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt), V f →
        Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion α) M d₀ d₁)

end AlgebraicGeometry.Scheme
