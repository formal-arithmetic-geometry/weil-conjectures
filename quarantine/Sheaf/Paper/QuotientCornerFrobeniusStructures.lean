/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Frobenius on quotient-coefficient corners and their strict completions

Source: blueprint main-20261015, sec-proper-base-change/sk-prop-pbc-complete,
lemma-weil-pbc-completed-map-reduction.proof.md, paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).

The quotient diagram is a ringed sequence site. All derived categories localize complexes
of strict systems, before evaluating. Restriction retains the completed coefficient action.

## Main definitions

- `QuotientFrobenius.WeilDatum`: the coherent strict quotient-diagram Weil input.
- `QuotientFrobenius.quotientCornerFrobeniusStructures`: all finite, strict and completed
  corner structures and their completed source and target reductions.
- `QuotientFrobenius.finite_formulas` and `QuotientFrobenius.towerTheta_evaluation`:
  the finite blueprint formulas and their compatibility with ambient scalar restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme
namespace QuotientFrobenius


/-- The original small pro-etale site keeps its actual object and morphism universes.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance (priority := 2000) baseSmall (T : Scheme.{t}) : EssentiallySmall.{t + 1} T.ProEt :=
  essentiallySmallSelf.{0} T.ProEt

/-- Abelian sheafification in the original finite-coefficient universe.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance (priority := 2100) baseSheafify (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  @SemilinearSections.abelianSheafify.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} _) _

/-- The locally bijective sheafification criterion in the same finite-coefficient universe.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance (priority := 2100) baseLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  @SemilinearSections.locallyBijective.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} _) _

/-- The vertical sequence site is small in the same coefficient universe.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance (priority := 2000) sequenceSiteSmall (T : Scheme.{t}) :
    EssentiallySmall.{t + 1} (ℕ × T.ProEt) := essentiallySmallSelf.{0} _

/-- Sheafification in the fixed coefficient universe of the quotient diagram site.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance (priority := 2100) sequenceSheafify (T : Scheme.{t}) :
    HasSheafify (coefficientSequenceTopology (ProEt.topology T)) AddCommGrpCat.{t + 1} :=
  @SemilinearSections.abelianSheafify.{t + 1, t, t + 1} (ℕ × T.ProEt) _
    (essentiallySmallSelf.{0} _) _

/-- The coefficient-sized local bijectivity criterion on the quotient diagram site.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance (priority := 2100) sequenceLocallyBijective (T : Scheme.{t}) :
    (coefficientSequenceTopology (ProEt.topology T)).WEqualsLocallyBijective
      AddCommGrpCat.{t + 1} :=
  @SemilinearSections.locallyBijective.{t + 1, t, t + 1} (ℕ × T.ProEt) _
    (essentiallySmallSelf.{0} _) _

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The actual finite quotient transitions, with index n representing exponent n+1.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev transition (T : Scheme.{t}) (n : ℕ) :=
  (reductionCoefficientSystem T d).map (homOfLE (Nat.le_succ n)).op

/-- Q_T is the ring of finite quotient sheaves on the strict sequence site.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev quotientRing (T : Scheme.{t}) :
    Sheaf (coefficientSequenceTopology (ProEt.topology T)) CommRingCat.{t + 1} :=
  @SemilinearSections.systemRing.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- Strict semilinear quotient systems; this is not a diagram category of derived objects.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev modules (T : Scheme.{t}) : Type (t + 2) :=
  @SemilinearSections.Systems.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- The ordinary unbounded derived category on the ringed quotient diagram site.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev derived (T : Scheme.{t}) : Type (t + 2) :=
  @SemilinearSections.DS.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- Exact quotient-linear evaluation, including the positive-level convention.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev evaluation (T : Scheme.{t}) (n : ℕ) :=
  @SemilinearSections.e.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T) n

/-- Base change on the vertical sequence sites, acting identically on the index.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev siteMap {U V : Scheme.{t}} (u : U ⟶ V) :=
  (𝟭 ℕ).prod (proEtaleBaseChange u)

/-- Vertical covers are preserved by base change.
Source: Stacks 09A5, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: a cover restricts to a cover on its vertical slice; base change preserves these
pro-etale covering sieves, independently at every positive index. -/
theorem siteMap_continuous {U V : Scheme.{t}} (u : U ⟶ V) :
    (siteMap u).IsContinuous (coefficientSequenceTopology (ProEt.topology V))
      (coefficientSequenceTopology (ProEt.topology U)) := by
  sorry

attribute [instance] siteMap_continuous

/-- The vertical slice of the strict ring is the specified finite coefficient sheaf.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: the system-ring construction is the uncurry of the quotient sequence, whose
object at n is the given finite coefficient sheaf; forgetting commutativity changes no data. -/
theorem quotientRing_obj (T : Scheme.{t}) (W : (ℕ × T.ProEt)ᵒᵖ) :
    (quotientRing d T).obj.obj W = (d.finiteRing T W.unop.1).obj.obj (op W.unop.2) := by
  sorry

/-- Direct image and the quotient site have the same target section ring.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: direct image is precomposition with base change; siteMap fixes the index.
Evaluate the uncurry formula for the system ring at the base-changed object. -/
theorem coefficientTarget_obj {U V : Scheme.{t}} (u : U ⟶ V)
    (W : (ℕ × V.ProEt)ᵒᵖ) :
    (((proEtaleSheafDirectImage u CommRingCat.{t + 1}).obj
      (d.finiteRing U W.unop.1)).obj.obj (op W.unop.2)) =
      (quotientRing d U).obj.obj ((siteMap u).op.obj W) := by
  sorry

/-- Section component of the structural coefficient map, with explicit slice identifications.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def coefficientComponent {U V : Scheme.{t}} (u : U ⟶ V) (W : (ℕ × V.ProEt)ᵒᵖ) :
    (quotientRing d V).obj.obj W ⟶ (quotientRing d U).obj.obj ((siteMap u).op.obj W) :=
  eqToHom (quotientRing_obj d V W) ≫
    (proEtaleRingDirectImageMap u (d.finiteRing V W.unop.1)
      (d.finiteRing U W.unop.1) (d.finiteRingIso u W.unop.1)).hom.app (op W.unop.2) ≫
    eqToHom (coefficientTarget_obj d u W)

/-- Constant-section coefficient maps commute with horizontal quotient restrictions.
Source: Stacks 098T, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: at fixed index use naturality of the constant-section adjunct. Naturality in
finite ring maps gives horizontal compatibility. Factor a product-site arrow into
horizontal and vertical arrows and compose their naturality equations. -/
theorem coefficient_naturality {U V : Scheme.{t}} (u : U ⟶ V)
    {M N : (ℕ × V.ProEt)ᵒᵖ} (a : M ⟶ N) :
    (quotientRing d V).obj.map a ≫ coefficientComponent d u N =
      coefficientComponent d u M ≫ (quotientRing d U).obj.map ((siteMap u).op.map a) := by
  sorry

/-- The ring-system map uses the specified finite adjunct at every index and section.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def coefficientMap {U V : Scheme.{t}} (u : U ⟶ V) :
    SemilinearSections.ring.{t + 1, t, t + 1} _ (quotientRing d V) ⟶
      ((siteMap u).sheafPushforwardContinuous RingCat.{t + 1}
        (coefficientSequenceTopology (ProEt.topology V))
        (coefficientSequenceTopology (ProEt.topology U))).obj
          (SemilinearSections.ring.{t + 1, t, t + 1} _ (quotientRing d U)) where
  hom := Functor.whiskerRight
    ({ app := fun W ↦ coefficientComponent d u W
       naturality := fun _ _ a ↦ coefficient_naturality d u a } :
      (quotientRing d V).obj ⟶ (siteMap u).op ⋙ (quotientRing d U).obj)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})

/-- Sectionwise direct image on the quotient ringed sequence site.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev modulePush {U V : Scheme.{t}} (u : U ⟶ V) : modules d U ⥤ modules d V :=
  SheafOfModules.pushforward.{t + 1} (F := siteMap u) (coefficientMap d u)

/-- Direct image is additive because it retains section maps and module addition.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: all component maps are the original additive maps on base-changed sections.
Thus direct image preserves sums and zero morphisms. -/
theorem modulePush_additive {U V : Scheme.{t}} (u : U ⟶ V) :
    (modulePush d u).Additive := by
  sorry

attribute [instance] modulePush_additive

/-- The tensor-formula module pullback exists on the small quotient diagram sites.
Source: Stacks 03D3, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: left Kan extension of module presheaves followed by sheafification gives the left
adjoint of the displayed sectionwise direct image. Its Hom correspondence is precisely
inverse image followed by extension along the constant-section coefficient identification. -/
theorem modulePush_isRightAdjoint {U V : Scheme.{t}} (u : U ⟶ V) :
    (modulePush d u).IsRightAdjoint := by
  sorry

attribute [instance] modulePush_isRightAdjoint

/-- Ordinary tensor pullback, fixed by the universal adjunction to actual direct image.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev modulePull {U V : Scheme.{t}} (u : U ⟶ V) : modules d V ⥤ modules d U :=
  (modulePush d u).leftAdjoint

/-- The actual module adjunction, with the ordinary direct image fixed on sections.
Source: blueprint paragraph 4; Stacks 03D3
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def moduleAdjunction {U V : Scheme.{t}} (u : U ⟶ V) : modulePull d u ⊣ modulePush d u :=
  Adjunction.ofIsRightAdjoint (modulePush d u)

/-- Identified-coefficient inverse image is exact on the strict quotient diagram.
Source: blueprint paragraph 4; Stacks 03D3
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: evaluate ordinary module pullback at each vertical slice. Its coefficient map is
c_{u,n}, an isomorphism, so it is exact inverse image. Kernels and cokernels of systems
are computed on these slices by lem-coef-semilinear-derived-sections. -/
theorem modulePull_exact {U V : Scheme.{t}} (u : U ⟶ V) :
    (modulePull d u).Additive ∧ PreservesFiniteLimits (modulePull d u) ∧
      PreservesFiniteColimits (modulePull d u) := by
  sorry

/-- Additivity of quotient-diagram inverse image. Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance modulePull_additive {U V : Scheme.{t}} (u : U ⟶ V) :
    (modulePull d u).Additive := (modulePull_exact d u).1

/-- Left exactness of quotient-diagram inverse image. Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance modulePull_limits {U V : Scheme.{t}} (u : U ⟶ V) :
    PreservesFiniteLimits (modulePull d u) := (modulePull_exact d u).2.1

/-- Right exactness of quotient-diagram inverse image. Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance modulePull_colimits {U V : Scheme.{t}} (u : U ⟶ V) :
    PreservesFiniteColimits (modulePull d u) := (modulePull_exact d u).2.2

/-- Grothendieck abelianness on the actual quotient diagram site.
Source: lem-coef-semilinear-derived-sections; blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance modules_grothendieck (T : Scheme.{t}) :
    IsGrothendieckAbelian.{t + 1} (modules d T) :=
  (@SemilinearSections.semilinearDerivedSections.{t + 1, t, t + 1}
    T.ProEt _ (ProEt.topology T) (essentiallySmallSelf.{0} T.ProEt)
      (d.finiteRing T) (transition d T)).some.systems.grothendieck

/-- K-injective resolutions in the actual quotient-system abelian category.
Source: lem-coef-semilinear-derived-sections, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: the strict semilinear system category is Grothendieck abelian, hence has
K-injective resolutions of all unbounded complexes. -/
theorem modules_kinjective (T : Scheme.{t}) :
    Abelian.HasKInjectiveResolutions (modules d T) := by
  sorry

attribute [instance] modules_kinjective

/-- Total left derived pullback; exactness identifies it with termwise inverse image.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev pull {U V : Scheme.{t}} (u : U ⟶ V) : derived d V ⥤ derived d U :=
  (modulePull d u).mapDerivedCategory

/-- K-injective total direct image on the category of strict quotient systems.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev push {U V : Scheme.{t}} (u : U ⟶ V) : derived d U ⥤ derived d V :=
  (modulePush d u).rightDerivedFunctor

/-- The canonical module adjunction, derived before any evaluation.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def adjunction {U V : Scheme.{t}} (u : U ⟶ V) : pull d u ⊣ push d u :=
  (moduleAdjunction d u).mapDerivedCategoryRightDerivedAdjunction

/-- Direct-image composition is fixed by fibre-product pasting at every index and section.
Source: blueprint paragraph 4; Stacks 03D8
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: use the canonical pasting map of base-changed site objects, with identity in the
index direction. Naturality of the finite coefficient adjuncts makes it linear. Its
inverse is the inverse pasting map; sectionwise extensionality gives uniqueness. -/
theorem modulePushComp_exists {U V W : Scheme.{t}} (u : U ⟶ V) (v : V ⟶ W) :
    ∃! e : modulePush d u ⋙ modulePush d v ≅ modulePush d (u ≫ v),
      ∀ (N : modules d U) (n : ℕ) (Z : W.ProEt)
        (m : ((modulePush d u ⋙ modulePush d v).obj N).val.obj (op (n, Z))),
        HEq ((e.hom.app N).val.app (op (n, Z)) m)
          (N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) u v).hom.app
              Z)).op m) := by
  sorry

/-- Ordinary pullback composition is the conjugate of the specified sectionwise pasting.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def modulePullComp {U V W : Scheme.{t}} (u : U ⟶ V) (v : V ⟶ W) :
    modulePull d (u ≫ v) ≅ modulePull d v ⋙ modulePull d u :=
  (conjugateIsoEquiv
    ((moduleAdjunction d v).comp
      (moduleAdjunction d u))
    (moduleAdjunction d (u ≫ v))).symm
      (modulePushComp_exists d u v).exists.choose

/-- Derived composition is the localization of the ordinary tensor associator.
Since pullback is exact, this also gives its K-flat flat-term normalization.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def pullComp {U V W : Scheme.{t}} (u : U ⟶ V) (v : V ⟶ W) :
    pull d (u ≫ v) ≅ pull d v ⋙ pull d u :=
  Functor.mapDerivedCategoryNatIso (modulePullComp d u v) ≪≫
    Functor.mapDerivedCategoryCompIso (modulePull d v) (modulePull d u)

/-- The Frobenius face comparison, directed Phi_U Lu* to Lu* Phi_V.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def kappa {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :
    pull d u ⋙ pull d FU.hom ≅ pull d FV.hom ⋙ pull d u :=
  (pullComp d FU.hom u).symm ≪≫
    eqToIso (congrArg (fun a ↦ pull d a) comm) ≪≫ pullComp d u FV.hom

/-- Exchange along a Frobenius face is the adjunction mate of kappa inverse.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def beta {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :
    push d u ⋙ pull d FV.hom ⟶ pull d FU.hom ⋙ push d u :=
  mateEquiv (adjunction d u) (adjunction d u) (kappa d u FU FV comm).inv

/-- A constant coefficient presheaf is a sheaf on the vertical sequence site.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: glue in the completed ring sheaf on the vertical slice. The restrictions in the
index direction are identities, so uniqueness of gluing gives horizontal compatibility. -/
theorem diagonalRing_isSheaf (T : Scheme.{t}) :
    Presheaf.IsSheaf (coefficientSequenceTopology (ProEt.topology T))
      ((CategoryTheory.Prod.snd ℕ T.ProEt).op ⋙ (d.completedRing T).obj) := by
  sorry

/-- The completed-coefficient diagonal ring on the same vertical sequence site.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def diagonalRing (T : Scheme.{t}) :
    Sheaf (coefficientSequenceTopology (ProEt.topology T)) CommRingCat.{t + 1} :=
  ⟨(CategoryTheory.Prod.snd ℕ T.ProEt).op ⋙ (d.completedRing T).obj,
    diagonalRing_isSheaf d T⟩

/-- The projection component uses the fixed vertical-slice identification.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def diagonalProjectionComponent (T : Scheme.{t}) (W : (ℕ × T.ProEt)ᵒᵖ) :
    (diagonalRing d T).obj.obj W ⟶ (quotientRing d T).obj.obj W :=
  (d.projection T W.unop.1).hom.app (op W.unop.2) ≫
    eqToHom (quotientRing_obj d T W).symm

/-- The coefficient projections are natural on the strict diagram site.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: vertical naturality is that of the projection; horizontal naturality is the
limit cone equation. Factor every product-site arrow into these two kinds. -/
theorem diagonalProjection_naturality (T : Scheme.{t})
    {M N : (ℕ × T.ProEt)ᵒᵖ} (a : M ⟶ N) :
    (diagonalRing d T).obj.map a ≫ diagonalProjectionComponent d T N =
      diagonalProjectionComponent d T M ≫ (quotientRing d T).obj.map a := by
  sorry

/-- The actual scalar map retaining all coefficient projections.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def diagonalProjection (T : Scheme.{t}) : diagonalRing d T ⟶ quotientRing d T where
  hom :=
    { app := fun W ↦ diagonalProjectionComponent d T W
      naturality := fun _ _ a ↦ diagonalProjection_naturality d T a }

/-- Projection to the original site is continuous for vertical covers.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: a sheaf on the original site, made constant in the index, glues independently on
every vertical slice. This is the continuous-functor sheaf criterion. -/
theorem diagonal_continuous (T : Scheme.{t}) :
    (CategoryTheory.Prod.snd ℕ T.ProEt).IsContinuous
      (coefficientSequenceTopology (ProEt.topology T))
      (ProEt.topology T) := by
  sorry

attribute [instance] diagonal_continuous

/-- The exact diagonal module functor, implemented by its sectionwise pullback presheaf.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev diagonal (T : Scheme.{t}) :
    proEtaleRingModules T (d.completedRing T) ⥤
      SemilinearSections.Mod.{t + 1, t, t + 1} (coefficientSequenceTopology (ProEt.topology T))
        (diagonalRing d T) :=
  SheafOfModules.pushforward.{t + 1} (F := CategoryTheory.Prod.snd ℕ T.ProEt) (𝟙 _)

/-- Diagonal retains addition of module maps on every section.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: its section maps are the original maps, independently of the index, so they
preserve sums of morphisms and the zero morphism. -/
theorem diagonal_additive (T : Scheme.{t}) : (diagonal d T).Additive := by
  sorry

attribute [instance] diagonal_additive

/-- Diagonal is exact, since its restriction to every slice is identity.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: kernels, cokernels and addition on the sequence site are computed on vertical
slices; diagonal restricts to identity on each slice. -/
theorem diagonal_exact (T : Scheme.{t}) :
    PreservesFiniteLimits (diagonal d T) ∧ PreservesFiniteColimits (diagonal d T) := by
  sorry

/-- Left exactness of diagonal. Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance diagonal_limits (T : Scheme.{t}) : PreservesFiniteLimits (diagonal d T) :=
  (diagonal_exact d T).1

/-- Right exactness of diagonal. Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance diagonal_colimits (T : Scheme.{t}) : PreservesFiniteColimits (diagonal d T) :=
  (diagonal_exact d T).2

/-- The universal K-flat scalar-extension pair for Delta A_T to Q_T. Its ordinary
functor is the sheafified tensor and its derived pair is fixed by the universal counit.
Source: Stacks 06YY, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def scalarModel (T : Scheme.{t}) :=
  (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{t + 1, t, t + 1, t + 2, t + 2}
    (diagonalProjection d T)).some

/-- Additivity of the fixed ordinary scalar-extension functor in the universal pair.
Source: Stacks 06YY, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance scalarModel_additive (T : Scheme.{t}) : (scalarModel d T).E.Additive :=
  (scalarModel d T).additive

/-- The actual strict quotient reduction of K: diagonal followed by derived extension.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev reduction (T : Scheme.{t}) : d.derived T ⥤ derived d T :=
  (diagonal d T).mapDerivedCategory ⋙ (scalarModel d T).T

/-- Restriction along Delta A_T to Q_T, followed by the normalized diagram realization.
Source: blueprint paragraph 4; Stacks 03CZ
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: at index n restrict the action through pi_n. The limit cone equations make all
horizontal restrictions A_T-linear. Retain the original horizontal restrictions and all
component maps of morphisms. Their presheaf laws give the tower and functor laws.
Extensionality on objects and section maps proves uniqueness. -/
theorem moduleRestriction_exists (T : Scheme.{t}) :
    ∃! R : modules d T ⥤ d.towers T,
      (∀ (M : modules d T) (n : ℕ),
        (R.obj M).obj (op n) = (reductionRestrict T (d.projection T n)).obj
          ((SemilinearSections.evaluation.{t + 1, t, t + 1}
            (ProEt.topology T) (d.finiteRing T) (transition d T) n).obj M)) ∧
      (∀ (M : modules d T) (m n : ℕ) (h : n ≤ m) (U : T.ProEtᵒᵖ),
        HEq (fun x ↦ (((R.obj M).map (homOfLE h).op).val.app U) x)
          (fun x : M.val.obj (op (m, U.unop)) ↦
            M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)) ∧
      (∀ {M N : modules d T} (a : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ),
        HEq (fun x ↦ (((R.map a).app (op n)).val.app U) x)
          (fun x : M.val.obj (op (n, U.unop)) ↦ a.val.app (op (n, U.unop)) x)) := by
  sorry

/-- The unique actual strict scalar restriction with the prescribed section maps.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def moduleRestriction (T : Scheme.{t}) : modules d T ⥤ d.towers T :=
  (moduleRestriction_exists d T).exists.choose

/-- Scalar restriction is additive and exact on the strict system category.
Source: blueprint paragraph 4; Stacks 03CZ
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: the underlying abelian sheaves and every transition are unchanged. Componentwise
kernels and cokernels in the two system categories are therefore preserved. -/
theorem moduleRestriction_exact (T : Scheme.{t}) :
    (moduleRestriction d T).Additive ∧ PreservesFiniteLimits (moduleRestriction d T) ∧
      PreservesFiniteColimits (moduleRestriction d T) := by
  sorry

/-- Additive scalar restriction. Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance moduleRestriction_additive (T : Scheme.{t}) : (moduleRestriction d T).Additive :=
  (moduleRestriction_exact d T).1

/-- Left exact scalar restriction. Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance moduleRestriction_limits (T : Scheme.{t}) :
    PreservesFiniteLimits (moduleRestriction d T) := (moduleRestriction_exact d T).2.1

/-- Right exact scalar restriction. Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
instance moduleRestriction_colimits (T : Scheme.{t}) :
    PreservesFiniteColimits (moduleRestriction d T) := (moduleRestriction_exact d T).2.2

/-- Derived strict scalar restriction, rather than forgetting to a family of objects.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev restriction (T : Scheme.{t}) : derived d T ⥤ DerivedCategory (d.towers T) :=
  (moduleRestriction d T).mapDerivedCategory

/-- Ordinary restriction/direct-image comparison is identity on every section and index.
Source: blueprint paragraph 4; Stacks 0D6E
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: both functors use the same base-changed sections and original horizontal
restrictions. Their completed actions agree by compatibility of c_u with pi_n.
Identity section maps are therefore linear, natural, invertible and unique. -/
theorem moduleRestrictionPush_exists {U V : Scheme.{t}} (u : U ⟶ V) :
    ∃! e : modulePush d u ⋙ moduleRestriction d V ≅
        moduleRestriction d U ⋙ d.towerModulePush u,
      ∀ (M : modules d U) (n : ℕ) (Z : V.ProEtᵒᵖ),
        HEq (fun x ↦ (((e.hom.app M).app (op n)).val.app Z) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange u).obj Z.unop)) ↦ x) := by
  sorry

/-- The section-normalized restriction/direct-image comparison before deriving.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def moduleRestrictionPush {U V : Scheme.{t}} (u : U ⟶ V) :=
  (moduleRestrictionPush_exists d u).exists.choose

/-- Restriction/pullback comparison fixed by the unit of the actual module adjunction.
Source: blueprint paragraph 4; Stacks 0D6D
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: both sides are the same inverse-image sheaf with its A_U-action restricted.
The tensor-unit identification gives their isomorphism. Transpose its section identity
under the displayed module adjunctions to obtain the unit equation. That equation
uniquely determines the comparison by the adjunction Hom bijection. -/
theorem moduleRestrictionPull_exists {U V : Scheme.{t}} (u : U ⟶ V) :
    ∃! e : modulePull d u ⋙ moduleRestriction d U ≅
        moduleRestriction d V ⋙ d.towerModulePull u,
      ∀ M : modules d V,
        (moduleRestriction d V).map
            ((moduleAdjunction d u).unit.app M) ≫
          (moduleRestrictionPush d u).hom.app ((modulePull d u).obj M) ≫
          (d.towerModulePush u).map (e.hom.app M) =
            (d.towerModuleAdjunction u).unit.app ((moduleRestriction d V).obj M) := by
  sorry

/-- Exact descent of the normalized ordinary restriction/pullback isomorphism.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def restrictionPull {U V : Scheme.{t}} (u : U ⟶ V) :
    pull d u ⋙ restriction d U ≅ restriction d V ⋙ d.towerPull u :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleRestrictionPull_exists d u).exists.choose ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Comparison of quotient and ambient derived direct image, normalized by universal units.
Source: blueprint paragraph 4; Stacks 0D6E
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: the ordinary comparison is the identity on sections. Derive the two factorizations
of the same ringed diagram morphism, first through Q and first through Delta A. The
composition theorem gives the comparison with the displayed universal-unit equation.
Resolving the input on the quotient diagram site determines it uniquely. Restriction is
exact; no assertion that evaluation of a K-injective system is K-injective is used. -/
theorem restrictionPush_exists {U V : Scheme.{t}} (u : U ⟶ V) :
    ∃! e : push d u ⋙ restriction d V ≅ restriction d U ⋙ d.towerPush u,
      ∀ C : CochainComplex (modules d U) ℤ,
        (restriction d V).map
            ((DerivedCategory.quotientCompQhIso _).inv.app _ ≫
              (modulePush d u).rightDerivedFunctorUnit.app
                ((HomotopyCategory.quotient _ _).obj C) ≫
              (push d u).map ((DerivedCategory.quotientCompQhIso _).hom.app C)) ≫
          e.hom.app (DerivedCategory.Q.obj C) =
        (moduleRestriction d V).mapDerivedCategoryFactors.hom.app
            (((modulePush d u).mapHomologicalComplex (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (moduleRestrictionPush d u) (.up ℤ)).hom.app C) ≫
          exchangeTowerDerivedUnit u (d.completedRing V) (d.completedRing U)
            (d.integralRingIso u)
            (((moduleRestriction d U).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (d.towerPush u).map ((moduleRestriction d U).mapDerivedCategoryFactors.inv.app C) := by
  sorry

/-- The canonical derived restriction/direct-image comparison with its unit normalization.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def restrictionPush {U V : Scheme.{t}} (u : U ⟶ V) :
    push d u ⋙ restriction d V ≅ restriction d U ⋙ d.towerPush u :=
  (restrictionPush_exists d u).exists.choose

/-- The representative counit of strict quotient reduction, retaining its tensor construction.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def reductionCounit (T : Scheme.{t}) (P : CochainComplex (proEtaleRingModules T
    (d.completedRing T)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((((diagonal d T) ⋙ (scalarModel d T).E).mapHomologicalComplex (.up ℤ)).obj P) :=
  (scalarModel d T).T.map ((diagonal d T).mapDerivedCategoryFactors.hom.app P) ≫
    (scalarModel d T).ε.app (((diagonal d T).mapHomologicalComplex (.up ℤ)).obj P)

/-- The ordinary quotient diagram reduction has exactly the published restricted tower.
Source: blueprint paragraph 4; Stacks 06YY
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: the scalar-model object identification gives the sheafification of ordinary tensor
on the sequence site. Its restriction to (n,U) is M tensor P_n. Send each generator
1 tensor x to the same generator in the published reduction construction. Extend by
linearity and sheafification. The quotient transitions and module maps commute on
these generators, giving the natural tower comparison. Generators determine it uniquely. -/
theorem ordinaryReductionRestriction_exists (T : Scheme.{t}) :
    ∃! e : ((diagonal d T ⋙ (scalarModel d T).E) ⋙ moduleRestriction d T) ≅
        completedReductionModuleTowerFunctor T d,
      ∀ (M : proEtaleRingModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U)
        (z : (((diagonal d T ⋙ (scalarModel d T).E) ⋙ moduleRestriction d T).obj M).obj
          (op n) |>.val.obj U),
        HEq z ((eqToHom ((scalarModel d T).obj_eq ((diagonal d T).obj M)).symm).val.app
          (op (n, U.unop))
          (SemilinearSections.extensionUnit (diagonalProjection d T)
            ((diagonal d T).obj M) (op (n, U.unop)) x)) →
        HEq (((e.hom.app M).app (op n)).val.app U z)
          (reductionTensorSection T (d.projection T n) M U 1 x) := by
  sorry

/-- The restricted reduction comparison is fixed on one strict K-flat representative.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: diagonal preserves flat-term K-flat complexes, and the universal scalar counit
computes their strict quotient tensors. Apply the ordinary comparison above before
localizing. Its naturality and the two universal counits give the displayed equation.
Every object has such a resolution, so the equation extends the comparison uniquely and
makes it invertible. This specifies the whole diagram, not just its evaluations. -/
theorem reductionRestriction_exists (T : Scheme.{t}) :
    ∃! e : reduction d T ⋙ restriction d T ≅ completedReductionTower T d,
      ∀ P : CochainComplex (proEtaleRingModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (restriction d T).map (reductionCounit d T P) ≫
            (moduleRestriction d T).mapDerivedCategoryFactors.hom.app
              ((((diagonal d T ⋙ (scalarModel d T).E).mapHomologicalComplex (.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (ordinaryReductionRestriction_exists d T).exists.choose (.up ℤ)).hom.app P) =
          e.hom.app (DerivedCategory.Q.obj P) ≫ completedReductionTowerComplexCounit T d P := by
  sorry

/-- The unique strict reduction identification, with its universal-counit normalization.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def reductionRestriction (T : Scheme.{t}) :
    reduction d T ⋙ restriction d T ≅ completedReductionTower T d :=
  (reductionRestriction_exists d T).exists.choose

/-- Underived evaluation on the strict quotient module category.
Source: Zheng 4.1, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev moduleEvaluation (T : Scheme.{t}) (n : ℕ) :=
  @SemilinearSections.evaluation.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T) n

/-- Evaluation/direct-image comparison fixed on all ordinary component carriers.
Source: lem-coef-semilinear-derived-sections, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: both functors take the original sections at (n,baseChange U), with the same
finite scalar action. Identity functions define the comparison and its inverse;
linearity and naturality follow from the constant-section adjunct. Sections determine it. -/
theorem moduleEvaluationPush_exists {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    ∃! e : modulePush d u ⋙ moduleEvaluation d V n ≅
        moduleEvaluation d U n ⋙ proEtaleRingModuleDirectImage u
          (d.finiteRing V n) (d.finiteRing U n) (d.finiteRingIso u n),
      ∀ (M : modules d U) (Z : V.ProEtᵒᵖ),
        HEq (fun x ↦ (e.hom.app M).val.app Z x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange u).obj Z.unop)) ↦ x) := by
  sorry

/-- The normalized ordinary evaluation of direct image.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def moduleEvaluationPush {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :=
  (moduleEvaluationPush_exists d u n).exists.choose

/-- Evaluation/pullback is fixed by the tensor-unit adjunction equation.
Source: lem-coef-semilinear-derived-sections, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: inverse image and scalar extension evaluate on each vertical slice. The
identity tensor-unit comparison is adjoint to the preceding ordinary direct-image
comparison. The adjunction Hom bijections determine it uniquely; exact inverse image
and its inverse coefficient identifications make it invertible. -/
theorem moduleEvaluationPull_exists {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    ∃! e : modulePull d u ⋙ moduleEvaluation d U n ≅
        moduleEvaluation d V n ⋙ proEtaleRingModulePullback u
          (d.finiteRing V n) (d.finiteRing U n) (d.finiteRingIso u n),
      ∀ M : modules d V,
        (moduleEvaluation d V n).map
            ((moduleAdjunction d u).unit.app M) ≫
          (moduleEvaluationPush d u n).hom.app ((modulePull d u).obj M) ≫
          (proEtaleRingModuleDirectImage u (d.finiteRing V n) (d.finiteRing U n)
            (d.finiteRingIso u n)).map (e.hom.app M) =
          (proEtaleRingModuleAdjunction u (d.finiteRing V n) (d.finiteRing U n)
            (d.finiteRingIso u n)).unit.app ((moduleEvaluation d V n).obj M) := by
  sorry

/-- Exact descent of the unit-normalized evaluation/pullback comparison.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def evaluationPull {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    pull d u ⋙ evaluation d U n ≅ evaluation d V n ⋙ d.finitePull u n :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleEvaluationPull_exists d u n).exists.choose ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The cochain universal unit of quotient direct image.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def pushUnit {U V : Scheme.{t}} (u : U ⟶ V) (P : CochainComplex (modules d U) ℤ) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((modulePush d u).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (modulePush d u).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    (push d u).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- The finite direct-image cochain unit, before any evaluation of a resolution.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finitePushUnit {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ)
    (P : CochainComplex (proEtaleRingModules U (d.finiteRing U n)) ℤ) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((proEtaleRingModuleDirectImage u (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso u n)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (proEtaleRingModuleDirectImage u (d.finiteRing V n) (d.finiteRing U n)
      (d.finiteRingIso u n)).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj P) ≫
    (d.finitePush u n).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- The finite-linear derived evaluation comparison retains its universal-unit equation.
Source: lem-coef-semilinear-derived-sections, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: apply the semilinear derived-sections comparison to the actual quotient ring
sequence and constant-section coefficient identifications. Its ordinary comparison is
moduleEvaluationPush. The two factorizations of the ringed diagram morphism give the
same universal right-derived pair; the displayed unit equation uniquely identifies
them. No claim that evaluation preserves quotient-system K-injectives is needed. -/
theorem evaluationPush_exists {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    ∃! e : push d u ⋙ evaluation d V n ≅ evaluation d U n ⋙ d.finitePush u n,
      ∀ P : CochainComplex (modules d U) ℤ,
        (evaluation d V n).map (pushUnit d u P) ≫ e.hom.app (DerivedCategory.Q.obj P) =
          (moduleEvaluation d V n).mapDerivedCategoryFactors.hom.app
            (((modulePush d u).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (moduleEvaluationPush d u n) (.up ℤ)).hom.app P) ≫
          finitePushUnit d u n
            (((moduleEvaluation d U n).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (d.finitePush u n).map ((moduleEvaluation d U n).mapDerivedCategoryFactors.inv.app
            P) := by
  sorry

/-- The canonical finite-linear evaluation of total direct image.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def evaluationPush {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    push d u ⋙ evaluation d V n ≅ evaluation d U n ⋙ d.finitePush u n :=
  (evaluationPush_exists d u n).exists.choose

/-- Evaluation of ordinary strict quotient reduction, specified on pure tensor generators.
Source: Stacks 06YY, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: evaluation of sheafified extension on the sequence site is sheafified extension
by pi_n. Map every 1 tensor x to the same generator in the published finite scalar
extension. The balanced tensor relations and sheafification extend this uniquely to
an invertible natural module map. -/
theorem ordinaryReductionEvaluation_exists (T : Scheme.{t}) (n : ℕ) :
    ∃! e : (diagonal d T ⋙ (scalarModel d T).E) ⋙ moduleEvaluation d T n ≅
        reductionChange T (d.projection T n),
      ∀ (M : proEtaleRingModules T (d.completedRing T)) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U)
        (z : (((diagonal d T ⋙ (scalarModel d T).E) ⋙
          moduleEvaluation d T n).obj M).val.obj U),
        HEq z ((eqToHom ((scalarModel d T).obj_eq ((diagonal d T).obj M)).symm).val.app
          (op (n, U.unop))
          (SemilinearSections.extensionUnit (diagonalProjection d T)
            ((diagonal d T).obj M) (op (n, U.unop)) x)) →
        HEq ((e.hom.app M).val.app U z)
          (reductionTensorSection T (d.projection T n) M U 1 x) := by
  sorry

/-- Finite evaluation of strict derived reduction retains its K-flat counit equation.
Source: Stacks 06YY, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: use one flat-term K-flat representative. The two universal scalar counits are
invertible there. Localize ordinaryReductionEvaluation and conjugate by these counits.
Functorial K-flat resolutions extend the comparison to every object and determine it
uniquely by the displayed equation. -/
theorem evaluationReduction_exists (T : Scheme.{t}) (n : ℕ) :
    ∃! e : reduction d T ⋙ evaluation d T n ≅ d.reduction T n,
      ∀ P : CochainComplex (proEtaleRingModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (evaluation d T n).map (reductionCounit d T P) ≫
            (moduleEvaluation d T n).mapDerivedCategoryFactors.hom.app
              (((diagonal d T ⋙ (scalarModel d T).E).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (ordinaryReductionEvaluation_exists d T n).exists.choose (.up ℤ)).hom.app P) =
          e.hom.app (DerivedCategory.Q.obj P) ≫
            reductionScalarComplexCounit T (d.projection T n) P := by
  sorry

/-- The normalized P_n-linear identification of the evaluated strict input with K_n.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def evaluationReduction (T : Scheme.{t}) (n : ℕ) :
    reduction d T ⋙ evaluation d T n ≅ d.reduction T n :=
  (evaluationReduction_exists d T n).exists.choose

/-- Ordinary ambient tower evaluation at the paper's positive level n+1.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev ambientModuleEvaluation (T : Scheme.{t}) (n : ℕ) :=
  reductionTowerEvaluation T (reductionModuleRing T (d.completedRing T)) n

/-- Derived ambient evaluation, using exact termwise evaluation.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev ambientEvaluation (T : Scheme.{t}) (n : ℕ) :=
  reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n

/-- Exact restriction of the finite coefficient action to the completed coefficient action.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev finiteRestriction (T : Scheme.{t}) (n : ℕ) :=
  reductionDerivedRestrict T (d.projection T n)

/-- Restriction and evaluation commute by the identity on the original section carriers.
Source: Stacks 03CZ, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: both sides are the n-th module with action restricted through pi_n and all maps
unchanged. Identity section maps are linear by that description. They give an
invertible natural transformation, uniquely determined on every section. -/
theorem moduleRestrictionEvaluation_exists (T : Scheme.{t}) (n : ℕ) :
    ∃! e : moduleRestriction d T ⋙ ambientModuleEvaluation d T n ≅
        moduleEvaluation d T n ⋙ reductionRestrict T (d.projection T n),
      ∀ (M : modules d T) (U : T.ProEtᵒᵖ),
        HEq (fun x ↦ (e.hom.app M).val.app U x)
          (fun x : M.val.obj (op (n, U.unop)) ↦ x) := by
  sorry

/-- Derived restriction/evaluation, induced by the ordinary identity of section carriers.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def restrictionEvaluation (T : Scheme.{t}) (n : ℕ) :
    restriction d T ⋙ ambientEvaluation d T n ≅
      evaluation d T n ⋙ finiteRestriction d T n :=
  (Functor.mapDerivedCategoryCompIso (moduleRestriction d T)
    (ambientModuleEvaluation d T n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (moduleRestrictionEvaluation_exists d T n).exists.choose ≪≫
    Functor.mapDerivedCategoryCompIso (moduleEvaluation d T n)
      (reductionRestrict T (d.projection T n))

/-- Ambient pullback/evaluation is the localization of the termwise identity.
Source: prop-weil-pbc-direct-image-limits, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def ambientPullEvaluation {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    d.towerPull u ⋙ ambientEvaluation d U n ≅ ambientEvaluation d V n ⋙ d.pull u :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Iso.refl (d.towerModulePull u ⋙ ambientModuleEvaluation d U n)) ≪≫
    Functor.mapDerivedCategoryCompIso (ambientModuleEvaluation d V n)
      (proEtaleRingModulePullback u (d.completedRing V) (d.completedRing U)
        (d.integralRingIso u))

/-- The canonical finite scalar restriction/pullback comparison for the same projections.
Source: Stacks 0D6D, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteRestrictionPull {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    d.finitePull u n ⋙ finiteRestriction d U n ≅
      finiteRestriction d V n ⋙ d.pull u :=
  proEtaleRingRestrictionDerivedPullback u (d.completedRing V) (d.finiteRing V n)
    (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
    (d.integralRingIso u) (d.finiteRingIso u n) (d.projection_comm u n)

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Automorphisms of the four schemes commuting with all four edges. Their commutation
identifications form the cube: in the scheme category higher coherence is equality of
proofs, and the Cartesian faces are supplied by `face_isPullback` below.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
structure Cube (_sq : ChosenCartesianSquare g' f' f g) where
  FX : X ≅ X
  FY : Y ≅ Y
  FX' : X' ≅ X'
  FY' : Y' ≅ Y'
  f_comm : FX.hom ≫ f = f ≫ FY.hom
  g_comm : FY'.hom ≫ g = g ≫ FY.hom
  g'_comm : FX'.hom ≫ g' = g' ≫ FX.hom
  f'_comm : FX'.hom ≫ f' = f' ≫ FY'.hom

/-- Each commutative face with invertible horizontal edges is Cartesian.
Source: blueprint Frobenius datum, paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: a cone over u and FV has the unique lift obtained by composing its first map
with FU inverse. The commutation equation verifies the second projection; cancellation
of FU proves uniqueness. The same construction applies to each of the four edges. -/
theorem face_isPullback {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) : IsPullback FU.hom u u FV.hom := by
  sorry

/-- The chosen Cartesian identification is the universal one for the Frobenius face.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def face {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :
    ChosenCartesianSquare FU.hom u u FV.hom where
  w := comm
  isoPullback := (face_isPullback u FU FV comm).isoPullback
  hom_fst := (face_isPullback u FU FV comm).isoPullback_hom_fst
  hom_snd := (face_isPullback u FU FV comm).isoPullback_hom_snd

/-- Integral kappa uses the canonical pullback composition on its Cartesian Frobenius face.
Source: blueprint paragraph 4; Stacks 0D6D
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def integralKappa {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :
    d.pull u ⋙ d.pull FU.hom ≅ d.pull FV.hom ⋙ d.pull u :=
  (proEtaleAmbientRingedPullbackComparison (face u FU FV comm)
    (d.completedRing U) (d.completedRing V) (d.completedRing U) (d.completedRing V)
    (d.integralRingIso u) (d.integralRingIso FV.hom) (d.integralRingIso FU.hom)
    (d.integralRingIso u) (d.integral_coherent (face u FU FV comm))).symm

/-- Integral beta is exactly the canonical ambient ringed exchange of the Frobenius face.
Source: blueprint paragraph 4; Stacks 07A7
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev integralBeta {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :=
  d.integralExchange (face u FU FV comm)

/-- The P_n-linear pullback-composition comparison on the Frobenius face.
Source: blueprint paragraph 4; Stacks 0D6D
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteKappa {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) (n : ℕ) :
    d.finitePull u n ⋙ d.finitePull FU.hom n ≅
      d.finitePull FV.hom n ⋙ d.finitePull u n :=
  (proEtaleAmbientRingedPullbackComparison (face u FU FV comm)
    (d.finiteRing U n) (d.finiteRing V n) (d.finiteRing U n) (d.finiteRing V n)
    (d.finiteRingIso u n) (d.finiteRingIso FV.hom n) (d.finiteRingIso FU.hom n)
    (d.finiteRingIso u n) (d.finite_coherent (face u FU FV comm) n)).symm

/-- The P_n-linear beta is the specified ambient exchange, hence the mate of kappa inverse.
Source: blueprint paragraph 4; Stacks 07A7
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev finiteBeta {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) (n : ℕ) :=
  d.finiteExchange (face u FU FV comm) n

/-- A coherent Weil structure is an isomorphism on the derived strict quotient diagram.
Its existence is data; no equality of evaluated morphisms is used as a substitute.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
structure WeilDatum (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X)
    extends Cube sq where
  theta : (pull d FX.hom).obj ((reduction d X).obj K) ≅ (reduction d X).obj K

variable {sq : ChosenCartesianSquare g' f' f g} {K : d.derived X}
  (F : WeilDatum d sq K)

/-- The quotient diagram's B and D corners, constructed by its actual total operations.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev cornerB := (pull d g).obj ((push d f).obj ((reduction d X).obj K))

/-- The quotient diagram's D corner, with ordinary uncompleted pullback on X'.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
abbrev cornerD := (push d f').obj ((pull d g').obj ((reduction d X).obj K))

/-- Theta_E is pullback of the strict Weil map after the specified pullback composition.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def thetaE :
    (pull d F.FX'.hom).obj ((pull d g').obj ((reduction d X).obj K)) ⟶
      (pull d g').obj ((reduction d X).obj K) :=
  (kappa d g' F.FX' F.FX F.g'_comm).hom.app ((reduction d X).obj K) ≫
    (pull d g').map F.theta.hom

/-- Theta_B is kappa_g, followed by Lg* beta_f, followed by Lg* Rf* theta.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def thetaB : (pull d F.FY'.hom).obj (cornerB (f := f) (g := g) d (K := K)) ⟶
    cornerB (f := f) (g := g) d (K := K) :=
  (kappa d g F.FY' F.FY F.g_comm).hom.app ((push d f).obj ((reduction d X).obj K)) ≫
    (pull d g).map ((beta d f F.FX F.FY F.f_comm).app ((reduction d X).obj K)) ≫
    (pull d g).map ((push d f).map F.theta.hom)

/-- Theta_D is beta_f' followed by Rf'* theta_E, on the strict quotient diagram itself.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def thetaD : (pull d F.FY'.hom).obj (cornerD (f' := f') (g' := g') d (K := K)) ⟶
    cornerD (f' := f') (g' := g') d (K := K) :=
  (beta d f' F.FX' F.FY' F.f'_comm).app ((pull d g').obj ((reduction d X).obj K)) ≫
    (push d f').map (thetaE d F)

/-- Evaluated Weil isomorphism, retaining its P_n-linear action and strict origin.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteWeil (n : ℕ) :
    (d.finitePull F.FX.hom n).obj ((d.reduction X n).obj K) ≅
      (d.reduction X n).obj K :=
  (d.finitePull F.FX.hom n).mapIso ((evaluationReduction d X n).app K).symm ≪≫
    ((evaluationPull d F.FX.hom n).app ((reduction d X).obj K)).symm ≪≫
    (evaluation d X n).mapIso F.theta ≪≫ (evaluationReduction d X n).app K

/-- The normalized quotient-linear identification of the evaluated B corner.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteBComparison (n : ℕ) :
    (evaluation d Y' n).obj (cornerB (f := f) (g := g) d (K := K)) ≅
      d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 1 :=
  (evaluationPull d g n).app ((push d f).obj ((reduction d X).obj K)) ≪≫
    (d.finitePull g n).mapIso ((evaluationPush d f n).app ((reduction d X).obj K)) ≪≫
    (d.finitePull g n).mapIso ((d.finitePush f n).mapIso
      ((evaluationReduction d X n).app K))

/-- The normalized quotient-linear identification of the evaluated D corner.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteDComparison (n : ℕ) :
    (evaluation d Y' n).obj (cornerD (f' := f') (g' := g') d (K := K)) ≅
      d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 3 :=
  (evaluationPush d f' n).app ((pull d g').obj ((reduction d X).obj K)) ≪≫
    (d.finitePush f' n).mapIso ((evaluationPull d g' n).app ((reduction d X).obj K)) ≪≫
    (d.finitePush f' n).mapIso ((d.finitePull g' n).mapIso
      ((evaluationReduction d X n).app K))

/-- Finite-linear evaluation of a strict Frobenius structure through its fixed comparison.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteTransport {T : Scheme.{t}} (FT : T ≅ T) (n : ℕ) {M : derived d T}
    {N : DerivedCategory (proEtaleRingModules T (d.finiteRing T n))}
    (c : (evaluation d T n).obj M ≅ N) (theta : (pull d FT.hom).obj M ⟶ M) :
    (d.finitePull FT.hom n).obj N ⟶ N :=
  (d.finitePull FT.hom n).map c.inv ≫
    (evaluationPull d FT.hom n).inv.app M ≫ (evaluation d T n).map theta ≫ c.hom

/-- Theta_B,n is evaluation of the coherent strict diagram morphism, with its P_n-action.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteThetaB (n : ℕ) :
    (d.finitePull F.FY'.hom n).obj
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 1) ⟶
        d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 1 :=
  finiteTransport d F.FY' n (finiteBComparison d n) (thetaB d F)

/-- Theta_D,n is evaluation of the coherent strict diagram morphism, with its P_n-action.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteThetaD (n : ℕ) :
    (d.finitePull F.FY'.hom n).obj
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 3) ⟶
        d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 3 :=
  finiteTransport d F.FY' n (finiteDComparison d n) (thetaD d F)

/-- The finite theta_E formula with the specified finite pullback composition.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteThetaE (n : ℕ) :
    (d.finitePull F.FX'.hom n).obj
      ((d.finitePull g' n).obj ((d.reduction X n).obj K)) ⟶
        (d.finitePull g' n).obj ((d.reduction X n).obj K) :=
  (finiteKappa d g' F.FX' F.FX F.g'_comm n).hom.app _ ≫
    (d.finitePull g' n).map (finiteWeil d F n).hom

/-- Finite evaluation carries kappa and beta to the canonical finite-level comparisons.
Source: lem-coef-semilinear-derived-sections, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: the ordinary evaluation comparison is identity on direct-image sections and
its pullback comparison is normalized by tensor units. Localization therefore preserves
pullback composition. The semilinear derived adjunction comparisons preserve units and
counits, hence preserve mates. Apply this to each edge and use naturality of the
reduction comparison to obtain the two displayed formulas. -/
theorem finite_formulas (n : ℕ) :
    finiteThetaB d F n =
      (finiteKappa d g F.FY' F.FY F.g_comm n).hom.app
        ((d.finitePush f n).obj ((d.reduction X n).obj K)) ≫
      (d.finitePull g n).map ((finiteBeta d f F.FX F.FY F.f_comm n).app
        ((d.reduction X n).obj K)) ≫
      (d.finitePull g n).map ((d.finitePush f n).map (finiteWeil d F n).hom) ∧
    finiteThetaD d F n =
      (finiteBeta d f' F.FX' F.FY' F.f'_comm n).app
        ((d.finitePull g' n).obj ((d.reduction X n).obj K)) ≫
      (d.finitePush f' n).map (finiteThetaE d F n) := by
  sorry

/-- All four finite structures, with A and C conjugated only by the published h and h'.
The input hypotheses and finite etale-origin witnesses are precisely those of fourArrows.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def finiteTheta [IsProper f] (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) (i : Fin 4) :
    (d.finitePull F.FY'.hom n).obj
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n i) ⟶
        d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n i :=
  match i with
  | 0 => (d.finitePull F.FY'.hom n).map ((d.fourArrows sq K hK W n).h.hom) ≫
      finiteThetaB d F n ≫ (d.fourArrows sq K hK W n).h.inv
  | 1 => finiteThetaB d F n
  | 2 => (d.finitePull F.FY'.hom n).map ((d.fourArrows sq K hK W n).h'.hom) ≫
      finiteThetaD d F n ≫ (d.fourArrows sq K hK W n).h'.inv
  | 3 => finiteThetaD d F n

/-- The canonical Q-to-ambient identification of B, retaining both derived factorizations.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def cornerBComparison :
    (restriction d Y').obj (cornerB (f := f) (g := g) d (K := K)) ≅
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1 :=
  (restrictionPull d g).app ((push d f).obj ((reduction d X).obj K)) ≪≫
    (d.towerPull g).mapIso ((restrictionPush d f).app ((reduction d X).obj K)) ≪≫
    (d.towerPull g).mapIso ((d.towerPush f).mapIso ((reductionRestriction d X).app K))

/-- The canonical Q-to-ambient identification of D, retaining all strict transitions.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def cornerDComparison :
    (restriction d Y').obj (cornerD (f' := f') (g' := g') d (K := K)) ≅
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3 :=
  (restrictionPush d f').app ((pull d g').obj ((reduction d X).obj K)) ≪≫
    (d.towerPush f').mapIso ((restrictionPull d g').app ((reduction d X).obj K)) ≪≫
    (d.towerPush f').mapIso ((d.towerPull g').mapIso ((reductionRestriction d X).app K))

/-- Transport a quotient-diagram Frobenius map by restriction and the specified comparison.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def transport {T : Scheme.{t}} (FT : T ≅ T) {M : derived d T}
    {N : DerivedCategory (d.towers T)}
    (c : (restriction d T).obj M ≅ N) (theta : (pull d FT.hom).obj M ⟶ M) :
    (d.towerPull FT.hom).obj N ⟶ N :=
  (d.towerPull FT.hom).map c.inv ≫
    (restrictionPull d FT.hom).inv.app M ≫ (restriction d T).map theta ≫ c.hom

/-- Frobenius on all four ambient strict towers. A and C are conjugated by H and H'
only after restriction; no quotient-diagram lift of these two isomorphisms is chosen.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def towerTheta (i : Fin 4) :
    (d.towerPull F.FY'.hom).obj
        (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i) ⟶
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i :=
  match i with
  | 0 => (d.towerPull F.FY'.hom).map
        (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom ≫
      transport d F.FY' (cornerBComparison d) (thetaB d F) ≫
        (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).inv
  | 1 => transport d F.FY' (cornerBComparison d) (thetaB d F)
  | 2 => (d.towerPull F.FY'.hom).map
        (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K).hom ≫
      transport d F.FY' (cornerDComparison d) (thetaD d F) ≫
        (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K).inv
  | 3 => transport d F.FY' (cornerDComparison d) (thetaD d F)

/-- The canonical restriction/evaluation comparison for the B corner.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def ambientBComparison (n : ℕ) :
    (ambientEvaluation d Y' n).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1) ≅
    (finiteRestriction d Y' n).obj
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 1) :=
  (ambientEvaluation d Y' n).mapIso (cornerBComparison d).symm ≪≫
    (restrictionEvaluation d Y' n).app (cornerB (f := f) (g := g) d (K := K)) ≪≫
    (finiteRestriction d Y' n).mapIso (finiteBComparison d n)

/-- The canonical restriction/evaluation comparison for the D corner.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def ambientDComparison (n : ℕ) :
    (ambientEvaluation d Y' n).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3) ≅
    (finiteRestriction d Y' n).obj
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 3) :=
  (ambientEvaluation d Y' n).mapIso (cornerDComparison d).symm ≪≫
    (restrictionEvaluation d Y' n).app (cornerD (f' := f') (g' := g') d (K := K)) ≪≫
    (finiteRestriction d Y' n).mapIso (finiteDComparison d n)

/-- All four canonical corner evaluation comparisons, normalized by H,h and H',h'.
Source: lem-weil-pbc-strict-tower-exchange-mate-normalization, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def ambientCornerComparison [IsProper f] (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) (i : Fin 4) :
    (ambientEvaluation d Y' n).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i) ≅
    (finiteRestriction d Y' n).obj
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n i) :=
  match i with
  | 0 => (ambientEvaluation d Y' n).mapIso
        (d.towerH (f := f) (f' := f') (g := g) (g' := g') K) ≪≫
      ambientBComparison d n ≪≫
        (finiteRestriction d Y' n).mapIso (d.fourArrows sq K hK W n).h.symm
  | 1 => ambientBComparison d n
  | 2 => (ambientEvaluation d Y' n).mapIso
        (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K) ≪≫
      ambientDComparison d n ≪≫
        (finiteRestriction d Y' n).mapIso (d.fourArrows sq K hK W n).h'.symm
  | 3 => ambientDComparison d n

/-- Evaluations of the ambient strict structures are precisely the restricted finite ones.
Source: blueprint paragraph 4; lem-coef-semilinear-derived-sections;
prop-weil-pbc-direct-image-limits
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: before deriving, both restriction/evaluation paths are identity on the same
sections and pi_n-restricted scalar action. Their direct-image comparisons use the same
universal units for the two factorizations of one ringed morphism. Uniqueness of that
comparison identifies them; the tensor-unit pullback comparison is its adjunction mate.
Thus restriction commutes with the quotient finite transport formula for B and D.
For A and C substitute their conjugations by H and H', and cancel the inverse h and h'
in ambientCornerComparison. This proves the four equations without requiring faithfulness
of derived evaluation. -/
theorem towerTheta_evaluation [IsProper f] (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) (i : Fin 4) :
    (ambientEvaluation d Y' n).map (towerTheta d F i) ≫
        (ambientCornerComparison (sq := sq) d hK W n i).hom =
      (ambientPullEvaluation d F.FY'.hom n).hom.app _ ≫
        (d.pull F.FY'.hom).map
          (ambientCornerComparison (sq := sq) d hK W n i).hom ≫
        (finiteRestrictionPull d F.FY'.hom n).inv.app _ ≫
        (finiteRestriction d Y' n).map (finiteTheta d F hK W n i) := by
  sorry

/-- The underived Frobenius/limit comparison is the actual universal limit comparison.
Source: blueprint paragraph 4; Stacks 0A07
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: identified-coefficient pullback by FT is exact and is the direct image by FT
inverse. That direct image preserves limits. The unique comparison is therefore an
isomorphism whose hom is limit.post; its inverse is fixed by the same limit projections. -/
theorem modulePullLimit_exists (T : Scheme.{t}) (FT : T ≅ T) :
    ∃! e : completedTowerLimit T (d.completedRing T) ⋙
        proEtaleRingModulePullback FT.hom (d.completedRing T) (d.completedRing T)
          (d.integralRingIso FT.hom) ≅
      d.towerModulePull FT.hom ⋙ completedTowerLimit T (d.completedRing T),
      ∀ M : d.towers T,
        e.hom.app M = limit.post M
          (proEtaleRingModulePullback FT.hom (d.completedRing T) (d.completedRing T)
            (d.integralRingIso FT.hom)) := by
  sorry

/-- Universal right-derived unit of the actual strict inverse limit, on cochain complexes.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def rlimUnit (T : Scheme.{t}) (P : CochainComplex (d.towers T) ℤ) :
    DerivedCategory.Q.obj
        (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (completedRlim T (d.completedRing T)).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (completedRlimUnit T (d.completedRing T)).app ((HomotopyCategory.quotient _ _).obj P) ≫
    (completedRlim T (d.completedRing T)).map
      ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- j is the derived comparison for the inverse automorphism, transported to exact
Frobenius pullback. Its universal-unit equation retains the common direct-image
normalization and does not select a map of independently chosen Roos triangles.
Source: blueprint paragraph 4; lem-weil-ringed-tower-pushforward-limit-comparison
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures).
Proof: apply the ringed tower pushforward/limit theorem to FT inverse. Its exact
ordinary direct image identifies, by the normalized inverse adjunction, with FT
pullback, termwise also on towers. Under this identification its ordinary comparison
is precisely modulePullLimit. The theorem's common-direct-image unit equation becomes
the displayed equation. K-injective tower resolutions make that equation determine j
uniquely; the comparison is invertible and commutes with every projection. -/
theorem pullLimit_exists (T : Scheme.{t}) (FT : T ≅ T) :
    ∃! e : completedRlim T (d.completedRing T) ⋙ d.pull FT.hom ≅
        d.towerPull FT.hom ⋙ completedRlim T (d.completedRing T),
      ∀ P : CochainComplex (d.towers T) ℤ,
        (d.pull FT.hom).map (rlimUnit d T P) ≫ e.hom.app (DerivedCategory.Q.obj P) =
          (proEtaleRingModulePullback FT.hom (d.completedRing T) (d.completedRing T)
            (d.integralRingIso FT.hom)).mapDerivedCategoryFactors.hom.app
              (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj
                P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (modulePullLimit_exists d T FT).exists.choose
              (.up ℤ)).hom.app P) ≫
          rlimUnit d T (((d.towerModulePull FT.hom).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (completedRlim T (d.completedRing T)).map
            ((d.towerModulePull FT.hom).mapDerivedCategoryFactors.inv.app P) := by
  sorry

/-- The inverse-automorphism comparison j with its universal-unit normalization retained.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def pullLimit (T : Scheme.{t}) (FT : T ≅ T) :
    completedRlim T (d.completedRing T) ⋙ d.pull FT.hom ≅
      d.towerPull FT.hom ⋙ completedRlim T (d.completedRing T) :=
  (pullLimit_exists d T FT).exists.choose

/-- Theta_Z,infinity is j_Z followed by the total derived limit of the strict Theta_Z.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def limitTheta (i : Fin 4) :
    (d.pull F.FY'.hom).obj ((completedRlim Y' (d.completedRing Y')).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i)) ⟶
      (completedRlim Y' (d.completedRing Y')).obj
        (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i) :=
  (pullLimit d Y' F.FY').hom.app _ ≫
    (completedRlim Y' (d.completedRing Y')).map (towerTheta d F i)

/-- s_A is exactly the defining identification of completed pullback with Rlim A.
Source: blueprint paragraph 4; def-weil-pbc-completed-base-change-map
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def sourceIdentification : (d.completedPull g).obj ((d.push f).obj K) ≅
    (completedRlim Y' (d.completedRing Y')).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 0) :=
  Iso.refl _

/-- d is precisely c_f',M, directed from T to Rlim D.
Source: blueprint paragraph 4; def-weil-pbc-completed-base-change-map
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def targetIdentification : (d.push f').obj ((d.completedPull g').obj K) ≅
    (completedRlim Y' (d.completedRing Y')).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3) :=
  (d.directImageRlimIso f').app
    ((d.towerPull g').obj ((completedReductionTower X d).obj K))

/-- Theta_S is conjugation of Theta_A,infinity by the specified s_A.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def sourceTheta :
    (d.pull F.FY'.hom).obj ((d.completedPull g).obj ((d.push f).obj K)) ⟶
      (d.completedPull g).obj ((d.push f).obj K) :=
  (d.pull F.FY'.hom).map (sourceIdentification (f := f) (f' := f') (g := g) (g' := g')
    d (K := K)).hom ≫ limitTheta d F 0 ≫
      (sourceIdentification (f := f) (f' := f') (g := g) (g' := g') d (K := K)).inv

/-- Theta_T is conjugation of Theta_D,infinity by the specified d=c_f',M.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def targetTheta :
    (d.pull F.FY'.hom).obj ((d.push f').obj ((d.completedPull g').obj K)) ⟶
      (d.push f').obj ((d.completedPull g').obj K) :=
  (d.pull F.FY'.hom).map (targetIdentification (f := f) (f' := f') (g := g) (g' := g')
    d (K := K)).hom ≫ limitTheta d F 3 ≫
      (targetIdentification (f := f) (f' := f') (g := g) (g' := g') d (K := K)).inv

/-- Finite tensor reduction of Theta_S uses the quotient-linear chi for Frobenius itself.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def sourceReducedTheta (n : ℕ) :
    (d.finitePull F.FY'.hom n).obj
        ((d.reduction Y' n).obj ((d.completedPull g).obj ((d.push f).obj K))) ⟶
      (d.reduction Y' n).obj ((d.completedPull g).obj ((d.push f).obj K)) :=
  (d.chi F.FY'.hom n).hom.app _ ≫ (d.reduction Y' n).map (sourceTheta d F)

/-- Finite tensor reduction of Theta_T, with the actual quotient action retained.
Source: blueprint paragraph 4 (blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def targetReducedTheta (n : ℕ) :
    (d.finitePull F.FY'.hom n).obj
        ((d.reduction Y' n).obj ((d.push f').obj ((d.completedPull g').obj K))) ⟶
      (d.reduction Y' n).obj ((d.push f').obj ((d.completedPull g').obj K)) :=
  (d.chi F.FY'.hom n).hom.app _ ≫ (d.reduction Y' n).map (targetTheta d F)

/-- The comparison called s in the completed-map construction is Rlim(H) after s_A.
Source: def-weil-pbc-completed-base-change-map, blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def sourceBIdentification : (d.completedPull g).obj ((d.push f).obj K) ≅
    (completedRlim Y' (d.completedRing Y')).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1) :=
  sourceIdentification (f := f) (f' := f') (g := g) (g' := g') d (K := K) ≪≫
    (completedRlim Y' (d.completedRing Y')).mapIso
      (d.towerH (f := f) (f' := f') (g := g) (g' := g') K)

/-- A record of all displayed corner structures in their exact coefficient categories.
The construction below fills its fields with the canonical formulas above.
Source: blueprint paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
structure CornerStructures where
  quotientE : (pull d F.FX'.hom).obj ((pull d g').obj ((reduction d X).obj K)) ⟶
    (pull d g').obj ((reduction d X).obj K)
  quotientB : (pull d F.FY'.hom).obj (cornerB (f := f) (g := g) d (K := K)) ⟶
    cornerB (f := f) (g := g) d (K := K)
  quotientD : (pull d F.FY'.hom).obj (cornerD (f' := f') (g' := g') d (K := K)) ⟶
    cornerD (f' := f') (g' := g') d (K := K)
  finite : ∀ (n : ℕ) (i : Fin 4),
    (d.finitePull F.FY'.hom n).obj
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n i) ⟶
        d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n i
  strict : ∀ i : Fin 4,
    (d.towerPull F.FY'.hom).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i) ⟶
        d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i
  completed : ∀ i : Fin 4,
    (d.pull F.FY'.hom).obj ((completedRlim Y' (d.completedRing Y')).obj
      (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i)) ⟶
        (completedRlim Y' (d.completedRing Y')).obj
          (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i)
  source : (d.pull F.FY'.hom).obj ((d.completedPull g).obj ((d.push f).obj K)) ⟶
    (d.completedPull g).obj ((d.push f).obj K)
  target : (d.pull F.FY'.hom).obj ((d.push f').obj ((d.completedPull g').obj K)) ⟶
    (d.push f').obj ((d.completedPull g').obj K)
  sourceReduction : ∀ n : ℕ,
    (d.finitePull F.FY'.hom n).obj
      ((d.reduction Y' n).obj ((d.completedPull g).obj ((d.push f).obj K))) ⟶
        (d.reduction Y' n).obj ((d.completedPull g).obj ((d.push f).obj K))
  targetReduction : ∀ n : ℕ,
    (d.finitePull F.FY'.hom n).obj
      ((d.reduction Y' n).obj ((d.push f').obj ((d.completedPull g').obj K))) ⟶
        (d.reduction Y' n).obj ((d.push f').obj ((d.completedPull g').obj K))

/-- Frobenius structures on the actual quotient corners and their strict completions.
The proper square, derived completeness and separate finite etale-origin witnesses are
exactly the domain of the completed base-change map. The coherent Weil isomorphism
is supplied on the ordinary derived category of strict Q_X-modules. Each field is the
specified formula; neither levelwise arrows nor chosen product cones replace it.
Source: blueprint main-20261015, completed-map-reduction proof, paragraph 4
(blueprint: def-weil-pbc-quotient-corner-frobenius-structures). -/
def quotientCornerFrobeniusStructures [IsProper f] (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) : CornerStructures d F where
  quotientE := thetaE d F
  quotientB := thetaB d F
  quotientD := thetaD d F
  finite := finiteTheta d F hK W
  strict := towerTheta d F
  completed := limitTheta d F
  source := sourceTheta d F
  target := targetTheta d F
  sourceReduction := sourceReducedTheta d F
  targetReduction := targetReducedTheta d F


end QuotientFrobenius
end AlgebraicGeometry.Scheme
