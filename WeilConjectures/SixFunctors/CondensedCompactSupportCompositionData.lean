/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedCompactSupportComposition

public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Refinement
import WeilConjectures.AlgebraicGeometry.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.FiniteDirectImageComposition
import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.AlgebraicGeometry.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProperImageLocalizingProper
import WeilConjectures.AlgebraicGeometry.CondensedArbitraryProperGenerators
import WeilConjectures.AlgebraicGeometry.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.CategoryTheory.Triangulated.LocalizingIsoLocus
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.CompactSupportRefinementBaseChange
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Direct data interface for coherent condensed compact-support comparisons

Source: latest blueprint sk-thm-sf-comp-composition, clauses (1)--(2)
(blueprint: sk-thm-sf-comp-composition).

This structure exposes exactly the six witnesses and twelve equations of the recorded
Coherent predicate. The previous interface nested the witnesses in existential propositions;
extracting its third and sixth witnesses caused reproducible kernel timeouts. Named fields
retain every normalization and coherence condition while making the maps directly usable.
The canonical helper constructions are imported from the owning module, not redefined.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace CompactSupportComposition

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Keep the shared derived-category instances opaque while checking the field types.
attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

/-- The exact six simultaneous witnesses and all twelve normalization/coherence clauses
of Coherent, expressed as fields. In particular neither comp nor exchange is an arbitrary
isomorphism: comp_normalized, open_normalized and exchange_normalized specify their maps.
Source: blueprint composition/base change, all clauses and canonicity
(blueprint: sk-thm-sf-comp-composition). -/
structure ComparisonWitnesses (k : Type u) [Field k] where
  preserves : ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    (∀ K, localizingClosureProEtale Λ X.obj.left K →
      localizingClosureProEtale Λ Y.obj.left
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ X.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ Y.obj.left
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
  comparison : ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c d : Compactification f.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ d
  comp : ∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left)),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙
          rightDerivedLowerShriekOfCompactification Λ d) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ e
  openIso : ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (sq : IsPullback a f'.hom.left f.hom.left v) (c : Compactification f.hom.left),
    D((c.i)_!open⟦Λ⟧) ⋙ moduleObjectDerivedPullback Λ (pullback.fst c.g v) ≅
      moduleObjectDerivedPullback Λ a ⋙ D(((c.ofIsPullback sq).i)_!open⟦Λ⟧)
  pullback_preserves : ∀ (X Y : SepFinType k) (v : X.obj.left ⟶ Y.obj.left),
    (∀ K, localizingClosureProEtale Λ Y.obj.left K →
      localizingClosureProEtale Λ X.obj.left ((moduleObjectDerivedPullback Λ v).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ Y.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ X.obj.left ((moduleObjectDerivedPullback Λ v).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((moduleObjectDerivedPullback Λ v).obj K))
  exchange : ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (_sq : IsPullback a f'.hom.left f.hom.left v)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙ moduleObjectDerivedPullback Λ v) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ a ⋙ rightDerivedLowerShriekOfCompactification Λ d)

/-- All twelve original normalization and coherence equations on the six comparison witnesses.
Source: blueprint composition/base change, canonicity and all coherence clauses
(blueprint: sk-thm-sf-comp-composition). -/
def ComparisonLaws (k : Type u) [Field k] (H : ComparisonWitnesses Λ k) : Prop :=
  -- refinement
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d : Compactification f.hom.left)
      (r : Compactification.DenseBoundaryCompactification f.hom.left)
      [QuasiCompact f.hom.left]
      (hc : r.obj ⟶ detSfBoundaryCompactification c)
      (hd : r.obj ⟶ detSfBoundaryCompactification d)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comparison f c d).hom.app K ≫ compactificationRefinementComponent Λ hd K.obj =
      compactificationRefinementComponent Λ hc K.obj) ∧
  -- comparison_id
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    H.comparison f c c = Iso.refl _) ∧
  -- comparison_cocycle
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d e : Compactification f.hom.left),
    H.comparison f c d ≪≫ H.comparison f d e = H.comparison f c e) ∧
  -- comp_normalized
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (T : Compactification.Triangle f.hom.left g.hom.left)
      [QuasiCompact (T.cf.g ≫ T.cg.i)]
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    ∃ m, compositionInterchangeIsNormalized Λ T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Λ⟧).obj K.obj) m ∧
      (H.comp f g T.cf T.cg T.cfg).hom.app K =
        R((T.cg.g)_*⟦Λ⟧).map
          (m ≫ R((T.p)_*⟦Λ⟧).map
            ((openFactor Λ T.cf.i T.q T.cfg.i T.i_q).hom.app K.obj)) ≫
          (rightDerivedLowerStarComp Λ T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (lowerStar Λ) T.p_g))).hom.app
              (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj)) ∧
  -- comp_independent
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c c' : Compactification f.hom.left) (d d' : Compactification g.hom.left)
      (e e' : Compactification (f.hom.left ≫ g.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comp f g c d e).hom.app K ≫ (H.comparison (f ≫ g) e e').hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ d).map ((H.comparison f c c').hom.app K) ≫
        (H.comparison g d d').hom.app
          ⟨_, (H.preserves f c').1 K.obj K.property⟩ ≫ (H.comp f g c' d' e').hom.app K) ∧
  -- unit_left
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comp (𝟙 X) f (Compactification.ofIsProper (𝟙 X.obj.left)) c
      (c.copy (Category.id_comp f.hom.left))).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map ((identity Λ X.obj.left).hom.app K.obj)) ∧
  -- unit_right
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comp f (𝟙 Y) c (Compactification.ofIsProper (𝟙 Y.obj.left))
      (c.copy (Category.comp_id f.hom.left))).hom.app K =
      (identity Λ Y.obj.left).hom.app ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj)) ∧
  -- assoc
  (∀ {X Y Z W : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification h.hom.left)
      (cd : Compactification (f.hom.left ≫ g.hom.left))
      (de : Compactification (g.hom.left ≫ h.hom.left))
      (cde : Compactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (rightDerivedLowerShriekOfCompactification Λ e).map ((H.comp f g c d cd).hom.app K) ≫
        (H.comp (f ≫ g) h cd e cde).hom.app K =
      (H.comp g h d e de).hom.app ⟨_, (H.preserves f c).1 K.obj K.property⟩ ≫
        (H.comp f (g ≫ h) c de (cde.copy (Category.assoc _ _ _).symm)).hom.app K) ∧
  -- open_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (sq : IsPullback a f'.hom.left f.hom.left v) (c : Compactification f.hom.left),
    (H.openIso sq c).inv = openExchange Λ sq c) ∧
  -- exchange_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (sq : IsPullback a f'.hom.left f.hom.left v)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.exchange sq c d).hom.app K =
      (condensedAmbientExchange Λ (square (c.isPullback_g_ofIsPullback sq).flip)).app
          (D((c.i)_!open⟦Λ⟧).obj K.obj) ≫
        R(((c.ofIsPullback sq).g)_*⟦Λ⟧).map ((H.openIso sq c).hom.app K.obj) ≫
        (H.comparison f' (c.ofIsPullback sq) d).hom.app
          ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- exchange_independent
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (sq : IsPullback a f'.hom.left f.hom.left v)
      (c c' : Compactification f.hom.left) (d d' : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (moduleObjectDerivedPullback Λ v).map ((H.comparison f c c').hom.app K) ≫
        (H.exchange sq c' d').hom.app K =
      (H.exchange sq c d).hom.app K ≫ (H.comparison f' d d').hom.app
        ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- comp_exchange
  (∀ {X Y Z X' Y' Z' : SepFinType k}
      (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
      (a : X'.obj.left ⟶ X.obj.left) (b : Y'.obj.left ⟶ Y.obj.left)
      (v : Z'.obj.left ⟶ Z.obj.left)
      (sf : IsPullback a f'.hom.left f.hom.left b)
      (sg : IsPullback b g'.hom.left g.hom.left v)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left))
      (c' : Compactification f'.hom.left) (d' : Compactification g'.hom.left)
      (e' : Compactification (f'.hom.left ≫ g'.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (moduleObjectDerivedPullback Λ v).map ((H.comp f g c d e).hom.app K) ≫
        (H.exchange (X := X) (Y := Z) (X' := X') (Y' := Z')
          (f := f ≫ g) (f' := f' ≫ g') (a := a) (v := v) (sf.paste_vert sg) e e').hom.app K =
      (H.exchange (f := g) (f' := g') (a := b) (v := v) sg d d').hom.app
          ⟨_, (H.preserves f c).1 K.obj K.property⟩ ≫
        (rightDerivedLowerShriekOfCompactification Λ d').map
          ((H.exchange (f := f) (f' := f') (a := a) (v := b) sf c c').hom.app K) ≫
        (H.comp f' g' c' d' e').hom.app
          ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩)

/-- The six witnesses together with all twelve original equations. Separating the equation
predicate avoids repeatedly checking dependent projection types in a single large structure.
Source: blueprint composition/base change, clauses (1)--(2)
(blueprint: sk-thm-sf-comp-composition). -/
structure CoherentData (k : Type u) [Field k] extends ComparisonWitnesses Λ k where
  laws : ComparisonLaws Λ k toComparisonWitnesses

/-- Composition and arbitrary scheme base change for condensed compact supports, with the
canonical refinement and proper/open normalizations and all coherence equations.
Source: blueprint latest, sk-thm-sf-comp-composition, clauses (1)--(2)
(blueprint: sk-thm-sf-comp-composition).

Proof plan, following the seven DAG steps:
1. Choose compactifications using thm-nagata-compactification and
lem-sfb-over-compactification-composite-cartesian. The theorems
det-sf-comp-coherence-single and det-proper-image-localizing-open preserve Dctf and Loc.
2. Interchange the middle proper and open factors using the unique identity-on-the-open
map (det-sf-comp-composition-interchange, lem-zl-condensed-open-proper-pasting). Apply the
last proper image and the canonical compositors (lem-weil-derived-direct-image-composition).
3. Compare all compactification models by common dense refinements. Mixed horizontal and
vertical mate-pasting commute with refinement; the compactification cocycle cancels the
intermediate comparisons (det-nagata-refinement-common-dense,
det-sf-comp-coherence-refinement, det-sf-comp-coherence-cocycle,
lem-zl-condensed-open-proper-pasting). This gives simultaneous independence.
4. Expand both threefold bracketings. Disjoint moves commute; overlapping moves are the
mixed-pasting equations or the proper/open compositor associativity laws. Identity models
give both unit equations. These are equations of actual ambient arrows on every Loc object.
5. Arbitrary scheme pullback preserves Dctf and sums. Proper exchange is invertible on Dctf
by lem-zl-condensed-arbitrary-proper-generators and lem-weil-pbc-proper-base-change, and on
Loc by det-proper-image-localizing-proper, lem-sfb-ambient-qcqs-exchange-canonical-shifts and
det-sf-determination-localizing. Pullback preservation is lem-zl-condensed-arbitrary-pullback.
No vertical map is required to respect the ground field.
6. Pull back each compactification literally, allowing nondense models. Compose proper
exchange with the inverse of the open-adjunction mate and the normalized compactification
comparison (lemma-nagata-compactification-base-change). The theorem
lem-sfb-compact-support-refinement-base-change and the cocycle prove choice independence.
7. Expand composition/exchange into these proper and open mates. Mate-pasting, the mixed
cube equation and open composition give the displayed equation, with canonical associators
(lem-zl-condensed-open-proper-pasting, lem-weil-pbc-mate-pasting,
lem-sfb-ringed-derived-monoidal-comparisons).
Fullness and the preservation clauses restrict every comparison and equation to Dctf. -/
theorem coherentData_exists (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime]
    (hpℓ : p ≠ ℓ) (k : Type u) [Field k] [CharP k p]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    Nonempty (CoherentData Λ k) := by
  sorry

end CompactSupportComposition
end AlgebraicGeometry.ProEtale.CondensedRing
