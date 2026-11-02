/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedShriekBoundedQcqs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZlShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
public import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedProperOpenQcqsCalculus
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.QcqsTowerNormalizationLaw
/-! # Condensed compact-support composition over quasi-separated bases

Definition interface (blueprint: def-zl-qcqs-composition-defs).

Source: latest blueprint, lem-zl-shriek-composition.proof, and
sk-thm-sf-comp-composition (1),(2); Stacks Tag 0F7J, lemma-shriek-composition
(blueprint: lem-zl-condensed-shriek-composition-qcqs).

The witnesses below retain the actual compactification functors, proper-refinement maps,
normalized proper/open compositor, and the proper/open isomorphism exchange. All categories
are full subcategories of the ordinary derived category with the pulled-back condensed ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

open CompactSupportComposition

variable (ℓ : ℕ) [Fact ℓ.Prime]

section

-- Match the coefficient-instance presentation in the bounded qcqs comparison theorem.
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

/-- The existing ordinary bounded constructible category with finite constant local models.
Source: latest blueprint, coefficient/category convention
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
abbrev C (X : Scheme.{u}) :=
  ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X

/-- The existing bounded constructible object predicate, with no completion condition.
Source: latest blueprint, coefficient/category convention
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
abbrev bc (X : Scheme.{u}) :=
  constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X

/-- A coherent compactification system for the given morphism. The comparison is fixed
on every proper refinement and satisfies identity and cocycle equations.
Source: Stacks 0F7J, refinement comparisons in the source proof, Step 3
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
structure System {X Y : Scheme.{u}} (f : X ⟶ Y) where
  preserves : ∀ (c : Compactification f)
      (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X),
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y
      ((CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) c).obj K.obj)
  comparison : ∀ c d : Compactification f,
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι ⋙
        CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) c ≅
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι ⋙
        CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) d
  refinement : ∀ (c d : Compactification f) (r : d.Refinement c)
      (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X),
    (comparison c d).hom.app K =
      (CompactificationReindexing.refinement (Profinite.padicAlgClRingObj ℓ) r).app K.obj
  comparison_id : ∀ c : Compactification f, comparison c c = Iso.refl _
  comparison_cocycle : ∀ c d e : Compactification f,
    comparison c d ≪≫ comparison d e = comparison c e

/-- The actual restriction of Rp_* j_! to bounded constructible objects.
Source: source proof, Steps 2--3 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
abbrev System.support {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (c : Compactification f) : C ℓ X ⥤ C ℓ Y :=
  (bc ℓ Y).lift ((bc ℓ X).ι ⋙
    rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c) (S.preserves c)

/-- The exact derived inverse image along a scheme automorphism, restricted to Dbc.
The preservation proof is precisely the existing reindexing theorem of strict Weil complexes.
Source: source proof, Step 4 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
abbrev pull {X : Scheme.{u}} (a : X ≅ X) : C ℓ X ⥤ C ℓ X :=
  (bc ℓ X).lift ((bc ℓ X).ι ⋙ StrictWeilCondensed.action (Profinite.padicAlgClRingObj ℓ) a)
    (fun K ↦ ((StrictWeilCondensed.action_preserves (Profinite.padicAlgClRingObj ℓ) a K.obj).1).2
      K.property)

/-- The specified compositor on a compatible compactification tower. Its middle map
is the unique identity-on-open normalized proper/open interchange, not an arbitrary map.
Source: source proof, Step 2 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def TowerNormalized {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    (Sh : System ℓ h) (Sg : System ℓ g) (Sgh : System ℓ (h ≫ g))
    (α : ∀ (c : Compactification h) (d : Compactification g)
      (e : Compactification (h ≫ g)), Sh.support ℓ c ⋙ Sg.support ℓ d ≅ Sgh.support ℓ e) :
    Prop :=
  ∀ (T : Compactification.Triangle h g) [QuasiCompact (T.cf.g ≫ T.cg.i)] (K : C ℓ X),
    TowerNormalizationLaw
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) T.cf.i).mapDerivedCategory)
      ((lowerStar (Profinite.padicAlgClRingObj ℓ) T.cf.g).rightDerivedFunctor)
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) T.cg.i).mapDerivedCategory)
      ((lowerStar (Profinite.padicAlgClRingObj ℓ) T.cg.g).rightDerivedFunctor)
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) T.q).mapDerivedCategory)
      ((lowerStar (Profinite.padicAlgClRingObj ℓ) T.p).rightDerivedFunctor)
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) T.cfg.i).mapDerivedCategory)
      ((lowerStar (Profinite.padicAlgClRingObj ℓ) (T.p ≫ T.cg.g)).rightDerivedFunctor)
      ((lowerStar (Profinite.padicAlgClRingObj ℓ) T.cfg.g).rightDerivedFunctor)
      (openFactor (Profinite.padicAlgClRingObj ℓ) T.cf.i T.q T.cfg.i T.i_q).hom
      (rightDerivedLowerStarComp (Profinite.padicAlgClRingObj ℓ) T.p T.cg.g).hom
      (Functor.rightDerivedFunctorNatIso
        (eqToIso (congrArg (fun t ↦ lowerStar (Profinite.padicAlgClRingObj ℓ) t) T.p_g))).hom
      (fun M m ↦ compositionInterchangeIsNormalized (Profinite.padicAlgClRingObj ℓ) T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T)) M m)
      K.obj ((α T.cf T.cg T.cfg).hom.app K).hom

/-- The map on geometric fibres is the actual base-change functor's map.
Source: finite-field geometric-fibre convention and source proof, Step 1
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def modelMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

end

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
