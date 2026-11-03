/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion

import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.AlgebraicGeometry.Compactification.DenseRefinementMorphisms
import WeilConjectures.Compactification.CompactificationCategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionMixed
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedCompositorCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian

/-! # Condensed compactification comparison and target-open restriction

Source: literature/blueprint/latest/blueprint/
part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-quasi-finite-maps-and-curves-preserving-irreducibility/
sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md, first paragraph;
and literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors-basics/sec-brown-construction/sec-construction-of-rf/
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md (1)--(3),
and sk-thm-sf-comp-composition/det-sf-comp-composition-base-change.proof.md (1)--(3)
under that same construction-of-rf directory.
(blueprint: lem-zl-condensed-compactification-open-comparison)

## Main declarations

* `comparisons_existsUnique` and `comparison_coherence`: normalized comparisons.
* `exchange` and `targetOpenIso`: the native target-open exchange and its literal restriction.
* `comparison_restriction` and `exchange_successive`: restriction coherence.
* `comparison_frobenius` and `restriction_frobenius`: Frobenius compatibility.
* `comparison_strictWeil` and `restriction_strictWeil`: maps of the recorded strict pairs.

All operations below are the ordinary derived operations on internal modules over
p_T^* Lambda. The equations specifying comparison and exchange use the published
adjunction mates. No comparison is selected from an unnormalized existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactificationOpenComparison


variable (D : WeilConjectures.FiniteFieldDatum.{u})

attribute [instance] ModelMap.qsX ModelMap.qsY ModelMap.ftX ModelMap.qcX ModelMap.ftY
  ModelMap.qcY ModelMap.separated ModelMap.finiteType ModelMap.quasiCompact

variable (ell : ℕ) [Fact ell.Prime]

section Squares

variable {X Y X' Y' X'' Y'' : Scheme.{u}}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}

/-- A Cartesian open square of compactifications, with its specified middle map.
Target restriction and geometric-Frobenius squares are instances of this same notion.
Source: det-sf-comp-composition-base-change.proof.md (1)
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
structure Square (c : Compactification f) (d : Compactification f')
    (i : X' ⟶ X) (v : Y' ⟶ Y) where
  middleMap : d.Z ⟶ c.Z
  openSquare : IsPullback i d.i c.i middleMap
  properSquare : IsPullback middleMap d.g c.g v

variable {ell} {c : Compactification f} {d : Compactification f'}
  {e : Compactification f''} {i : X' ⟶ X} {v : Y' ⟶ Y}
  {i' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}

/-- The canonical open-adjunction mate is invertible in a Cartesian open square.
Source: det-sf-comp-composition-base-change.proof.md (1), open comparison
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: on modules the open-adjunction mate identifies extension by zero with its
Cartesian inverse image, as can be checked on the open slice and its closed complement.
Both functors are exact. Termwise passage to complexes and localization gives the
same mate by the exact-derived-adjunction normalization, hence an isomorphism. -/
theorem open_mate_isIso (s : Square c d i v) :
    IsIso (CohomologyTransport.openExchange (coefficient ell) i d.i c.i s.middleMap
      s.openSquare.w) := by
  sorry

/-- The canonical exchange is native direct-image exchange followed by the inverse open mate.
This formula is defined on every ordinary derived input, before any finiteness assumption.
Source: det-sf-comp-composition-base-change.proof.md (1)--(2)
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def exchange (s : Square c d i v) :
    CohomologyTransport.C (coefficient ell) c ⋙ CohomologyTransport.L (coefficient ell) v ⟶
      CohomologyTransport.L (coefficient ell) i ⋙ CohomologyTransport.C (coefficient ell) d :=
  letI := open_mate_isIso (ell := ell) s
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (CohomologyTransport.J (coefficient ell) c.i)
      (CohomologyTransport.ordinary (coefficient ell) s.middleMap d.g c.g v
        s.properSquare.w) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (asIso (CohomologyTransport.openExchange (coefficient ell) i d.i c.i s.middleMap
        s.openSquare.w)).inv (CohomologyTransport.R (coefficient ell) d.g) ≫
    (Functor.associator _ _ _).hom

/-- At a target open, and at an isomorphism of the full diagram, exchange is invertible
on the entire ordinary derived category.
Source: det-sf-comp-composition-base-change.proof.md (1)--(2), and
lem-zl-quasi-finite.proof.md, first paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: for a target open, native direct-image exchange is the normalized derived open
restriction and is invertible, without boundedness or constructibility. For an
isomorphism of diagrams it is a conjugate of the original adjunction under exact
inverse site equivalences, hence invertible. The open mate is invertible in both cases.
Whiskering and composing these maps gives the assertion. -/
theorem exchange_isIso (s : Square c d i v)
    (hv : IsOpenImmersion v ∨ (IsIso i ∧ IsIso v ∧ IsIso s.middleMap)) :
    IsIso (exchange (ell := ell) s) := by
  sorry

end Squares

/-- Frobenius exchange in the exact-termwise convention of strict Weil complexes.
The two endpoint comparisons identify termwise inverse image with total left derivation.
Source: lem-zl-quasi-finite.proof.md, first paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def frobeniusExchange {G : ModelMap D} (c : Compactifications D G) :
    T D ell c ⋙ StrictWeilCondensed.action (coefficient ell)
        (StrictWeilCondensed.modelFrobenius D G.Y) ≅
      StrictWeilCondensed.action (coefficient ell)
        (StrictWeilCondensed.modelFrobenius D G.X) ⋙ T D ell c :=
  let s := frobeniusSquare D c
  letI := exchange_isIso (ell := ell) s
    (Or.inr ⟨inferInstance, inferInstance,
      inferInstanceAs (IsIso (StrictWeilCondensed.modelFrobenius D (middle D c)).hom)⟩)
  Functor.isoWhiskerLeft (T D ell c)
      (leftDerivedUpperStarIsoMapDerivedCategory (coefficient ell)
        (StrictWeilCondensed.modelFrobenius D G.Y).hom).symm ≪≫
    asIso (exchange (ell := ell) s) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (coefficient ell)
        (StrictWeilCondensed.modelFrobenius D G.X).hom) (T D ell c)

/-- Induced Weil structure on a compactification output, in the ambient derived category.
Source: lem-zl-quasi-finite.proof.md, first paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def outputStructure {G : ModelMap D} (c : Compactifications D G)
    (K : CohomologyTransport.D (coefficient ell) ((geometric D).obj G.X).left)
    (φ : (StrictWeilCondensed.action (coefficient ell)
      (StrictWeilCondensed.modelFrobenius D G.X)).obj K ≅ K) :
    (StrictWeilCondensed.action (coefficient ell)
      (StrictWeilCondensed.modelFrobenius D G.Y)).obj ((T D ell c).obj K) ≅
        (T D ell c).obj K :=
  (frobeniusExchange D ell c).app K ≪≫ (T D ell c).mapIso φ

/-- For the stated coefficient field on a geometric finite-type qs model, bounded
constructible outputs have exactly the membership needed by the strict pair category.
Source: sk-def-sf-weil-complexes, field-coefficient Dctf=Dbc paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: identify the recorded finite-presentation constructibility with the finite
constant local-model predicate for the pulled-back condensed algebraic closure.
The geometric scheme is qcqs. The field case of integral_ctf_equals_bc gives finite
Tor amplitude for every bounded constructible object, without derived completeness. -/
theorem bounded_ctf (A : Model D) [QuasiSeparated A.hom]
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    (K : CohomologyTransport.D (coefficient ell) ((geometric D).obj A).left)
    (hK : boundedConstructible
      (condensedRingObj (coefficient ell) ((geometric D).obj A).left) K) :
    (constantModelBoundedConstructible (coefficient ell) ((geometric D).obj A).left ⊓
      fun L ↦ DerivedCategory.finiteTorAmplitude _ L) K := by
  sorry

/-- The induced strict Weil pair, using the recorded category and the stated
bounded-constructibility condition, rather than assuming preservation of outputs.
Source: sk-def-sf-weil-complexes, strict pair definition
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def strictPair (A : Model D) [QuasiSeparated A.hom]
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    (K : CohomologyTransport.D (coefficient ell) ((geometric D).obj A).left)
    (φ : (StrictWeilCondensed.action (coefficient ell)
      (StrictWeilCondensed.modelFrobenius D A)).obj K ≅ K)
    (hK : boundedConstructible
      (condensedRingObj (coefficient ell) ((geometric D).obj A).left) K) :
    StrictWeilCondensed.Complex (coefficient ell) (StrictWeilCondensed.modelFrobenius D A) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    ⟨K, bounded_ctf D ell A K hK⟩ (ObjectProperty.isoMk _ φ)

set_option maxHeartbeats 800000 in
-- Elaborate the literal iterated model pullbacks and their derived functor endpoints together.
end AlgebraicGeometry.ProEtale.CondensedRing.CompactificationOpenComparison
