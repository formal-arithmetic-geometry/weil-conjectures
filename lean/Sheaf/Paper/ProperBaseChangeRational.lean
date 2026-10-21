/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.BoundedConstructibleBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.ModuleObjectProjectionMap

public import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.Paper.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.CoefficientHeartTriangulated
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.CartesianCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.Paper.IntegralModelsOperations
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.SixFunctors.IntegralModelsGenerators
import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Proper direct image with rational condensed coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.md, clauses 1--3
(blueprint: det-thm-sfb-proper-base-change-rational).

The three coefficient comparisons are the existing derived push mates. Bounded
constructibility is the recorded ambient internal-module predicate. Base change uses the
recorded conditional restriction with its preservation proof supplied by the existing
finiteness-coefficient interface. Projection uses the existing canonical module-object mate.
The rational cases are expressed by equality of bundled coefficient ring objects.
This fixes the ring operations as well as the underlying sheaf.

## Main statements

* `isIso_rationalizationPushHom_boundedBelow`: localization commutes with proper pushforward.
* `isIso_finiteCoefficientPushHom_boundedBelow` and
  `isIso_algClCoefficientPushHom_boundedBelow`: the other two coefficient comparisons.
* `properPushforward_boundedConstructible_rational`: preservation of bounded constructibility.
* `isIso_properProjectionMap_boundedConstructible_rational`: the specified projection mate.
* `isIso_properBaseChange_boundedConstructible_rational`: the specified exchange components.

The helper `rationalCoefficientPushforwardPreservation` supplies the existing preservation
proof by the displayed ring equality; it introduces no preservation assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical push comparison for the coefficient inclusion O_E -> E. Its definition
only supplies the flatness proof to the recorded `derivedPushHom`; it does not choose a map.
Source: blueprint rational proper direct image, clause 1, and its proof steps 1--2
(blueprint: det-thm-sfb-proper-base-change-rational). -/
def rationalizationPushHom (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (lowerStar (Profinite.padicIntegersRingObj ℓ E.1) p).rightDerivedFunctor ⋙
        (Mod.extendScalars (padicIntegersToPadicSubfield Y ℓ E)).leftDerivedFunctor ⟶
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor ⋙
        (lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor :=
  letI : ∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) Z)) :=
    fun Z ↦ Exists.elim (padicIntegers_invertEll Z ℓ E) fun _ hj ↦
      Exists.elim hj.2 fun _ ht ↦ Exists.elim ht.2.2 fun _ hα ↦ hα.2.2.2
  derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) p

/-- The existing finiteness-coefficient preservation proof, named to avoid repeated expansion
in the canonical restricted base-change map. This supplies a proof, never extra map data.
Source: blueprint rational proper direct image, clauses 2--3
(blueprint: det-thm-sfb-proper-base-change-rational). -/
abbrev rationalFinitenessPushforwardPreservation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    [IsFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    PreservesBoundedConstructiblePushforwards Λ k :=
  fun f K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f K.obj K.property

attribute [local irreducible] upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedPushSource derivedPushTarget
  moduleObjectProjectionMap rationalizationPushHom boundedConstructibleBaseChangeOfPreserves

/-- The named preservation proof for precisely the two rational coefficient cases.
The bundled ring equality fixes multiplication as well as the underlying coefficient sheaf.
Source: blueprint rational proper direct image, clauses 2--3
(blueprint: det-thm-sfb-proper-base-change-rational). -/
abbrev rationalCoefficientPushforwardPreservation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    PreservesBoundedConstructiblePushforwards Λ.X k := by
  rcases hΛ with ⟨E, hE⟩ | hQ
  · subst Λ
    exact rationalFinitenessPushforwardPreservation (Profinite.continuousMapRingObj E) ℓ
  · subst Λ
    exact rationalFinitenessPushforwardPreservation (Profinite.padicAlgClRingObj ℓ) ℓ

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

include k in
/-- Proper pushforward commutes with inverting ell on every bounded-below integral complex.
Source: blueprint rational proper direct image, clause 1
(blueprint: det-thm-sfb-proper-base-change-rational).

Proof (steps 1--2): properness gives qcqs. Use the coefficient localization and flatness of
`det-prop-sfb-qlbar-colimit-x-invert-ell`, so a bounded-below representative stays bounded
below after scalar extension. Tensor that representative with the fraction cocone. By
`lem-pc-module-filtered-colimits-tensor`, localization is the termwise filtered colimit of
multiplication by ell. Apply `det-pe-bounded-continuity-direct-image` to this common-lower-bound
diagram. Its cohomology comparison is the specified mate: the nth leg is the original
coefficient inclusion multiplied by ell^(-n). The long exact cohomology sequence makes its
cone acyclic; the derived localization inverts it. Restriction of scalars reflects this
isomorphism, and `def-sfb-derived-comap-lower-star-iso` identifies the two pushforwards.
-/
theorem isIso_rationalizationPushHom_boundedBelow
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)))
    (_hK : DerivedCategory.TStructure.t.plus K) :
    IsIso ((rationalizationPushHom ℓ E p.left).app K) := by
  sorry

include k in
/-- Proper pushforward commutes with a finite coefficient extension on bounded-below objects.
Source: blueprint rational proper direct image, clause 1
(blueprint: det-thm-sfb-proper-base-change-rational).

Proof (steps 1 and 3): `det-prop-sfb-cartesian-coefficients-finite-free` identifies scalar
extension after restriction with a finite sum using an integral basis. A right adjoint
preserves finite products, hence finite sums in the additive derived category, by
`lem-weil-pbc-right-adjoint-preserves-limits`. The inclusion of the summand indexed by b_i
is k -> b_i tensor k; pullback compatibility of the basis identifies these with the actual
summand maps of `def-sfb-derived-push-hom`. The restricted comparison is therefore invertible.
`def-sfb-derived-comap-lower-star-iso` compares pushforwards, and restriction reflects
isomorphisms. No constructibility hypothesis is used.
-/
theorem isIso_finiteCoefficientPushHom_boundedBelow
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)))
    (_hK : DerivedCategory.TStructure.t.plus K) :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) p.left).app K) := by
  sorry

include k in
/-- Proper pushforward commutes with extension to finite-subextension-valued condensed Qlbar.
Source: blueprint rational proper direct image, clause 1
(blueprint: det-thm-sfb-proper-base-change-rational).

Proof (steps 1 and 4): finite subextensions containing E are cofinal, by taking composita.
`sk-prop-sfb-qlbar-colimit-x` and tensor-colimit compatibility express scalar extension as the
filtered colimit of the finite extensions. Flatness `lem-sfb-qlbar-flat` preserves the fixed
lower bound. Apply bounded continuity and the finite-extension comparison at every stage.
Naturality of the mates makes their colimit exactly the Qlbar mate. The acyclic-cone argument
and reflection by restriction prove invertibility in the Qlbar derived category. For the
composite O_E -> E -> Qlbar, scalar transitivity and the adjunction triangle identities
identify the composed comparisons with the direct comparison, as in
`det-prop-scalar-six-pullback`.
-/
theorem isIso_algClCoefficientPushHom_boundedBelow
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)))
    (_hK : DerivedCategory.TStructure.t.plus K) :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left).app K) := by
  sorry

/-- Proper pushforward preserves bounded constructible complexes with rational coefficients.
Source: blueprint rational proper direct image, clause 2
(blueprint: det-thm-sfb-proper-base-change-rational).

Proof (step 5): by `det-lem-integral-models-generators`, reduce to integral lattice generators
extended by zero. The integral proper theorem puts their images in integral Dbc. The
coefficient comparisons of clause 1 and `lem-sfb-extend-scalars-bounded-constructible` and
`lem-sfb-extend-to-qlbar-constructible` put their rational images in Dbc; scalar transitivity
handles Qlbar. Standing schemes are Noetherian by finite type over k. Pushforward is
triangulated by `lem-pc-right-derived-functor-triangulated`; target Dbc is closed under zero,
isomorphisms, shifts and cones by `det-cor-coefficient-heart-ii-triangulated`. Induct over the
finite cone-and-shift generation to obtain preservation for all bounded constructible K.
-/
theorem properPushforward_boundedConstructible_rational
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (_hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ.X X.left)))
    (_hK : boundedConstructible (condensedRingObj Λ.X X.left) K) :
    boundedConstructible (condensedRingObj Λ.X Y.left)
      ((lowerStar Λ.X p.left).rightDerivedFunctor.obj K) := by
  sorry

/-- The specified proper projection formula is invertible on bounded constructible objects.
Source: blueprint rational proper direct image, clause 3, projection formula
(blueprint: det-thm-sfb-proper-base-change-rational).

Proof (steps 6, 8--11): the canonical scalar/pull/tensor comparisons on K-flat representatives
send s tensor (a tensor b) to (s tensor a) tensor (1 tensor b); these equalities give their
composition and tensor coherence. Choose a common finite coefficient field for any pair of
Qlbar generators by taking a compositum. Finite-free integral extension carries both lattices
to lattices over this common field; scalar extension commutes with extension by zero.
For an integral pair, `det-lem-integral-models-operations` puts K tensor p* M in integral Dbc.
Transpose the two coefficient/projection routes using the geometric adjunction. Use the
counit equation for the push mate, and naturality of the pull and tensor comparisons: both
adjuncts are the scalar extension of (counit tensor 1) followed by the canonical tensor map.
Thus the two routes are equal. The integral projection map is invertible by
`det-thm-sfb-proper-base-change-integral`, and the coefficient push comparisons are invertible
by clause 1, proving the rational map invertible on generator pairs. By
`lem-weil-pbc-ringed-projection-mate-exact`, derived tensor is exact and its comparison
commutes with shifts. The adjoint shift compatibility, triangulated right adjoint, and
composition/whiskering lemmas give the connecting square for the actual mate in both
variables. Apply `lem-sf-triangle-two-out-of-three` and generation first in K for a fixed
M-generator, then in M for arbitrary K. This proves invertibility for every Dbc pair.
-/
theorem isIso_properProjectionMap_boundedConstructible_rational
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (_hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ.X X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ.X Y.left)))
    (_hK : boundedConstructible (condensedRingObj Λ.X X.left) K)
    (_hM : boundedConstructible (condensedRingObj Λ.X Y.left) M) :
    IsIso (moduleObjectProjectionMap Λ.X p.left K M) := by
  sorry

variable {X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The recorded unit--square--counit base-change map is invertible for every proper
cartesian square in the standing setting, with no condition on g.
Source: blueprint rational proper direct image, clause 3, proper base change
(blueprint: det-thm-sfb-proper-base-change-rational).

Proof (steps 6--7 and 10--11): use the canonical scalar pull comparison, push mate and
K-flat tensor normalization of step 6. Properness is stable under base change. An integral
lattice generator and its pullback are in integral Dbc by
`det-lem-integral-models-operations`, so clause 1 inverts the two proper coefficient mates.
The restricted unit--square--counit definition is the restriction of the ambient one.
Transpose under p'^* adjoint Rp'_*; a triangle identity gives its exchange counit equation.
Apply `lem-weil-pbc-coefficient-exchange-mates` with this equation, the geometric counit
identity for coefficient mates, and the balanced-tensor pull-comparison cube. The resulting
commuting square identifies the actual rational exchange component with the integral one
and invertible comparisons. The integral theorem inverts the integral component.
Adjunction-compatible shifts, `lem-sf-triangulated-right-adjoint` and
`lem-weil-pbc-commshift-nattrans-comp-whisker` make this exact transformation commute with
shifts, including the connecting square. By `lem-sf-triangle-two-out-of-three` and
`det-lem-integral-models-generators`, invertibility extends through shifts and cones from
generators to all of Dbc. Components are invertible in the full subcategory, hence the
natural transformation is invertible. No smoothness or properness of g is used.
-/
theorem isIso_properBaseChange_boundedConstructible_rational
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (sq : IsPullback g' p' p g)
    (K : ProEtale.BoundedConstructible
      (condensedRingObj Λ.X X.left)) :
    IsIso ((boundedConstructibleBaseChangeOfPreserves Λ.X ℓ
      (rationalCoefficientPushforwardPreservation ℓ Λ hΛ)
      sq.toCommSq).app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
