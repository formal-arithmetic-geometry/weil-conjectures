/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.CompletionMapForLocalHom

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.IntegersExcellent
import WeilConjectures.RingTheory.CompleteLocalGRing
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.PopescuSmoothing
import WeilConjectures.RingTheory.RegularComposition

/-! # Relative étale approximation from an isomorphism of completed local rings

Source: Stacks Project, `more-morphisms.tex`, Tag 0GDX,
`lemma-relative-map-approximation-pre`, specialized to bases of finite type over `Spec ℤ`.
(blueprint: lem-trf-relative-completion-etale-approximation)
This statement is refreshed by group Q48 on 2026-10-18.
Its canonical helper constructions are unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The canonical map from the completed local base to the second base, defined by `σ`.
Source: Stacks Project, Tag 0GDX, definition of `Y_σ`.
(blueprint: lem-trf-relative-completion-etale-approximation) -/
def relativeCompletionFormalBaseMap {S T : Scheme.{u}} (s : S) (t : T)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) :
    Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))) ⟶ T :=
  Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t

/-- The canonical closed point of the completed local base: the inverse image of the zero
prime of the residue field under the first completion coordinate. For the Noetherian local
rings in Tag 0GDX this is the unique closed point.
Source: Stacks Project, Tag 0GDX; Algebra, Tags 05GG and 05GI.
(blueprint: lem-trf-relative-completion-etale-approximation) -/
def relativeCompletionClosedPoint {S : Scheme.{u}} (s : S) :
    Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))) :=
  PrimeSpectrum.comap
    (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (S.presheaf.stalk s))).toRingHom
    ⟨⊥, inferInstance⟩

/-- Relative approximation with the canonical completed-base scalar maps.
The point `s` of the source statement is written as `f x`. The map from its completion to
that of `𝒪_{X,x}` is the completion of the local stalk map, characterized in every finite
quotient by `RingHom.exists_adicCompletion_map_of_local`. The map into the second completed
stalk is constants on `Spec(Â)`, followed by the projection's stalk map and completion.
The equation in `hformal` expresses exactly compatibility with these two scalar maps.

Source: Stacks Project, Tag 0GDX, `lemma-relative-map-approximation-pre`.
(blueprint: lem-trf-relative-completion-etale-approximation)

Proof:
1. Restrict to affine neighbourhoods. The bases are Noetherian and their local rings are
   excellent, hence G-rings, because they are of finite type over the excellent ring ℤ.
   The two locally finite type families become finitely presented on these affines.
2. Put B = Spec(Â). Its ring is Noetherian, local, complete and a G-ring, with residue field
   κ(s). Completed-local base change identifies the completion of X ×_S B at the point over
   x with the completion at x. Tag 0CAV applied to the given scalar-compatible isomorphism
   supplies an elementary étale span over B between X ×_S B and Y_σ.
3. The map from the affine coordinate ring of S to Â is regular: localization is regular,
   and the G-ring completion map is regular. Popescu smoothing writes B as a directed
   inverse limit of affine smooth S-schemes S_i. The image s_i of B's closed point has
   residue field κ(s), since κ(s) → κ(s_i) → κ(s) has identity composite.
4. Finite presentation of T over ℤ factors B → T through some S_i → T. Fix the target
   families X_i = X ×_S S_i and Y_i = Y ×_T S_i. After shrinking the span to an affine
   neighbourhood of its marked point, finite-presentation descent (Tags 01ZM and 07RP)
   descends the span and both étale arrows to a common stage, retaining the fixed target
   families and the marked residue-field isomorphisms.
5. The smooth map S_i → S has κ(s_i) = κ(s). Thus s_i is closed in its fibre and has
   separable residue extension. Tag 057G gives an immersion V → S_i through s_i, étale
   over S; shrink S_i so the immersion is closed. Its marked point v has κ(v) = κ(s).
   Restrict S_i → T to obtain τ, with τ(v) = t.
6. Pull the descended span back to V. The resulting U → X ×_S V and U → Y ×_T V are
   the actual base changes of the two étale stage arrows, hence étale; the composite
   U → X is étale as well. The fibre over the descended marked point is Spec of its
   residue field, since the ideal of V vanishes there. Its unique point u has
   κ(u) = κ(x), maps to v and x, and all triangles commute by the pullback identities.
   These are exactly the asserted diagram and residue isomorphisms; no agreement with
   the original formal isomorphism is required in the conclusion. -/
theorem relative_completion_etale_approximation
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ T)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (sZ : S ⟶ Spec (.of (ULift.{u} ℤ)))
    (tZ : T ⟶ Spec (.of (ULift.{u} ℤ)))
    [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    [LocallyOfFiniteType tZ] [QuasiCompact tZ]
    (x : X) (y : Y) (t : T) (hyt : g y = t)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
        (S.presheaf.stalk (f x))) [IsLocalHom σ]
    (yσ : pullback (C := Scheme.{u}) g (relativeCompletionFormalBaseMap (f x) t σ))
    (hyσ : pullback.fst g (relativeCompletionFormalBaseMap (f x) t σ) yσ = y)
    (hb : pullback.snd g (relativeCompletionFormalBaseMap (f x) t σ) yσ =
      relativeCompletionClosedPoint (f x))
    (hformal : ∃ e :
        AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
        AdicCompletion
          (IsLocalRing.maximalIdeal
            ((pullback g (relativeCompletionFormalBaseMap (f x) t σ)).presheaf.stalk yσ))
          ((pullback g (relativeCompletionFormalBaseMap (f x) t σ)).presheaf.stalk yσ),
      e.toRingHom.comp
          (Classical.choose (RingHom.exists_adicCompletion_map_of_local (f.stalkMap x).hom)) =
        (algebraMap
          ((pullback g (relativeCompletionFormalBaseMap (f x) t σ)).presheaf.stalk yσ)
          (AdicCompletion
            (IsLocalRing.maximalIdeal
              ((pullback g (relativeCompletionFormalBaseMap (f x) t σ)).presheaf.stalk yσ))
            ((pullback g (relativeCompletionFormalBaseMap (f x) t σ)).presheaf.stalk yσ))).comp
          (((pullback.snd g (relativeCompletionFormalBaseMap (f x) t σ)).stalkMap yσ).hom.comp
            (StructureSheaf.toStalk
              (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
                (S.presheaf.stalk (f x)))
              ((pullback.snd g (relativeCompletionFormalBaseMap (f x) t σ)) yσ)).hom)) :
    ∃ (V : Scheme.{u}) (v : V) (a : V ⟶ S) (τ : V ⟶ T)
      (U : Scheme.{u}) (u : U) (w : U ⟶ V)
      (e : U ⟶ X) (m : U ⟶ pullback g τ),
      a v = f x ∧ τ v = t ∧ e u = x ∧ w u = v ∧
        w ≫ a = e ≫ f ∧ m ≫ pullback.snd g τ = w ∧
        Etale a ∧ Etale e ∧ Etale m ∧
        IsIso (a.residueFieldMap v) ∧ IsIso (e.residueFieldMap u) := by
  sorry

end AlgebraicGeometry
