/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.SupportedModelHull
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Strict bounded filtered diagrams after direct image

Source: steps 5--6 of lem-sfb-supported-hull-proetale-descent, using bounded
continuity of pro-etale direct image, HRS Lemma 5.3(1).
(blueprint: lem-sfb-supported-pushforward-strict-colimit).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The inverse image of an admissible class under qcqs derived direct image has
its required closure under strict filtered diagrams with a common termwise bound.
This is only the colimit clause, not preservation of hull generators.

Source: steps 5--6 of lem-sfb-supported-hull-proetale-descent; HRS Lemma 5.3(1)
for bounded continuity and Stacks derived.tex, Tag 013K, for simultaneous resolutions.
(blueprint: lem-sfb-supported-pushforward-strict-colimit)

Proof: regard D as one bounded-below complex in the Grothendieck category of
small I-diagrams of module sheaves. The all-lower-bounds Cartan--Eilenberg theorem
and its total-resolution theorem give a strict quasi-isomorphism D to H, where H
has the same lower bound and termwise injective diagrams. Evaluation preserves
injectives: its left adjoint is the coproduct indexed by each hom set, which is
exact because arbitrary sums are filtered colimits of finite sums. Thus every
H_i is bounded below with injective terms and is K-injective. The complexes b_*H_i
strictly represent Rb_*QD_i and have the same common lower bound. Apply the
colimit clause of hP to them. The canonical comparison from Q(colim b_*H_i) to
Rb_*Q(colim H_i) is an isomorphism on every cohomology sheaf by bounded continuity.
Exact filtered colimits also make colim D_i to colim H_i a quasi-isomorphism.
Transport membership through these two isomorphisms and through the unique
comparison from the chosen colimit to c. This proves the assertion for every
colimit cocone; no unbounded continuity assertion or compatibility choice of local
generation expressions is used. Zero diagrams and all integer lower bounds remain
allowed.
-/
theorem supportedModelClass_pushforward_strictColimit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (U V : Scheme.{u})
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace V] [QuasiSeparatedSpace V]
    (b : U ⟶ V) [WeaklyEtale b] [QuasiCompact b] [QuasiSeparated b]
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))))
    (hP : IsSupportedModelHullClass Λ V P)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ℤ)
    (a : ℤ) (hD : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).X n))
    (hmem : ∀ i : I, P ((CondensedRing.moduleObjectDerivedPushforward Λ b).obj
      (DerivedCategory.Q.obj (D.obj i))))
    (c : Cocone D) (hc : IsColimit c) :
    P ((CondensedRing.moduleObjectDerivedPushforward Λ b).obj
      (DerivedCategory.Q.obj c.pt)) := by sorry

end AlgebraicGeometry.ProEtale
