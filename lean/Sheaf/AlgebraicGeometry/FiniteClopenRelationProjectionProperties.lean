/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Finite arrows and étale projections of a clopen restriction

Source: Stacks Project, More on Groupoids, Tag 03X5,
`lemma-quasi-finite-over-base-j-proper`, the inverse image of the finite object square;
étale permanence as in the preceding `lemma-quasi-finite-over-base`
(blueprint: lem-a1-finite-clopen-relation-projection-properties).

The auxiliary constructions are the induced endpoint after base change, the iterated
restricted relation and its canonical endpoint, arrow and square maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace FiniteClopenRelation

variable {T U R B : Scheme.{u}}
variable (fU : U ⟶ T) (fR : R ⟶ T) (fB : B ⟶ T)

/-- The endpoint induced by base change to `B`.
Source: Stacks Project, Tag 03X5, base-changed relation
(blueprint: lem-a1-finite-clopen-relation-projection-properties). -/
noncomputable abbrev baseChangeEndpoint (s : R ⟶ U) (hs : s ≫ fU = fR) :
    pullback fR fB ⟶ pullback fU fB :=
  pullback.map fR fB fU fB s (𝟙 B) (𝟙 T) (by simp [hs]) (by simp)

variable (s t : R ⟶ U) (hs : s ≫ fU = fR) (ht : t ≫ fU = fR)
variable (V : (pullback fU fB).Opens)

/-- The actual iterated fibre product `V ×_{U_B} R_B ×_{U_B} V`.
Source: Stacks Project, Tag 03X5, restriction to the object square
(blueprint: lem-a1-finite-clopen-relation-projection-properties). -/
noncomputable abbrev restriction : Scheme.{u} :=
  pullback
    (pullback.snd V.ι (baseChangeEndpoint fU fR fB s hs) ≫
      baseChangeEndpoint fU fR fB t ht) V.ι

/-- The first endpoint of the restricted relation.
Source: Stacks Project, Tag 03X5, restricted endpoint
(blueprint: lem-a1-finite-clopen-relation-projection-properties). -/
noncomputable abbrev source : restriction fU fR fB s t hs ht V ⟶ V.toScheme :=
  pullback.fst
      (pullback.snd V.ι (baseChangeEndpoint fU fR fB s hs) ≫
        baseChangeEndpoint fU fR fB t ht) V.ι ≫
    pullback.fst V.ι (baseChangeEndpoint fU fR fB s hs)

/-- The second endpoint of the restricted relation.
Source: Stacks Project, Tag 03X5, restricted endpoint
(blueprint: lem-a1-finite-clopen-relation-projection-properties). -/
noncomputable abbrev target : restriction fU fR fB s t hs ht V ⟶ V.toScheme :=
  pullback.snd
    (pullback.snd V.ι (baseChangeEndpoint fU fR fB s hs) ≫
      baseChangeEndpoint fU fR fB t ht) V.ι

/-- The canonical arrow-forgetting map to `R_B`.
Source: Stacks Project, Tag 03X5, inverse image of the object square
(blueprint: lem-a1-finite-clopen-relation-projection-properties). -/
noncomputable abbrev toRelation : restriction fU fR fB s t hs ht V ⟶ pullback fR fB :=
  pullback.fst
      (pullback.snd V.ι (baseChangeEndpoint fU fR fB s hs) ≫
        baseChangeEndpoint fU fR fB t ht) V.ι ≫
    pullback.snd V.ι (baseChangeEndpoint fU fR fB s hs)

/-- The canonical pair of endpoints into the finite object square.
Source: Stacks Project, Tag 03X5, inverse image of the object square
(blueprint: lem-a1-finite-clopen-relation-projection-properties). -/
noncomputable abbrev toSquare : restriction fU fR fB s t hs ht V ⟶
    pullback (V.ι ≫ pullback.snd fU fB) (V.ι ≫ pullback.snd fU fB) :=
  pullback.lift (source fU fR fB s t hs ht V) (target fU fR fB s t hs ht V) (by
    simp only [source, target, Category.assoc]
    rw [pullback.condition_assoc (f := V.ι)
      (g := baseChangeEndpoint fU fR fB s hs)]
    rw [← pullback.condition_assoc
      (f := pullback.snd V.ι (baseChangeEndpoint fU fR fB s hs) ≫
        baseChangeEndpoint fU fR fB t ht) (g := V.ι)]
    simp only [Category.assoc, baseChangeEndpoint, pullback.map,
      pullback.lift_snd, Category.comp_id])

end FiniteClopenRelation

open FiniteClopenRelation

/-- A clopen restriction of a closed relation with étale endpoints has finite arrows
and étale endpoints. No equivalence-relation operations or axioms are assumed.

Source: Stacks Project, More on Groupoids, Tag 03X5,
`lemma-quasi-finite-over-base-j-proper`, closed-immersion specialization of the
restricted-relation argument, and the preceding `lemma-quasi-finite-over-base`
(blueprint: lem-a1-finite-clopen-relation-projection-properties).

Proof:
1. By the universal property in def-pc-fibre-product, the base-changed object square
is the base change of `U ×_T U`, and `R_B` is the corresponding base change of `R`.
The iterated fibre product defining `restriction` is the inverse image of `V ×_B V`.
All identifications preserve the two endpoints.
2. Apply lem-weil-pbc-closed-immersion-base-change twice to `j = (s,t)`.
The result is `toSquare`, hence a closed immersion. By
lem-weil-pbc-closed-immersion-finite it is finite.
3. The projection `V ×_B V → V` is finite by
lem-weil-pbc-finite-morphism-permanence, since `V → B` is finite.
Apply lem-weil-pbc-finite-composition to obtain finiteness of `V ×_B V → B`,
and then of `restriction → B`.
4. The two pullbacks of the open inclusion `V.ι` are open immersions by
lem-weil-pbc-open-immersion-base-change. Their composite is `toRelation` and has
image `s_B⁻¹(V) ∩ t_B⁻¹(V)`. Both inverse images are clopen by continuity, so their
intersection is clopen. The pullback scheme structures are the restricted sheaves.
5. The base-changed endpoints are étale by lem-weil-pbc-etale-scheme-base-change.
The first restricted endpoint factors through the étale base change to `V`, followed
on its source by the open restriction imposed by the other endpoint. Open immersions
are étale and composites are étale by lem-weil-pbc-etale-composition-cancellation.
The second endpoint is symmetric. None of these steps uses relation axioms.
-/
theorem finite_clopen_relation_projection_properties
    (T U R B : Scheme.{u})
    (fU : U ⟶ T) (fR : R ⟶ T) (fB : B ⟶ T)
    (s t : R ⟶ U) (hs : s ≫ fU = fR) (ht : t ≫ fU = fR)
    [Etale s] [Etale t]
    [IsClosedImmersion (pullback.lift s t (hs.trans ht.symm))]
    (V : (pullback fU fB).Opens) (_hV : IsClosed (V : Set (pullback fU fB : Scheme.{u})))
    [IsFinite (V.ι ≫ pullback.snd fU fB)] :
    IsClosedImmersion (toSquare fU fR fB s t hs ht V) ∧
    IsFinite (toSquare fU fR fB s t hs ht V) ∧
    IsFinite
      (pullback.fst (V.ι ≫ pullback.snd fU fB) (V.ι ≫ pullback.snd fU fB) ≫
        V.ι ≫ pullback.snd fU fB) ∧
    IsFinite (toRelation fU fR fB s t hs ht V ≫ pullback.snd fR fB) ∧
    IsOpenImmersion (toRelation fU fR fB s t hs ht V) ∧
    Set.range (toRelation fU fR fB s t hs ht V) =
      (baseChangeEndpoint fU fR fB s hs) ⁻¹' (V : Set (pullback fU fB : Scheme.{u})) ∩
        (baseChangeEndpoint fU fR fB t ht) ⁻¹' (V : Set (pullback fU fB : Scheme.{u})) ∧
    IsClopen (Set.range (toRelation fU fR fB s t hs ht V)) ∧
    Etale (source fU fR fB s t hs ht V) ∧
    Etale (target fU fR fB s t hs ht V) := by
  sorry

end AlgebraicGeometry
