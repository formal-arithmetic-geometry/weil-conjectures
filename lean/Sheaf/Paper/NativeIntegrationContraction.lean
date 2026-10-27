/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.CompositeIntegrationOperations

/-! # Native integration maps and their structural identities -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityIntegration

variable {C E T : Type w} [Category.{v} C] [Category.{v} E] [Category.{v} T]
  [MonoidalCategory C] [MonoidalCategory E] [MonoidalCategory T]
  [BraidedCategory C] [BraidedCategory E] [BraidedCategory T]

/-- Precompositor contraction, before the projection/compositor identity is used.
Source: expanded Steps 1--4 of the composite-integration calculation
(blueprint: lem-pur-native-precompositor-contraction). -/
def PrecompositorContraction (o : CompositeOperations C E T) : Prop :=
  ∀ (d : CompositeIntegrationData o) (K : T) (hK : d.domainZ K),
    let L := compositeTwist o d.Lf d.Lg
    d.compositeCounit K hK =
      o.fg.F.map (β_ (o.fg.P.obj K) L).hom ≫
      o.fg.F.map (L ◁ (o.pullComp.app K).inv) ≫
      (o.alpha (L ⊗ o.f.P.obj (o.g.P.obj K))
        (d.origin _ (d.tensor_f _ _ d.mem_fg (d.pull_g K hK)))).inv ≫
      o.g.F.map (q o.f L (o.g.P.obj K) (d.pf_f _ _ d.mem_fg (d.pull_g K hK))) ≫
      q o.g (o.f.F.obj L) K (d.pf_g _ _ (d.af.push_closed _ d.mem_fg) hK) ≫
      ((o.g.F.map (q o.f d.Lf d.Lg (d.pf_f _ _ d.mem_f d.mem_g)) ≫
        o.g.F.map (trace d.af d.unitY ▷ d.Lg) ≫ o.g.F.map (λ_ d.Lg).hom ≫
        trace d.ag d.unitZ) ▷ K) ≫ (λ_ K).hom

/-- The selected site's actual operations and canonical braidings.
Source: site-wise calculation (blueprint: lem-pur-native-precompositor-contraction). -/
def nativeContractionAssertion
    (b : Bool) (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] : Prop :=
  match b with
  | false =>
      letI := nativeBraiding (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} R))
      letI := nativeBraiding (Sheaf (Y.smallEtaleTopology) (ModuleCat.{u + 1} R))
      letI := nativeBraiding (Sheaf (Z.smallEtaleTopology) (ModuleCat.{u + 1} R))
      PrecompositorContraction (etaleOperations R f g)
  | true =>
      letI := nativeBraiding (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))
      letI := nativeBraiding (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R))
      letI := nativeBraiding (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
      PrecompositorContraction (proEtaleOperations R f g)

/-- Successive native trace contractions, before projection/compositor cancellation.
Source: blueprint, `lem-pur-projection-purity-agreement.proof.md`, final canonical
reassociations, expanded Steps 1--4; Stacks 0DV0
(blueprint: lem-pur-native-precompositor-contraction).

Proof: expand the composite counit by `Adjunction.comp_counit_app`. Substitute the
supplied f and g coefficient counit formulas. Move the symmetry of Pg K and Lg through
the f counit by naturality. Pullback tensor naturality and its compatibility with the
Koszul braiding, followed by the hexagon identity, identify the source reassociation
with the displayed symmetry, inverse pullback composition, and sigma of
`tensorAction_trace_contraction`. Apply that existing lemma to the native projection
natural transformations and the supplied action_f. The permitted projection pairs are
`domainX M ∧ domainY N` and `domainY M ∧ domainZ N`; twist_closed, tensor_f, pull_g and
push_closed provide all five needed memberships. Use the traces of af and ag as the two
maps to the tensor units. Their first contraction is q_f followed by trace_f tensor
identity and lambda. Applying Fg and composing trace_g gives the four displayed trace
factors. Functoriality gives the claimed equality. This calculation is performed for
each site's actual maps and canonical pullback comparisons; no projection/compositor
identity or inverse projection for fg is used. -/
theorem nativePrecompositorContraction
    (b : Bool) (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    nativeContractionAssertion b R f g := by
  sorry

end WeilConjectures.PurityIntegration
