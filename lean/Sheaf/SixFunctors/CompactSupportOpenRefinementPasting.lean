/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.SixFunctors.CompactSupportProperTriangle

/-!
# Local open-adjunction equation for compactification refinement

Source: blueprint det-sf-comp-composition-base-change, proof (3), before applying Rp'_*.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The local equation before applying the final proper direct image.

Source: blueprint det-sf-comp-composition-base-change, proof (3), the maps from the
base-changed extension by zero into the direct image from a common refinement.
(blueprint: lem-sfb-compact-support-open-refinement-pasting).

Proof: the supplied equality esr identifies the two ambient refinement maps into
c after pullback. Their open triangles identify both restrictions with the same
map on the source open. The inverses of oc and od are the specified open exchanges,
so after transposing by the open adjunction their contribution is the canonical
pullback comparison and the open unit. The refinement maps are, by definition,
the adjuncts of the inverse restriction isomorphisms followed by the open units.
Restrict the proper mate for h to that same open: since h is the identity there,
the two units and counits cancel by the adjunction triangle identities, and the
remaining pullback comparison is the canonical one on the open. Substituting the
normalization of each refinement, the adjunct of each side is thus the open unit
followed by the inverse restriction for hc. Composition of the restriction mates
uses the derived direct-image compositor normalized on K-injectives, exactly the
triangle appearing on the left. Injectivity of the open-adjunction Hom equivalence,
after precomposing with the isomorphism oc, proves the equality. No final direct
image to Y' is applied in this statement. It uses neither density nor any proper
base-change isomorphism or localizing condition, and works for empty opens and
arbitrary unbounded complexes. -/
theorem compactSupportOpenRefinement_pasting
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c : Compactification f) (d : Compactification.BoundaryCompactification f)
    (oc : D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧))
    (od : D((d.obj.obj.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((d.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (hoc : oc.inv = detSfOpenBaseChangeMap Λ f v c)
    (hod : od.inv = detSfOpenBaseChangeMap Λ f v d.obj.obj)
    (h : d ⟶ detSfBoundaryCompactification c)
    (w : Compactification.BoundaryCompactification (pullback.snd f v))
    (hd : w ⟶ detSfBoundaryCompactification (d.obj.obj.baseChange v))
    (hc : w ⟶ detSfBoundaryCompactification (c.baseChange v))
    (esr : hd.hom.hom.hom ≫
        compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g h.hom.hom.hom_g v =
      hc.hom.hom.hom)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (detSfDerivedPullback Λ (pullback.fst c.g v)).map (localizingRefinementMap Λ h K) ≫
      (condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare
        h.hom.hom.hom c.g d.obj.obj.g h.hom.hom.hom_g v)).app (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) ≫
      R((compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g h.hom.hom.hom_g v)_*⟦Λ⟧).map
        (od.hom.app K ≫ localizingRefinementMap Λ hd
          ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) ≫
      (compactSupportPushforwardTriangle Λ hd.hom.hom.hom
        (compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g h.hom.hom.hom_g v)
        hc.hom.hom.hom esr).hom.app
          (D((w.obj.obj.i)_!open⟦Λ⟧).obj
            ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) =
    oc.hom.app K ≫ localizingRefinementMap Λ hc
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
