/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite

/-! # Base change and topology of finite morphisms of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 03ZQ, 03ZS, 0414, 0415 and 04NY;
Properties of Spaces, Tags 03BX and 03H4
(blueprint: lem-sfb-finite-space-morphism-topology).

Finiteness uses scheme-test representability, with the existing scheme finiteness
predicate. The point map and topology are the canonical field-valued point constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism finite on scheme tests remains so after every algebraic-space base change.
Its point map is continuous and closed with finite fibres, and its scheme pullback along
every representable étale scheme chart is locally quasi-finite in the Stacks sense.
Source: Stacks Project, Morphisms of Spaces, Tags 03ZQ, 03ZS, 0414, 0415 and 04NY;
Properties of Spaces, Tags 03BX and 03H4
(blueprint: lem-sfb-finite-space-morphism-topology).

Proof:
1. By lem-trf-space-fibre-products-etale-covers the sheaf pullback is an algebraic space.
   For T → X', pullback pasting identifies (Y ×_X X') ×_{X'} T with Y ×_X T over T.
   The finite scheme representing the latter therefore represents the former.
2. By lem-a1-space-affine-etale-cover choose a point-surjective scheme atlas V → X.
   Its pullback W → Y is a point-surjective étale atlas, by the scheme-test definition
   and lem-trf-space-fibre-products-etale-covers. The map g : W → V is finite. The atlas
   theorem identifies both atlas quotient topologies with def-a1-space-point-topology:
   every étale scheme-source map is continuous, and the atlas itself is such a map.
3. For an open O in |X|, the inverse image in W of |f|⁻¹(O) equals the inverse image
   under g of its inverse image in V. This is open by scheme continuity. The quotient
   criterion for W → |Y| proves continuity of |f|.
4. For closed C in |Y|, g(q⁻¹(C)) is closed in V by
   lem-weil-pbc-finite-closed-map-finite-fibres. It equals p⁻¹(|f|(C)): for the reverse
   inclusion, represent compatible points v and y by field-valued representatives.
   The common-field relation of def-a1-algebraic-space-point-classes makes their maps
   to X agree after extension. Their pair gives a section of W and hence a scheme point
   over v mapping to y. Closedness detected by V → |X| now proves |f|(C) closed.
5. For x in |X| choose v in V above it. The same common-field argument gives a
   surjection g⁻¹({v}) → |f|⁻¹({x}). The source is finite by
   lem-weil-pbc-finite-closed-map-finite-fibres, so the target is finite as well.
6. For each étale scheme chart T → X, the hypothesis represents Y ×_X T by a scheme
   finite over T. Apply pqf-lem-finite-qf and pqf-lem-qf-locqf-qc, with the finite-type
   property of a finite scheme morphism, to obtain Scheme.Hom.IsLocallyQuasiFinite.
   This is precisely the predicate of pqf-def-quasifinite. -/
theorem finite_schemeTests_baseChange_topology
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (hf : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f.hom.hom) :
    (∀ (X' : AlgebraicSpace S) (g : X' ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsFinite p.left)
        (Limits.pullback.snd f.hom g.hom).hom) ∧
    Continuous (mapPoint f.hom.hom) ∧
    IsClosedMap (mapPoint f.hom.hom) ∧
    (∀ x : Point X.obj.obj, (mapPoint f.hom.hom ⁻¹' {x}).Finite) ∧
    (∀ (T : Over S) (a : yoneda.obj T ⟶ X.obj.obj), IsEtale a →
      ∃ (U : Over S) (p : U ⟶ T) (q : yoneda.obj U ⟶ Y.obj.obj),
        IsPullback q (yoneda.map p) f.hom.hom a ∧
          Scheme.Hom.IsLocallyQuasiFinite p.left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
