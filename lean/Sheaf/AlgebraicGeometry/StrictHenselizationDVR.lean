/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
import Sheaf.AlgebraicGeometry.StrictHenselization
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# DVR property of strict henselizations

Source: Stacks Project, More on Algebra, Tags 0AP3 and 07QM; Étale Cohomology, Tag 04HX
(blueprint: lem-sc-strict-henselization-dvr).
-/

universe v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The canonical map from a Noetherian scheme local ring to its strict henselization
is flat, local and injective, and preserves and reflects the DVR property.
The first conjunct specifies the map on every germ using the affine pointed
neighbourhood coprojections: whenever a representative factors through an affine
open `U`, pulling sections to that representative and taking its colimit coprojection
agrees with taking their germ and applying `ι`.
Source: Stacks Project, Tags 0AP3, 07QM and 04HX
(blueprint: lem-sc-strict-henselization-dvr).

Proof:
1. Choose an affine open `U = Spec A` containing the image point, with prime `p`.
   The local ring is `A_p`. By `lem-weil-pbc-etale-local-ring-triples`, the pointed
   affine-neighbourhood colimit is the colimit over étale triples `(B,q,phi)`.
   By `lem-weil-pbc-strict-henselization-triples`, this is the ring strict
   henselization, with its structural map and maximal ideal. This is Tag 04HX,
   and respects the neighbourhood maps, giving the first conjunct.
2. The triple diagram is filtered and consists of étale `A`-algebras, hence flat
   `A`-modules by `lem-weil-pbc-etale-algebra-flat`. Its ring colimit is flat over
   `A` by `lem-weil-pbc-filtered-colimit-flat-modules`. Its maximal ideal pulls
   back to `p`, so `A -> C` factors through a local map `A_p -> C`. Since
   `C tensor_{A_p} M = C tensor_A M`, this map is flat. A flat local map is
   faithfully flat (`lem-pc-local-flat-faithful-flat-reflects-surjective`), and
   contraction of the zero ideal (`lem-weil-pbc-faithfully-flat-ideal-contraction`)
   makes it injective. This is the argument of Tag 07QM.
3. If `A_p` is a DVR, it has dimension one (`lem-sc-dvr-dimension-one`) and is
   regular local. Strict henselization preserves Noetherianity, dimension and
   regularity (`lem-sc-strict-henselization-noetherian`,
   `lem-sc-strict-henselization-dimension`, `lem-sc-strict-henselization-regular`).
   Hence its strict henselization is a DVR by `lem-sc-regular-dim1-dvr`.
4. Conversely, if the strict henselization is a DVR, it is regular local of
   dimension one. The dimension and regularity lemmas reflect these properties
   to `A_p`. The assumed Noetherianity and `lem-sc-regular-dim1-dvr` make `A_p`
   a DVR. These two implications give Tag 0AP3. -/
theorem strictHenselization_dvr
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω))
    [IsNoetherianRing (Y.presheaf.stalk (s.base x)).1] :
    ∃ ι : Y.presheaf.stalk (s.base x) ⟶ strictHenselizationRing s,
      (∀ (U : Y.Opens) (_ : IsAffineOpen U) (hx : s.base x ∈ U)
        (n : SmallModel.{v} (strictHenselizationNeighbourhoods s))
        (h : ⊤ ≤ ((AffineEtale.Spec Y).obj
          (((equivSmallModel.{v} (strictHenselizationNeighbourhoods s)).inverse.obj n).1)).hom
            ⁻¹ᵁ U),
        Y.presheaf.germ U (s.base x) hx ≫ ι =
          Scheme.Hom.appLE
            (((AffineEtale.Spec Y).obj
              (((equivSmallModel.{v} (strictHenselizationNeighbourhoods s)).inverse.obj n).1)).hom)
              U ⊤ h ≫ colimit.ι (strictHenselizationDiagram s) (op n)) ∧
      RingHom.Flat ι.hom ∧ IsLocalHom ι.hom ∧ Function.Injective ι.hom ∧
      ((∃ _ : IsDomain (Y.presheaf.stalk (s.base x)).1,
          IsDiscreteValuationRing (Y.presheaf.stalk (s.base x)).1) ↔
        (∃ _ : IsDomain (strictHenselizationRing s).1,
          IsDiscreteValuationRing (strictHenselizationRing s).1)) := by
  sorry

end AlgebraicGeometry.Scheme
