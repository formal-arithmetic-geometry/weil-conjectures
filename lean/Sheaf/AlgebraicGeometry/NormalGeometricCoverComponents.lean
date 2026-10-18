/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Connected.Clopen
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.GeometricCoverComponentQcProper
import Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen

/-!
# Connected components of geometric coverings over a normal base

Source: Bhatt--Scholze, The pro-étale topology for schemes, Definition 7.3.1(3), p. 66,
and proof of Lemma 7.4.10, p. 71; Stacks Project, Tag 0BQ3
(blueprint: lem-a1-normal-geometric-cover-components).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A geometric covering of a nonempty connected, quasi-compact, locally Noetherian scheme
with integrally closed local domains is the coproduct of its clopen connected components,
each finite étale and surjective over the base. The component index may be empty or infinite.
Source: Bhatt--Scholze, Definition 7.3.1(3), p. 66, and proof of Lemma 7.4.10, p. 71;
Stacks Project, Tag 0BQ3 (blueprint: lem-a1-normal-geometric-cover-components).

Proof: If `Z` is empty, the component family is empty. Otherwise
`lem-a1-normal-etale-components-clopen` applies: normality implies geometric unibranchness
(Tag 0BQ3), and étaleness makes `Z` locally topologically Noetherian. Its connected
components are therefore irreducible and clopen. Give each its induced open subscheme
structure. By `lem-a1-geometric-cover-component-qc-proper`, the valuation lifting property
makes each restricted map quasi-compact and proper with finite fibres; this is the generic
fibre and Noetherian induction argument of Lemma 7.4.10. Apply
`thm-pqf-finite-iff-proper-finite-fibres` to obtain finiteness. Restriction to an open
subscheme preserves étaleness. The image is open by
`lem-weil-pbc-etale-morphism-open-map` and closed by
`lem-weil-pbc-finite-closed-map-finite-fibres`. It is nonempty because a connected component
is nonempty, so connectedness of `X` makes this image all of `X`. Finally the pairwise
disjoint components cover `Z`, and their open subschemes have the coproduct universal
property. No quasi-compactness of `Z` or finiteness of its component index is used. -/
theorem normalGeometricCoverComponents
    {X Z : Scheme.{u}} [ConnectedSpace X] [IsLocallyNoetherian X] [CompactSpace X]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (q : Z ⟶ X) [Etale q] (hval : ValuativeCriterion q) :
    ∃ C : ConnectedComponents Z → Z.Opens,
      (∀ c : ConnectedComponents Z,
        (C c : Set Z) = ConnectedComponents.mk ⁻¹' {c} ∧
        IsClosed (C c : Set Z) ∧ ConnectedSpace (C c).toScheme ∧
        IsFinite ((C c).ι ≫ q) ∧ Etale ((C c).ι ≫ q) ∧ Surjective ((C c).ι ≫ q)) ∧
      Nonempty (IsColimit (Cofan.mk Z (fun c : ConnectedComponents Z ↦ (C c).ι))) := by
  sorry

end AlgebraicGeometry
