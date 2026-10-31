/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.NormalEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IntegralEtaleQuasiCompact
import WeilConjectures.AlgebraicGeometry.StrictLocalSplitClopenFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Components of strictly locally split étale schemes over a normal base

Source: Weil conjectures blueprint, `sec-six-functors/sk-lem-finite`,
`thm-lisse-qlbar-representations`, proof (4); Stacks Project, Tag 033N
(blueprint: lem-sf-normal-strict-local-split-components).

The splitting hypothesis uses the canonical strict henselization and its structural map.
A colimiting cofan of sections says that its pullback is a coproduct of copies of the base,
with the isomorphism commuting with the projections to the base. No quasi-compactness of
`T` or finiteness of the splitting index is assumed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A separated étale scheme over a nonempty connected Noetherian normal scheme, split
at every strict localization, has clopen normal integral components finite étale and
surjective over the base.

Source: blueprint `thm-lisse-qlbar-representations`, proof (4); Stacks Project, Tag 033N
(blueprint: lem-sf-normal-strict-local-split-components).

Proof:
1. The source is locally Noetherian, and its stalks are normal domains by étale normality.
   Connected components are open in a locally Noetherian scheme and are always closed.
   Stalk equivalences along the open inclusion transport normality to each component.
   A connected locally Noetherian scheme with domain stalks is irreducible; domain
   stalks also give reducedness, hence the component and the base are integral.
2. Apply `integral_etale_quasiCompact` to the component map. Its generic fibre is a
   single finite separable field, and its normalization is finite by Tag 032L.
   The existing normalization-open theorem embeds the component in that Noetherian
   normalization, proving quasi-compactness without assuming it for the whole source.
3. Apply `isFinite_clopen_of_strictLocal_split`. On each strict localization the
   component is a quasi-compact clopen union of sheets of a split coproduct. A local
   spectrum has no nontrivial clopen subset, so finitely many whole sheets occur.
   The cofiltered finite-limit theorem descends finiteness to pointed affine étale
   neighbourhoods, and fpqc descent gives finiteness over the base.
4. The component map is étale and finite, so its image is open and closed. It is
   nonempty, hence all of the connected base. This gives surjectivity. Empty source
   is included because the conclusion is quantified over its points.
-/
theorem normal_strictLocal_split_components
    {X T : Scheme.{u}} [Nonempty X] [PreconnectedSpace X] [IsNoetherian X]
    (hX : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (q : T ⟶ X) [IsSeparated q] [Etale q]
    (hsplit : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ (I : Type u)
        (ι : I → (Scheme.strictHenselizationScheme s ⟶
          pullback q (Scheme.strictHenselizationStructuralMap s))),
        (∀ i : I, ι i ≫ pullback.snd q (Scheme.strictHenselizationStructuralMap s) =
          𝟙 (Scheme.strictHenselizationScheme s)) ∧
        Nonempty (IsColimit (Cofan.mk
          (pullback q (Scheme.strictHenselizationStructuralMap s)) ι))) :
    ∀ t : T, ∃ U : T.Opens,
      (U : Set T) = connectedComponent t ∧ IsClosed (U : Set T) ∧
      IsIntegral U.toScheme ∧
      (∀ z : U.toScheme, IsDomain (U.toScheme.presheaf.stalk z) ∧
        IsIntegrallyClosed (U.toScheme.presheaf.stalk z)) ∧
      IsFinite (U.ι ≫ q) ∧ Etale (U.ι ≫ q) ∧ Surjective (U.ι ≫ q) := by
  have : ConnectedSpace X := ⟨inferInstance⟩
  let : IrreducibleSpace X :=
    irreducibleSpace_of_isDomain_stalk X fun x ↦ (hX x).1
  let (x : X) : IsDomain (X.presheaf.stalk x) := (hX x).1
  let : IsReduced X := isReduced_of_isReduced_stalk _
  let : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  have hnormalT := Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain q hX
  intro t
  let U : T.Opens := ⟨connectedComponent t, isOpen_connectedComponent⟩
  have hnormalU (z : U.toScheme) : IsDomain (U.toScheme.presheaf.stalk z) ∧
      IsIntegrallyClosed (U.toScheme.presheaf.stalk z) := by
    obtain ⟨hd, hi⟩ := hnormalT (U.ι z)
    let : IsDomain (T.presheaf.stalk (U.ι z)) := hd
    let : IsIntegrallyClosed (T.presheaf.stalk (U.ι z)) := hi
    let e := (asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  let : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : IrreducibleSpace U.toScheme :=
    irreducibleSpace_of_isDomain_stalk U.toScheme fun z ↦ (hnormalU z).1
  let (z : U.toScheme) : IsDomain (U.toScheme.presheaf.stalk z) := (hnormalU z).1
  let : IsReduced U.toScheme := isReduced_of_isReduced_stalk _
  let : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let f := U.ι ≫ q
  have : QuasiCompact f := integral_etale_quasiCompact hX f
  have : IsFinite f := isFinite_clopen_of_strictLocal_split q hsplit U
    isClosed_connectedComponent
  have hrange : Set.range f = Set.univ :=
    IsClopen.eq_univ ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
      (Set.range_nonempty f)
  have hsurj : Surjective f := ⟨Set.range_eq_univ.mp hrange⟩
  exact ⟨U, rfl, isClosed_connectedComponent, inferInstance, hnormalU,
    inferInstance, inferInstance, hsurj⟩

end AlgebraicGeometry
