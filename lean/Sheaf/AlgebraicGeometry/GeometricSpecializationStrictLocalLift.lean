/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation
import Sheaf.RingTheory.StrictHenselizationTriplesPresentation
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.WeaklyEtaleField
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Lifting geometric specializations to strict local schemes

Source: Stacks Project, Tag 0GJ5, remark-can-lift
(blueprint: lem-weil-pbc-geometric-specialization-strict-local-lift).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A prescribed geometric generization lifts through the structural map of the strict
henselization at the specialized geometric point.
Source: Stacks Project, Tag 0GJ5, remark-can-lift
(blueprint: lem-weil-pbc-geometric-specialization-strict-local-lift).

Proof:
1. Choose an affine open U = Spec R containing s; specialization implies t lies in U.
Shrink affine pointed neighbourhoods into U, using
`lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`. Cofilteredness and
`lem-weil-pbc-colimit-initial-full-subcategory` identify their coordinate-ring colimit H
with the original one, compatibly with the structural map. H is ind-etale over R.
2. Apply `lem-sbc-geometric-strict-henselization-local-presentation` and
`lem-sc-strict-henselization-triples-presentation`. The maximal-ideal contraction from
`lem-weil-pbc-strict-henselization-triples` and the closed-point description in
`lem-weil-pbc-strict-henselization-functoriality` identify the localization prime with s.
Then `lem-sc-strict-henselization-faithfully-flat` gives faithful flatness over R_s.
3. The prime of t localizes to a prime of R_s with the same contraction in R.
By `lem-weil-pbc-faithfully-flat-surjective-spectrum` it lifts to P in H, giving a point
 t' of Spec H over t.
4. The fibre H tensor_R kappa(t) is ind-etale, hence weakly etale, by
`lem-weil-pbc-ind-etale-stability`. Its prime induced by P has residue field kappa(t').
`lem-weil-pbc-weak-etale-field` shows this is separable algebraic over kappa(t).
5. By `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`, embed kappa(t')
into Ωt extending the residue embedding of barT. The resulting local map H_P to Ωt
produces a by `lem-weil-pbc-morphism-from-spec-local-ring`. The same bijection for S
shows that its composite to S equals the prescribed barT, since their point and
residue-field embedding agree. -/
theorem exists_geometricPoint_strictHenselization_lift
    {S : Scheme.{u}} (t s : S) (hts : t ⤳ s)
    {Ωt Ωs : Type u} [Field Ωt] [IsAlgClosed Ωt] [Field Ωs] [IsAlgClosed Ωs]
    (barT : Spec (.of Ωt) ⟶ S) (barS : Spec (.of Ωs) ⟶ S)
    (hbarT : barT (IsLocalRing.closedPoint Ωt) = t)
    (hbarS : barS (IsLocalRing.closedPoint Ωs) = s) :
    ∃ a : Spec (.of Ωt) ⟶ strictHenselizationScheme barS,
      a ≫ strictHenselizationStructuralMap barS = barT := by
  sorry

end AlgebraicGeometry.Scheme
