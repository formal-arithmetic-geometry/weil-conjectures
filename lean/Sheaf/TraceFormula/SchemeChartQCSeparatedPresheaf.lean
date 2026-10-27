/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.TraceFormula.SpaceQCSeparatedPointCover
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# From scheme chart properties to the algebraic-space presheaf predicates

Source: Stacks, Morphisms of Spaces, Tags 03KG and 03KM
(blueprint: lem-trf-scheme-chart-qc-separated-presheaf).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Recognize quasi-compactness and separatedness on represented scheme charts of
a map to a scheme, using the point-cover convention of the project.
Source: Stacks, Morphisms of Spaces, Tags 03KG and 03KM; Schemes, Tag 01K5;
Morphisms, Tag 01QR
(blueprint: lem-trf-scheme-chart-qc-separated-presheaf).

Proof: for each affine scheme test of a local map, its scheme fibre product is
quasi-compact by stability of quasi-compact scheme maps under base change. Its
identity is a surjective etale atlas, so it satisfies IsQuasiCompactPresheafMap.
The diagonal of the local scheme map is a closed immersion, and every scheme test
of it is a closed immersion by base-change stability, giving IsSeparatedPresheafMap.
Use each specified cartesian square to identify these local maps with the base changes
of g. Quasi-compactness and separation are invariant under these pullback isomorphisms.
Finally apply etale locality along the jointly surjective family t_i. One may view T
as an algebraic space represented by its Yoneda sheaf; this does not change g or either
presheaf predicate. Empty T and empty covering families satisfy the same test argument. -/
theorem qcSeparatedPresheafMap_of_schemeCharts
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (g : X.obj.obj ⟶ yoneda.obj T) (I : Type v)
    (Tᵢ : I → Over S) (t : ∀ i : I, Tᵢ i ⟶ T)
    (he : ∀ i : I, Etale (t i).left)
    (hs : IsJointlySurjective (fun i : I ↦ yoneda.map (t i)))
    (V : I → X.EtaleSite) (p : ∀ i : I, (V i).obj.left ⟶ Tᵢ i)
    (hp : ∀ i : I, IsPullback (V i).obj.hom (yoneda.map (p i))
      g (yoneda.map (t i)))
    (hq : ∀ i : I, QuasiCompact (p i).left)
    (hsep : ∀ i : I, IsSeparated (p i).left) :
    IsQuasiCompactPresheafMap g ∧ IsSeparatedPresheafMap g := by sorry

end AlgebraicGeometry.AlgebraicSpace
