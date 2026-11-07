/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of properties of morphisms along fpqc coverings

We record the descent of properties of morphisms of schemes along fpqc coverings
(Stacks, Section 02KM), following the blueprint of the proper base change theorem.

## Main results

- `AlgebraicGeometry.fpqc_local_on_base_criterion`: a property of morphisms which is invariant
  under isomorphisms, stable under flat base change, Zariski local on the base and which descends
  along faithfully flat morphisms of affine schemes descends along fpqc coverings (Stacks 02KP).
- `AlgebraicGeometry.Scheme.fpqcCover_of_smallEtaleCover`: a covering family of the small étale
  site is an fpqc covering.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

section Criterion

variable {P : MorphismProperty Scheme.{u}}


end Criterion

/-- **The fpqc topology is finer than the small étale topology**: a covering family
`{f i : V i ⟶ U}` of the small étale site of `T` is an fpqc covering of `U`; in particular every
`f i` is flat.

(blueprint: `lem-weil-pbc-fpqc-finer-than-etale`) -/
theorem Scheme.fpqcCover_of_smallEtaleCover {T : Scheme.{u}} {U : T.Etale} {ι : Type v}
    {V : ι → T.Etale} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ T.smallEtaleTopology U) :
    Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈ fpqcPrecoverage U.left := by
  refine fppfPrecoverage_le_fpqcPrecoverage _ ?_
  rw [fppfPrecoverage, ofArrows_mem_precoverage_iff]
  refine ⟨fun x ↦ ?_, fun i ↦ ⟨inferInstance, inferInstance⟩⟩
  have hx : x ∈ ⋃ i, Set.range (f i).left := by
    rw [(ofArrows_mem_smallEtaleTopology_iff f).mp hf]
    trivial
  exact Set.mem_iUnion.mp hx

end AlgebraicGeometry
