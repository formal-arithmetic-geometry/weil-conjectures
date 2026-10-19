## Worker report

The module `Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBound` states
`AlgebraicGeometry.exists_stage_fibre_dimension_le`, with its sole proof `sorry`.
It introduces no definitions, new nodes, dependency modules, or statement corrections.
Source checked: `literature/stacks-project/limits.tex`, label `lemma-limit-dimension`,
Tag 05M5, beginning at line 4505. The node is precisely its affine specialization.
The declaration docstring includes the node's complete seven-step proof, including
its fixed-ambient-fibre stabilization argument rather than the problematic last
diagram in the printed Stacks proof.

Hypotheses and conclusion, clause by clause:

- Small nonempty directed partially ordered index set: `{I : Type u}`, `[PartialOrder I]`,
  `[Nonempty I]`, `[IsDirected I (· ≤ ·)]`. The category is the canonical thin category
  of this partial order. Index and rings share `u`, as the stage brief requires.
- Directed systems of commutative rings: `A C : I ⥤ CommRingCat.{u}`. Their functor
  laws give exactly the transition identities and composition laws.
- Compatible homomorphisms `A_i → C_i`: `φ : A ⟶ C`. Naturality is the compatibility.
- Each is finite type: `hfinite : ∀ i : I, (φ.app i).hom.FiniteType`.
  `RingHom.FiniteType` unfolds to `Algebra.FiniteType` for the algebra induced by
  that ring map; it introduces no different finite-type notion.
- Surjectivity for every `i ≤ j`: `hsurj` quantifies over both indices and `hij`.
  `pushout.desc (φ.app j) (C.map (homOfLE hij)) (φ.naturality (homOfLE hij))`
  is the map from the pushout of `A_i → A_j` and `A_i → C_i` to `C_j`.
  The two maps out of the pushout are exactly `A_j → C_j` and `C_i → C_j`.
  Its `.hom` is required to be `Function.Surjective`. The tensor-product
  universal property, implemented by `CommRingCat.pushoutCoconeIsColimit`,
  identifies this pushout with `A_j ⊗[A_i] C_i` and this map with the node's
  canonical comparison. Surjectivity is invariant under this ring isomorphism.
  In particular the condition is actual surjectivity, not categorical epimorphism.
- The colimits `A` and `C`: Mathlib's chosen `colimit A` and `colimit C`, with
  their induced map `colimMap φ`. Existence comes from the standard small
  colimits of commutative rings; no independent colimit data or hypothesis is added.
- Nonnegative integer `d`: `(d : ℕ)`, cast to `WithBot ℕ∞` in the inequalities.
  This parameterizes exactly the integers that are at least zero.
- Every prime of the limiting base: `∀ (p : Ideal ↥(colimit A)) [p.IsPrime]`.
  Its residue field is the recorded `p.ResidueField`, with canonical algebra map.
- Limiting fibre bound: `hbound` applies `topologicalKrullDim` to the underlying
  space of `pullback (Spec.map (colimMap φ)) (Spec.map (CommRingCat.ofHom
  (algebraMap ↥(colimit A) p.ResidueField)))`, requiring `≤ (d : WithBot ℕ∞)`.
  The recorded `pullbackSpecIso` canonically identifies this affine scheme with
  `Spec (C ⊗[A] κ(p))`. Thus this is precisely the node's spectrum, expressed
  by its equivalent fibre-product construction without a duplicate fibre definition.
- Conclusion: `∃ i : I, ∀ (p : Ideal (A.obj i)) [p.IsPrime], ... ≤ (d : WithBot ℕ∞)`
  is one stage, uniformly for every prime of that stage's base. The same affine
  pullback construction now uses `φ.app i` and `algebraMap (A.obj i) p.ResidueField`,
  hence is exactly `Spec (C_i ⊗[A_i] κ(p))` under `pullbackSpecIso`.
- Empty spectra: `topologicalKrullDim` is valued in `WithBot ℕ∞`; an empty
  underlying space has dimension `⊥`, so the inequalities include empty fibres.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, via its recorded bare-map
  form `RingHom.FiniteType` (lines 215–218).
- `Mathlib.AlgebraicGeometry.Pullbacks`: `AlgebraicGeometry.pullbackSpecIso`,
  together with `pullbackSpecIso_inv_fst` and `pullbackSpecIso_inv_snd` identifying
  the affine pullback with the tensor-product spectrum and its projections.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  its cocone/universal-property interface and `colimMap` for the induced ring map.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`. The ordinary
  residue field is used; the tensor-product fibre's spectrum is expressed by the
  recorded affine pullback isomorphism, without redefining `Ideal.Fiber`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`, `includeRight`,
  `productMap`, `productMap_apply_tmul`, `ext`. These give the recorded tensor
  universal property used by `CommRingCat.pushoutCoconeIsColimit`
  (`Mathlib.Algebra.Category.Ring.Constructions`) to identify the comparison source.

The stated proof dependencies are imported without `public`: the local dimension
module, field-extension invariance, supremum of local dimensions, bounded-open-upstairs,
reduced induced closed subschemes, affine-transition nonempty limits, and the
Spec–global-sections adjunction. The commutative-ring filtered colimit module
supplies the elementwise colimit results. The remaining Mathlib proof dependencies
(Noetherianity of finite type algebras, maximal ideals in ideal families, compactness
of spectra and quotient spectrum embeddings) are available through these imports.
No proof-dependency import closes a cycle.

Edge cases checked mathematically: `d = 0` is included; fibres of zero rings and
empty fibres have dimension bottom; a zero limiting base has no primes, so its
hypothesis is vacuous exactly as in the source; no nontrivial-ring assumption is
introduced. The nonempty index requirement prevents the existential stage from
being impossible. Singleton diagrams reduce to the assumed fibre bound. No
Noetherian hypothesis on the original base or stage rings is imposed: the proof
only uses Noetherianity of a finite type algebra over the fixed residue field.
No choice of independent test-object universe excludes a case.

Searches made on 2026-10-15:

- `grep`: (fiber|fibre).*dimension.*(limit|colimit)|(limit|colimit).*dimension. 5 hits: Mathlib/Probability/Process/FiniteDimensionalLaws.lean, Mathlib/Probability/CentralLimitTheorem.lean, Mathlib/Algebra/Category/FGModuleCat/Limits.lean, Mathlib/CategoryTheory/Abelian/Injective/Dimension.lean, Mathlib/CategoryTheory/Abelian/Projective/Dimension.lean. No exact statement; the hits concern other dimension or colimit results.
- `loogle`: "topologicalKrullDim", "colimit". 0 hits: none. No exact statement; the hits concern other dimension or colimit results.
- `leanfinder`: Bounds on dimensions of all fibres of finite type algebras descend along directed colimits with surjective base change comparison maps. 8 hits: Algebra.IsStandardSmoothOfRelativeDimension.out, RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit, PrimeSpectrum.finite_of_toPiLocalization_pi_surjective, Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, PrimeSpectrum.finite_of_toPiLocalization_surjective, Algebra.lift_rank_le_of_surjective_injective, Algebra.Smooth.exists_finiteType, Algebra.rank_le_of_surjective_injective. No exact statement; the hits concern other dimension or colimit results.
- `leansearch`: For a directed system of finite type ring maps with surjective base change comparisons, a bound on all fibre dimensions of its colimit holds at a stage. service unavailable: Internal Server Error; no conclusion drawn from the unavailable service.

Direct `rg` searches of `WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` for the item id, affine-limit dimension patterns,
and `exists_stage_fibre_dimension_le` found no existing statement or name collision.
The broader fibre/limit search found neighbouring field-extension, fibre-bound,
and colimit material, whose signatures do not assert this descent statement.
`grep -rn` for the exact item id in `WeilConjectures` returned no result.

Validation: the sole delivered module compiled cleanly using `scompile.py` on
2026-10-15, in 1.5 seconds, nice 19, two threads, with the 60-second per-file limit.
There were no errors or warnings. No local compiler or library build was run.
No statement fault or disputed mathematical clause was found.


## Second reading by NR

I independently read the node, its seven proof steps, every statement-dependency
node and the recorded Mathlib declarations, the complete delivered Lean module,
and `limits.tex`, section "Limits and dimensions of fibres", Tag 05M5,
`lemma-limit-dimension` (lines 4505 onward). No mismatch was found; the Lean
module and node record are retained unchanged. This delivery contains no new
nodes or dependency modules, and no stage-2 statement correction.

The source has affine base transitions, quasi-compact quasi-separated bases,
finite type morphisms and closed immersion base-change comparison maps. In the
node's affine specialization the first two conditions hold automatically, and
the last condition is precisely surjectivity of the comparison ring map. There
is no ambient field, characteristic or Noetherian hypothesis in this source.

Object, hypothesis and conclusion inventory, with independent verdicts:

1. Small nonempty directed partial order I: `{I : Type u} [PartialOrder I]
   [Nonempty I] [IsDirected I (· ≤ ·)]`. Exact; the preorder category supplies
   the unique arrows, and functors encode the directed systems. The common
   index/ring universe follows the project's small-colimit convention.
2. Two systems of commutative rings: `(A C : I ⥤ CommRingCat.{u})`.
   Exact, including zero rings. No domain, field or nontriviality assumption.
3. Compatible ring homomorphisms: `(φ : A ⟶ C)`. Exact: naturality says
   `A.map hij ≫ φ.app j = φ.app i ≫ C.map hij`.
4. Each ring homomorphism is finite type: `hfinite : ∀ i : I,
   (φ.app i).hom.FiniteType`. Exact: `RingHom.FiniteType` is definitionally
   `Algebra.FiniteType` for the algebra induced by this very ring map, as
   required by def-weil-pbc-finite-type-algebra.
5. For every i ≤ j the canonical comparison is surjective: `hsurj` quantifies
   over `i j hij` and applies `Function.Surjective` to the underlying ring map
   of `pushout.desc (φ.app j) (C.map (homOfLE hij)) (φ.naturality ...)`.
   Exact: the pushout span is `A_i → A_j`, `A_i → C_i`, and the two maps to
   `C_j` are the given structure and transition maps. I opened
   `CommRingCat.pushoutCocone`, its projections and `pushoutCoconeIsColimit`:
   their point is `A_j ⊗[A_i] C_i` and the desc map is the tensor product
   universal map. This is ordinary surjectivity, not the weaker ring-epimorphism
   condition. Its meaning is independent of the chosen pushout isomorphism.
6. A and C are the ring colimits, with their induced map: `colimit A`,
   `colimit C`, `colimMap φ`. Exact; standard small colimit existence is
   synthesized, not an additional mathematical restriction.
7. Nonnegative integer d: `(d : ℕ)`. Exact, with casts to `WithBot ℕ∞`.
8. Every prime of the limiting base and its residue field:
   `∀ (p : Ideal ↥(colimit A)) [p.IsPrime]`, `p.ResidueField` and the
   canonical `algebraMap`. Exact: `Ideal.ResidueField` abbreviates the residue
   field of `Localization.AtPrime p`, not an arbitrary extension field.
9. Dimension of each limiting fibre at most d: `hbound` measures
   `topologicalKrullDim` of the scheme pullback of `Spec.map (colimMap φ)`
   and `Spec.map` of the residue field structure map. Exact: I read
   `pullbackSpecIso` and its two projection formulas, which identify this
   scheme with `Spec (C ⊗[A] κ(p))` using the algebra of the induced ring map.
   Isomorphisms give homeomorphisms, preserving this dimension. This uses
   the recorded affine-fibre-product notion, with no substitute definition.
10. One stage uniformly bounding every fibre: `∃ i : I, ∀ (p : Ideal
    (A.obj i)) [p.IsPrime], ... ≤ (d : WithBot ℕ∞)`. Exact quantifier order.
    The analogous pullback uses `φ.app i` and that stage's own residue field,
    and the same `pullbackSpecIso` identifies its tensor-product spectrum.
11. Empty spectra allowed: `topologicalKrullDim` takes values in `WithBot ℕ∞`
    and is the dimension of `IrreducibleCloseds`; the empty space has value
    bottom. Exact, with no nonemptiness condition on a fibre.

Additional dependency checks: I opened tensor `includeLeft`, `includeRight`,
`productMap`, `productMap_apply_tmul` and `ext`; they give precisely the
recorded commutative-algebra tensor universal property. `Spec` and `Spec.map`
are the actual affine schemes and contravariant morphisms. `Ideal.Fiber` places
κ(p) on the left, but the chosen scheme pullback directly uses the recorded
`C ⊗ κ(p)` affine-spectrum identification; it introduces no competing notion.
I also read the imported field-extension local-dimension, bounded-open-upstairs
and supremum-of-local-dimensions signatures to check the proof plan applies to
finite type fibre algebras, without requiring the original bases Noetherian.

Edge cases: I is necessarily nonempty in both the node and Lean, so the empty
index set is correctly excluded. A singleton index reduces to the hypothesis.
Zero base or stage rings, zero fibre rings, empty schemes and empty fibres are
all permitted. If the limiting base is zero, its prime hypothesis is vacuous,
exactly as in the node. The conclusion is still an eventual-stage assertion,
not silently made vacuous. d = 0 is included. There is no characteristic
restriction, no field assumption on the systems, and no finiteness assumption
on I. Universe u is explicitly bound and shared by the rings and the small
index category; residue fields and pullbacks remain in the same universe.
Every variable is explicitly bound; there is no extra test-object universe.

Independent searches, using different wording from the worker:

- LeanFinder via msearch: "In an inverse limit of affine schemes whose
  transition comparisons are closed immersions, bounded dimensions of geometric
  fibres hold eventually". Eight hits concerned affine/quasi-affine descent,
  nonempty closed subsets in limits, eventual equality of morphisms, and
  eventual vanishing of sections. None asserts fibre-dimension descent.
- Loogle via msearch: `"topologicalKrullDim", "FiniteType"`: zero hits.
- grep via msearch: `(dimension|krullDim).*(IsColimit|DirectLimit)|
  (IsColimit|DirectLimit).*(dimension|krullDim)`: two simplicial-set dimension
  hits; neither concerns schemes or Krull dimension.
- Direct rg on upstream WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json used dimension/Krull-dimension with colimit,
  inverse-limit and direct-limit patterns, plus the exact declaration and node
  identifiers. No duplicate declaration. I opened the nearby project result
  `CommRingCat.filteredColimit_prime_chain_and_dimension`: it bounds the
  colimit ring dimension by a supremum and contracts finite prime chains; it
  does not give a single stage bounding all fibres. Other hits concern
  zero-dimensional etale colimits and strict henselization, not this theorem.

H5/H6/H8/H9: no definitions, hence no hollow data; the sole theorem has proof
`sorry`, with no proof supplied. The module and theorem cite 05M5 and the
blueprint identifier. I compared all seven docstring proof steps to the node:
open bad loci, functoriality via surjective comparison, reduced quotients and
nonempty limit, fixed residue-field base change, Noetherian kernel stabilization,
local-dimension contradiction, and the supremum conclusion are all present.
No private or local substitute, local notation or hidden let binder occurs.
All lines are at most 100 characters. The node's `lean.statement` was checked
verbatim against the file's signature and matches exactly. No statement-change
record exists, so correction/citer review is inapplicable.

Second-reader validation: the sole delivered file compiled cleanly with
`scompile.py NR lem-weil-pbc-affine-limit-fibre-dimension-bound` on 2026-10-15:
1.6 seconds, nice 19, two threads, 60-second per-file limit, no warnings or
errors. No local compiler or global build was run. The second reading changed
only this report; no mathematical or Lean repair was needed.
