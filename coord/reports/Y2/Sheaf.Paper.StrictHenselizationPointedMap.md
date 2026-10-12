## What changed

Repair of reviewer X-3bcd8, E2/E3. Deleted the false declaration
`AlgebraicGeometry.strictHenselizationPointedMap_factorization` and its entire
docstring from `Sheaf.Paper.StrictHenselizationPointedMap`. Replaced the invalid
three-line assembly proof of `AlgebraicGeometry.strictHenselizationPointedMap`
with `by sorry`, keeping its signature unchanged. Its declaration now has a
source, blueprint id and complete compatible-residue-cocone proof in words.
Retained the completed proof of `AlgebraicGeometry.strictHenselizationPointedMap_core`.
No definitions, retained signatures, visibility or imports changed; Challenge is untouched.

The existential node records the direct compatible-cocone route, without the
universal-factorization dependency. The deleted lemma's node has no Lean
realization and records the counterexample and deletion. The core node records
the proved affine-chart comparison and abstract separable-closure transport.
Change record: `coord/changes/strictHenselizationPointedMap_factorization.md`.

## Proved and sorry left

Proved one of the two original sorries:
`AlgebraicGeometry.strictHenselizationPointedMap_core`
(node `lem-weil-pbc-strict-henselization-pointed-map-core`). Its proof contains
no sorry, but uses existing declarations that may depend on existing holes.

Deleted, rather than proved, the false holed declaration
`AlgebraicGeometry.strictHenselizationPointedMap_factorization`
(node `lem-weil-pbc-strict-henselization-pointed-map-factorization`). Reopened
`AlgebraicGeometry.strictHenselizationPointedMap`
(node `lem-weil-pbc-strict-henselization-pointed-map`), the sole remaining sorry.
This existing existential theorem must construct a specific compatible map;
the abstract core does not prove its pointedness. No new statements or split-off
holes were added. Relative to the original module, two holes are removed
(one proved and one false declaration deleted) and one existing proof is reopened.
The deletion is not counted as a proof.

## No longer needed

The universal-factorization declaration and node
`lem-weil-pbc-strict-henselization-pointed-map-factorization` are no longer used.
No modules or imports are pruned: both proof imports,
`Sheaf.AlgebraicGeometry.EtaleLocalRingTriples` and
`Sheaf.RingTheory.StrictHenselizationTriples`, are needed by the proved core.
The core theorem (node `lem-weil-pbc-strict-henselization-pointed-map-core`)
is retained but removed from the existential node's old `proof_deps`. The deleted
factorization node also drops its old dependencies
`lem-weil-pbc-etale-local-ring-triples` and
`lem-weil-pbc-strict-henselization-triples`; these remain used by the core and
the existential plan, so neither module is pruned. The unit sk-thm-p1 route is preserved.

## Where the brief, the DAG or earlier work was wrong

The returned delivery disputed a false universal lemma but still used it in the
existential assembly. This repair removes that unsound route exactly as requested.
For Y = Spec(C), Ω = C and the identity geometric point, the strict henselization
and relative separable closure identify with C. Complex conjugation is a
surjection with zero kernel, but the identity neighbourhood requires its induced
scheme morphism to be the identity. It fails on structure sheaves. Thus even
surjectivity and kernel equality cannot repair the universal statement.

[Stacks Tag 04HX](https://stacks.math.columbia.edu/tag/04HX) and
[Tag 04GW](https://stacks.math.columbia.edu/tag/04GW) provide the affine-neighbourhood
and triple-colimit construction for the particular compatible residue map.
The existential docstring and node now retain this choice throughout the argument,
including an embedding-compatible identification of relative separable closures.
The core uses only an abstract closure equivalence and therefore cannot replace it.
The declaration-use search lists only this module as a user of the deleted lemma;
no downstream adaptations are needed. The existing existential theorem and every
Challenge signature remain unchanged. No new nodes are introduced.

## Second reading by Y2

1. Compared the sole delivered Lean module with the read-only repository using
   `diff` and the declaration parser. Both retained signatures are byte for byte
   unchanged; no definition, visibility, or import changed. The only removed
   signature is the false universal factorization, declared in
   `coord/changes/strictHenselizationPointedMap_factorization.md`. Direct search
   of both Lean roots confirms that its only user was the reopened existential
   proof in this module. Verdict: pass, with the recorded deletion.
2. Compiled the delivered module with `lcompile.py` (exit 0, 4.7 seconds), and
   compiled a fresh scratch copy with `#print axioms` for both retained theorems.
   Both report only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The core has no local hole; its imported dependencies still have holes. The
   sole local hole is the named existing existential theorem with its source,
   blueprint node and compatible-cocone proof docstring. There are no forbidden
   declarations or hollow definitions. Existential witnesses are eliminated
   inside a proposition proof, not used to define arbitrary public data.
   Verdict: pass, relative to existing imported holes.
3. No new or split-off statement is introduced. Independently checked the
   deleted universal claim on the algebraically closed field C with identity
   geometric point: conjugation fails the identity-neighbourhood equation,
   despite being surjective with zero kernel. The retained core only asserts
   existence and allows an abstract closure equivalence; this is true in that
   case and does not imply pointedness. Read the full signatures of both triple
   input theorems and checked each field extracted by the core proof.
   Verdict: the false statement is correctly deleted, not counted as proved.
4. Searched with `msearch.py ... grep` for `IsSepClosure.equiv`,
   `ker_eq_maximalIdeal`, and `strictHenselizationRing`, and directly searched
   both Lean roots for residue/surjection and pointed-map combinations. The
   proof uses the existing Mathlib closure-equivalence and maximal-kernel
   lemmas rather than restating them. No shorter ready-made geometric transport
   was found. The two private proof imports supply the two triple theorems;
   public imports supply objects in the signatures. Reviewed `sk-thm-p1.json`
   `realized`: no unit statement or step is bypassed or changed. Completed the
   dependency-removal inventory above; no module is pruned. Verdict: pass.
5. Compared all three delivered node JSON files with the repository. Only
   `proof`, `proof_deps`, `proof_origin`, and the deleted lemma's `lean: null`
   differ. The core's steps match the affine comparison, colimit isomorphism,
   scalar transport, abstract closure equivalence, and kernel argument in Lean.
   The existential node records an unfinished compatible-map plan and uses
   neither the core nor the false universal factorization. Read Stacks
   [04HX](https://stacks.math.columbia.edu/tag/04HX),
   [04GW](https://stacks.math.columbia.edu/tag/04GW), and
   [04GP](https://stacks.math.columbia.edu/tag/04GP) online because the cited
   local source is absent. These support the affine/triple construction and
   the plan for the remaining hole. Verdict: pass; no new nodes need auditing.

Second reading changed only this report: made the removed-dependency inventory
explicit and recorded the independent signature, source, proof, axiom and node
checks. No Lean repair was needed. One of the two original holed declarations
is proved, one false holed declaration is deleted, and the existing existential
proof is reopened; zero new split-off statements. This repair does not claim a
net proof-hole reduction beyond the separately reported false-lemma deletion.
