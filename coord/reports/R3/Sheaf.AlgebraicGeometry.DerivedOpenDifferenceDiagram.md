## What changed

Replaced the sorry in `AlgebraicGeometry.derived_open_difference_diagram` by an
explicit construction and a checked reduction to the single-summand theorem
`AlgebraicGeometry.derived_open_intersection_mate_isIso` in the new module
`Sheaf.AlgebraicGeometry.DerivedOpenIntersectionMateIso`.
The existing theorem's signature, visibility, definitions, and public import are unchanged.
All additional imports are proof imports. Three private, fully proved matrix lemmas
supply the invertibility calculation. The open adjunctions and their counit
isomorphisms are constructed from existing proved APIs. The overlap equation is
proved by the inverse law of `homEquiv`; both summand calculations are proved
by naturality and biproduct identities.

Read Stacks Tags [08DG](https://stacks.math.columbia.edu/tag/08DG) and
[08FE](https://stacks.math.columbia.edu/tag/08FE) online: the referenced literature
TeX file is absent from this machine's read-only repository. The proof follows
the direct-image difference construction and its two split restrictions.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.derived_open_difference_diagram`
(node `lem-sc-derived-open-difference-diagram`). No sorry remains in the item's module.

New hole: `AlgebraicGeometry.derived_open_intersection_mate_isIso`
(node `lem-sc-derived-open-intersection-mate-iso`). This is a decomposition:
one original hole closed, one strictly smaller hole added, net zero holes.
The remaining statement involves one object on one open and its canonical
restriction mate; it contains no difference arrow, biproduct matrix, gluing
isomorphism, or existential diagram. It is used twice, with the opens exchanged.
Its source and full proof in words are in its docstring and node.

The three private helpers `isIso_upper_triangular`, `isIso_lift_from_first`, and
`isIso_lift_from_second` are proved without holes. Empty opens, empty intersection,
entire opens, and zero objects satisfy the remaining statement: it is the
sectionwise identity on the appropriate intersection complex. Arbitrary
adjunction choices change it only by natural automorphisms.

## No longer needed

No original import or existing module is pruned. The direct dependency on
`lem-pc-restrict-derived-direct-image-open` moves below the new single-summand
node; it remains needed transitively and is not claimed as pruning.
The redundant trial import `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
was removed: the retained imports already provide its API. The second reader
also removed the redundant trial import
`Mathlib.CategoryTheory.Preadditive.Biproducts`; compilation confirms its API
is already available. `Mathlib.CategoryTheory.Adjunction.Additive` remains
necessary for `Adjunction.right_adjoint_additive`.
No triangle/fiber/glued-object theorem is imported or used. The blueprint unit
has empty realized statement/step lists; the difference-diagram construction
and its local split restrictions retain the existing route.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically sound. Its specified open-adjunction expression needs
an explicit type on the underlying adjunction between the shared sheaf-of-modules
categories before applying `mapDerivedCategoryRightDerivedAdjunction`; otherwise
Lean tries to synthesize the separate `HasDerivedCategory X.Modules` instance.
The implementation supplies that type, without changing any interface.

The existing `schemeDerivedDirectImage_openRestriction` gives a natural
isomorphism between functors. Identifying the specified adjunction mate with
that isomorphism is still required and is isolated in the new theorem, rather
than inferred from the mere existence of an arbitrary isomorphism.
No forced adaptation, statement repair, or disputed statement is involved.

## New nodes

`lem-sc-derived-open-intersection-mate-iso`, in
`dag/nodes/sec-picard-framework/lem-sc-derived-open-intersection-mate-iso.json`,
is the canonical single-summand open base-change mate calculation from Tags
08FE and 08DG. It has one public theorem in its own new module. Its statement
does not assume a cover, and its adjunctions are explicit parameters; no data
is chosen from an unproved existence theorem. No change record is needed. The second reader added a plain proof import of
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` to this new module,
matching its stated proof dependency.


## Second reading by R3

1. **Interfaces: pass.** Diffed the delivered module against the repository.
   The existing theorem signature is byte for byte identical, as verified by
   extraction and comparison. Its docstring and public import are unchanged;
   no definition or existing visibility changed. No other existing module is
   delivered, and no interface change record is needed.
2. **Proof and trust: pass.** Both delivered modules compile through lcompile.
   The item has no sorry. The only new sorry is the reported public theorem
   `AlgebraicGeometry.derived_open_intersection_mate_isIso`; no prohibited
   declaration or data chosen from an unproved existence theorem occurs.
   A scratch copy prints axioms for the target, split theorem, and all three
   private helpers: helpers use only propext, Classical.choice, Quot.sound;
   target and split theorem additionally use sorryAx, as explicitly reported.
3. **Split statement: pass.** Read the new theorem and its node independently,
   and checked Stacks Tags [08FE](https://stacks.math.columbia.edu/tag/08FE),
   [08BS](https://stacks.math.columbia.edu/tag/08BS), and
   [08DG](https://stacks.math.columbia.edu/tag/08DG).
   Restriction of a K-injective representative computes both sides with the
   same sections, and the canonical mate is the identity in these coordinates.
   Changing either adjunction composes with invertible natural automorphisms.
   Empty intersection, empty opens, O or P equal to the whole space, and zero
   objects cause no exception. The theorem supplies one summand's diagonal
   entry and is strictly smaller than the existential difference diagram.
   Independent LeanFinder search for Beck–Chevalley/open-immersion mates found
   underived restriction composition and counit APIs, not this theorem.
   Local searches found only bounded-below derived mate/base-change theorems
   in PlusAdjunction/PlusBaseChange, which do not settle the unbounded statement.
   The existing unbounded openRestriction theorem gives a Nonempty functor
   isomorphism without identifying this particular mate. No quick closure or
   duplicate statement was found. Its proof docstring and node are complete.
4. **Route and pruning: pass after import repair.** Read the explicit adjunction,
   overlap-equation, summand and triangular-matrix proofs from the target down.
   All map data is constructed; the only deferred fact is the single-summand
   mate calculation, used with the opens exchanged. The old direct-image
   restriction dependency remains below it; no old dependency or module is
   pruned. The unit's realized statement and step lists are empty, and the
   construction/split-restriction route is kept. Removed the redundant
   Preadditive.Biproducts import, retained the necessary Adjunction.Additive
   import, and added the new theorem's missing proof-dependency import.
5. **Nodes: pass.** Compared the existing node diff: only proof, proof_deps and
   proof_origin change. Both lean.statement strings equal their declarations
   verbatim, and proof_deps are exactly the unions of proof-step uses. Checked
   the new node's source, searches, provenance, blueprint ancestry, chapter,
   unit, status and lean record. They match the new module and the reduction.

Second-reading changes: two proof imports repaired and this review recorded.
No theorem statement, definition, proof body, or hole count was changed.
The delivery closes one original hole and adds one smaller hole: decomposition,
net zero holes, with no module pruning.
