## What changed

Proved the three remaining holes in
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` without changing any
existing signature, visibility, or definition. The stalk algebra maps now follow from
Mathlib scheme-stalk composition and congruence. The complex stalk isomorphism is the
existing natural module stalk isomorphism lifted to complexes, with explicit equality
transport. Coordinates use the existing K-flat and functorial K-injective resolutions,
comparison of universal derived counits, and Mathlib's K-injective Hom bijection.
Two private, fully proved helpers handle counit invertibility and lifting derived maps.

Added proof-only imports of `Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`, and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`. Updated the two existing nodes'
proof routes to agree with the Lean. No new statements or adaptations.

## Proved and sorry left

Closed 3 of the 3 original holes:

- `AlgebraicGeometry.SingleComplexBaseChange.exists_stalk_algebra_maps`
  (`lem-single-complex-stalk-algebra-maps`).
- `AlgebraicGeometry.SingleComplexBaseChange.exists_tensorStalkIso`
  (`def-pc-single-complex-base-change-stalk-condition`).
- `AlgebraicGeometry.SingleComplexBaseChange.nonempty_coordinates`
  (`def-pc-single-complex-base-change-stalk-condition`).

No direct `sorry` remains in the delivered module, and no holes are added or split off.
These are proofs from existing declarations, as required by stage 3; the imported
resolution and derived-pullback constructions retain their existing upstream holes.
The already-proved `exists_tensorMap` proof is retained.

## No longer needed

None of the original imports, nodes, or modules is removed. All three original public
imports supply notions used by the statements or definitions. A tentative proof import
of `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero` was removed after checking
that the necessary instances are already available through retained imports.
The unit's `realized` statement and step lists are empty; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps despite recording two unproved existence theorems;
its proof field now documents their Lean constructions and the existing tensor-map proof.
The previous intermediate algebra-map node is directly provable from Mathlib and needs
no additional decomposition. The signature of `exists_derivedPullbackComposition`
exports the universal property but not K-flat invertibility of its selected counit.
The proof obtains the latter by comparing universal counits with the K-flat-computing
counit supplied by `exists_derivedPullback`, rather than assuming the missing clause.
The local literature payload is absent on this machine; the cited Stacks tags 0DJ8,
0DJ9 and 070I were read on the official Stacks site. No source or statement correction
was necessary.


## Second reading by T4

1. **Interfaces unchanged — PASS.** Read the entire sandbox module against the
   repository module with `diff -u`, and checked the declaration table with
   `stage3_delivery.diff_module`: no existing statement changed. The three original
   public imports, universes, section variables, declaration visibility, all existing
   definitions, and the already-proved `exists_tensorMap` body are unchanged. The
   only new declarations are two private, fully proved proof helpers; all three
   additional imports are plain proof imports. No change record or adaptation is
   required. Relevant existing change records do not require further edits here.

2. **Proof and axioms — PASS, relative to existing upstream holes.** Compiled the
   delivered module through `lcompile.py --all` without errors or warnings (36 s).
   Scanned the source: no direct `sorry`, axiom, unsafe/opaque declaration, external
   implementation, kernel-check bypass, or hollow definition. Compiled a scratch
   copy with `#print axioms` for all three newly proved theorems, both private
   helpers, the retained tensor-map theorem, and the selected maps and predicate.
   `exists_stalk_algebra_maps`, `exists_tensorMap`, `tensorMap`, and the generic
   chain-map lifting helper use only `propext`, `Classical.choice`, `Quot.sound`.
   `exists_tensorStalkIso`, `nonempty_coordinates`, the counit helper,
   `tensorStalkIso`, and `StalkCondition` additionally use upstream `sorryAx`.
   Thus this delivery closes three local holes, not the transitive proof closure.
   Choices of resolutions and chain maps occur inside a proof of `Nonempty`, not
   inside a new data definition. All existing data definitions remain byte-identical.

3. **Split statements and small cases — PASS.** There are no new public statements,
   nodes, or split-off holes. Read the private helpers: counit invertibility follows
   by comparing two universal left-derived counits, then evaluating their factorization
   on a K-flat complex; map surjectivity follows from Mathlib's K-injective Hom
   bijection and fullness of the homotopy quotient. Neither restates coordinates.
   The algebra-map proof uses only square commutativity and the commutativity of the
   target stalk; it does not insert flatness or nonzero assumptions. The stalk-complex
   proof transports an arbitrary equal ring map before lifting a natural isomorphism,
   so its components are the exact stipulated maps. Zero complexes, arbitrary
   degrees, identity squares and empty schemes introduce no excluded cases.

4. **Shortest route, imports and unit route — PASS.** Independently searched the
   Mathlib homology sources and both library roots for chain-map lifting, K-injective
   localization and universal counit invertibility. The relevant Mathlib result is
   precisely `CochainComplex.IsKInjective.Qh_map_bijective`, already used here.
   Analogous generic lifting and pullback-counit helpers exist in
   `DerivedModuleDirectSums` and `GlobalHomAdjunctionIso`, but are private; the latter
   also depends on this module. Retaining these short private proofs avoids adding
   an unrelated dependency or an import cycle. The additional Loogle query returned
   a query-parse diagnostic rather than usable search evidence; conclusions above
   rest on the source search. Each new proof import supplies a theorem actually used.
   The original public imports supply `counit`/additivity, the specified stalk
   isomorphism, and the cohomology model used in definitions. Both original nodes
   had empty `proof_deps`, so there is no omitted old dependency to prune. Read
   `dag/units/sk-thm-picard-semicon.json`: its `realized.statement` is empty and its
   one `realized.steps` entry is empty. This proof changes neither the unit record
   nor any unit-level route. `No longer needed` is complete; no module is pruned.

5. **DAG agreement — PASS.** Compared both node JSON files with the repository.
   Only `proof`, `proof_deps`, and `proof_origin` differ. The algebra-map node records
   the actual stalk-map composition/congruence argument and needs no DAG proof
   dependencies. The definition node records tensor lifting, transported natural
   stalk isomorphism, K-flat resolution, functorial K-injective resolution, comparison
   of universal counits, and lifting of a derived map. Checked its cited declarations
   against `KFlatResolution`, `RingedSiteKInjectiveResolutions`, `DerivedPullback`,
   `DerivedPullbackComposition`, `TensorPullbackStalk`, and the Mathlib-match record
   for `lem-weil-pbc-kinjective-hom-derived`. Its `proof_deps` is exactly the union
   of its steps' `uses`; source and origin explain the proof actually written.

**Second-reading changes:** appended this independent review and retained the Lean
proofs and DAG edits unchanged. Closed holes: the three declarations listed above.
Added holes: none. Split-off statements: none. Pruned imports/modules/nodes: none.
