## What changed

Repair B3/B5 (reviewer X-2b78b): added all seven requested inline citations to the
coordinate-constancy node statement, added the three requested statement dependencies,
and expanded source.place with the exact Stacks lemma and remark labels. The Lean
modules, signatures, proof, and remaining-hole count are unchanged.

Repair H1 (reviewer X-583d0): restored both delivered Lean modules to the review files mirror, byte-checked them against the exact packet diff and sandbox sources, and reran the required compilation. The return concerned missing mirror files; the Lean proof and statements are unchanged.

Added a complete stalk-coordinate construction in the item module. The finite inverse-image stalk germ bijection supplies coordinate maps and the finite pushforward stalk bijection makes the resulting product map injective. Added the strictly smaller coordinate-constancy theorem as a separate module; the main theorem now constructs the required preimage from it.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.finiteSurjectiveSetDescent_compatible_germ_lifts`
(node `lem-weil-pbc-sets-finite-descent-germ-lifts`). The private helper
`AlgebraicGeometry.descent_coordinate` is also proved and introduces no hole.

Added one hole: `AlgebraicGeometry.finiteSurjectiveSetDescent_coordinates_constant`
(node `lem-weil-pbc-sets-finite-descent-coordinates-constant`). This is a decomposition,
not a complete proof of finite descent: one hole closed, one added, net zero before
any global import-closure pruning. The item itself has no remaining `sorry`.
The main theorem's axiom check includes `sorryAx`; the coordinate helper uses only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the item's direct proof-only import
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`, replacing it with
`Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentCoordinatesConstant`.
Composition units remain available through the public definition dependency
`FiniteSurjectiveSetDescentInjective` and are needed by the split-off comparison proof.
No module is claimed to be globally pruned.

The following old `proof_deps` are no longer direct dependencies of the main proof:
`def-pc-fibre-product`, `def-weil-geometric-point`, `def-weil-pbc-geometric-stalks`,
`lem-weil-pbc-finite-composition`, `lem-weil-pbc-finite-morphism-permanence`, and
`lem-weil-pbc-sets-etale-inverse-image-composition-units`.
The fibre-product and composition argument is delegated to the coordinate-constancy
node; definitions needed by signatures remain unchanged. Finiteness of the composite
is unnecessary for this reduced main proof. The finite pushforward stalk theorem is
needed only for injectivity on the original morphism.

## Where the brief, the DAG or earlier work was wrong

The DAG proof step identifying the two comparison maps with coordinate projections is substantial and cannot be discharged by rewriting alone; it is split into the coordinate-constancy theorem.

## New nodes

`lem-weil-pbc-sets-finite-descent-coordinates-constant` is the strictly smaller comparison-coordinate statement used by the item.

## Earlier second reading (a previous round; superseded)

The item statement and the coordinate-constancy node preserve the finite, surjective, geometric-point, and compatibility hypotheses exactly. The new theorem is strictly smaller: it only asserts equality of two stalk coordinates and is used to combine the already proved coordinate bijection and unit formula.

## Earlier second reading (a previous round; superseded)

1. Compared the item against the repository by `diff` and byte-compared its existing
   theorem signature: unchanged. No existing definition, target statement, or public
   import changed. The only added declaration in the item is a private proved helper.
   No change record is required. The earlier definition-location change record was
   checked against the current imported definitions.
2. Compiled both files in import order with `lcompile.py --all`: pass. Checked scratch
   copies with `#print axioms`: the private coordinate helper uses only the three
   permitted axioms; the main theorem and split-off theorem additionally use `sorryAx`.
   Only the reported named coordinate-constancy theorem contains `sorry`. No forbidden
   declarations or hollow definitions were added. The coordinate maps come from a
   proved germ theorem whose formula uniquely determines them; the chosen geometric
   lift is confined to a theorem proof, not a data definition.
3. Reviewed the split-off theorem against [Stacks 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
   and [09Z3](https://stacks.math.columbia.edu/tag/09Z3), including comparison transport.
   Verdict: true, strictly smaller, and precisely sufficient for the main proof.
   Bijectivity and `hdiag` force each supplied coordinate map to agree with the
   canonical inverse-image stalk map. A pair of lifts gives a point of the fibre product;
   compatibility gives equal germs there and the composition-unit formula identifies
   their coordinates. Empty fibres are vacuous, a singleton fibre is reflexive, the
   identity morphism has one lift, and an empty sheaf has no section at a nonempty
   geometric point. Searches using new leanfinder, loogle, and grep queries, plus
   repository searches for comparison/stalk and finite-descent declarations, found no
   existing exact coordinate theorem. The remaining comparison calculation requires
   substantial pointed-neighbourhood transport and was not closed in this review.
4. Read the proof from the main conclusion downward: it constructs a lift, proves
   the diagonal formula using existing germ/naturality lemmas, and uses only stalk-map
   injectivity to finish from coordinate constancy. No shorter existing route was found.
   The report now lists every removed direct DAG dependency and the replaced import.
   Imports serve signatures, the implemented proof, or the documented proof plan of
   the remaining hole. The `sk-thm-iff` unit's realized statement and step remain
   unchanged; this decomposition is below its unit route.
5. Repaired the main node's stale proof plan and `proof_deps` to name the actual
   coordinate helper argument and split-off coordinate theorem. Corrected a nonexistent
   finite-morphism dependency ID in the new node, made its natural-language statement
   include the arbitrary coordinate maps and diagonal hypothesis, recorded its Lean
   signature verbatim, and added the independent search records. Removed finite
   pushforward bijectivity from the new node's proof dependencies: only its caller needs
   it. Every referenced node exists. Sources and proof origins retain the Stacks route.

Second-reading changes: corrected both DAG records and the progress/pruning report;
no Lean proof or existing signature required repair. This remains a one-for-one
hole decomposition, with no claimed globally pruned module.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered germ-lifts module with the repository version. The existing
   theorem signature is byte-for-byte unchanged; the only interface change is the
   declared split-off module and its import, both recorded in the DAG. No target or
   existing definition was altered.
2. Compiled both modules with `lcompile.py --all`. The only `sorry` is the named
   `finiteSurjectiveSetDescent_coordinates_constant` theorem. There are no forbidden
   declarations or hollow definitions. Scratch `#print axioms` checks show only the
   three permitted axioms for the private helper, with `sorryAx` additionally for
   the main and split-off theorem; the private coordinate construction is a real
   construction from `etaleSetInverseImageStalkGerm`.
3. Checked the split-off statement on empty, singleton, and identity fibres and against
   the Stacks 09Z2/09Z3 argument. It is true, strictly smaller than the item, and its
   hypotheses and conclusion are exactly those used by the caller. Repository and
   Mathlib searches found no duplicate declaration.
4. Read the proof downward from the target. The coordinate helper proves the diagonal
   unit formula, finite geometric-point lifting supplies a lift, and pushforward
   injectivity reduces the result to the split-off coordinate theorem. The unit route
   remains intact; removed imports and proof dependencies are listed above.
5. Checked both DAG nodes against the Lean declarations, including proof steps,
   dependencies, source, and unit. They agree, and the new node records its source,
   searches, and exact Lean signature.

Changed nothing in the Lean proof or theorem signatures during this second reading;
the delivery is ready for the required dry run and submission.

## Second reading by J2

1. **Interface: pass.** Independently diffed the delivered item against this machine's
   repository and byte-compared the existing theorem signature: identical. Its
   docstring, public imports, and all existing definitions are unchanged. The new
   coordinate theorem is a declared split-off statement, not an alteration of the
   item. The existing node changes only `proof` and `proof_deps`.
2. **Proof and trust: pass.** Recompiled both delivered modules in import order with
   `lcompile.py --all`; both pass. Compiled a scratch copy with `#print axioms` for
   the main theorem, private helper, and coordinate theorem. The helper uses only
   `propext`, `Classical.choice`, and `Quot.sound`; the two public theorems additionally
   use `sorryAx`. Exactly one named theorem has `sorry`, as reported above; no
   forbidden declaration or hollow definition occurs. Coordinate maps are supplied
   by the proved, uniquely characterized inverse-image germ comparison. The chosen
   geometric lift appears only inside the main theorem's proof.
3. **Split-off statement: pass.** Read the statement, its complete docstring argument,
   and the actual composition comparison definition against Stacks 09Z2 and 09Z3.
   Bijectivity and the diagonal formula force the coordinate identification to be
   the inverse of the canonical unit restriction. The pair of lifts defines a
   fibre-product point, where compatibility and the composition-unit formula give
   equal coordinates. Empty fibres are vacuous, singleton fibres are reflexive,
   identity morphisms have one lift, and an empty stalk admits no section germ.
   This is strictly the comparison-coordinate part of the argument: it constructs
   no preimage and uses neither surjectivity nor pushforward-stalk injectivity.
   New searches used leanfinder (inverse-image stalk composition and fibre-product
   projections), loogle (`CategoryTheory.Limits.colimit.ι_pre`), and grep
   (`stalk.*(comp|pullback)|fiber.*diagonal`), together with repository searches.
   No existing exact coordinate theorem was found. Closing this hole requires the
   remaining pointed-neighbourhood transport calculation, not a short rewrite.
4. **Route and pruning: pass.** Read from the main conclusion downward: stalk-product
   injectivity reduces equality to coordinates; the proved helper supplies the
   diagonal formula; finite geometric-point lifting supplies one coordinate; the
   split-off result supplies constancy. Imports support the signatures, this proof,
   or the remaining theorem's documented proof plan. Independently compared old
   and new `proof_deps`: all six removed dependencies are listed in `No longer
   needed`. No globally pruned module is claimed. The `sk-thm-iff` unit's realized
   statement and step remain untouched; this reduction stays below its route.
5. **DAG: pass.** Both recorded Lean signatures match their declarations exactly;
   each `proof_deps` equals the union of the proof steps' `uses`, and every statement
   and proof dependency ID exists. The new node records its source, proof origin,
   creation, blueprint ancestry, chapter/unit, search history, and full Lean record.
   Its statement cites the definitions and comparisons it uses. Existing node
   fields outside the permitted proof fields are unchanged.

Second-reading changes: appended this independent review and refreshed the search
log; no Lean proof, signature, or node required repair. One original hole is closed
and one strictly smaller hole is added: decomposition, net zero, no global pruning.
