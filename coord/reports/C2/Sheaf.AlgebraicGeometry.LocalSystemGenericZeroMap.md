## What changed
The existing target `AlgebraicGeometry.Scheme.eq_zero_of_generic_sheafFiber_eq_zero`
now reduces generic vanishing to vanishing of stalk maps, then applies the existing
`AlgebraicGeometry.Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint` to the
morphism and zero. A local small-limits instance resolves universe inference;
`Point.sheafFiber_additive` supplies preservation of zero.

The propagation step is stated in the new module
`Sheaf.AlgebraicGeometry.GenericStalkVanishingPropagation`. The target module adds
three plain proof imports: that module,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper`.
Its existing public import and existing target signature are unchanged.
The target node records the actual two-step reduction. No definition or existing
statement changed; no change record is required.

## Proved and sorry left
The only original declaration,
`AlgebraicGeometry.Scheme.eq_zero_of_generic_sheafFiber_eq_zero`, has a complete
Lean reduction with no local sorry. It still depends on the open propagation lemma;
this is a partial proof delivery, not an axiom-free proof of the target.

The sole remaining sorry is the named theorem
`AlgebraicGeometry.Scheme.all_sheafFiber_map_eq_zero_of_generic` in
`Sheaf.AlgebraicGeometry.GenericStalkVanishingPropagation`, node
`lem-weil-pbc-generic-all-stalks`. Its docstring gives the source and a complete
natural-language proof. No other sorry is added.

Both delivered modules compile locally without errors or warnings. A scratch copy
with explicit `#print axioms` commands confirms the target and the propagation
lemma use only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
The existing equality-detection theorem has only the three permitted axioms.

## No longer needed
The proposed new `eq_zero_of_all_sheafFiber_map_eq_zero` lemma and its proposed node
`lem-weil-pbc-all-stalk-map-zero-implies-zero` were removed: the library already
proves the more general equality-detection result used directly in the target.

Of the target's old proof_deps, `prop-weil-pbc-geometric-stalks-exact` is no longer
needed by this argument: it represents source germs directly and never forms an
image sheaf. The six other old dependencies
`def-constructible-constant`, `def-constructible-locally-constant`,
`def-sc-generic-point`, `def-weil-pbc-etale-site`,
`def-weil-pbc-geometric-stalks`, and `lem-weil-pbc-flat-lfp-open`
are no longer direct dependencies of the target but remain dependencies of the
propagation node. `lemma-weil-pbc-geometric-stalk-conservative` remains a direct
dependency through the equality theorem in its module. No original import is
removed, and no claim is made that another module becomes globally unreachable.

## Where the brief, the DAG or earlier work was wrong
The first worker overlooked the existing stalkwise equality theorem, leaving an
unnecessary conservativity sorry. Its suggested proof by applying conservativity
to phi minus zero was incomplete: conservativity detects isomorphisms, not zero
maps directly; joint faithfulness, supplied by the existing theorem, is the needed
argument. The propagation node's top-level statement was accidentally copied from
the conservativity lemma, its search records did not describe propagation, and the
target node had not been updated to the written reduction. These are repaired.

## New nodes
`lem-weil-pbc-generic-all-stalks`, under
`dag/nodes/sec-proper-base-change/`, states exactly the remaining generic-to-stalk
propagation step. Its Lean record points to
`lean/Sheaf/AlgebraicGeometry/GenericStalkVanishingPropagation.lean` and reproduces
the signature verbatim. It carries the same chapter and unit as the target, source
Tags 09BG (3) and 09BH (3), four proof steps, and genuine search records from this
reading. LeanSearch returned Internal Server Error; LeanFinder and Loogle found
only neighbouring results, and the Mathlib grep found no exact theorem.
There are no change records.

## Second reading by C2
1. Compared the delivered target module against the repository with diff. The
   signature of the sole existing declaration is byte-for-byte unchanged, as are
   all existing definitions and the public import. All added imports are plain
   proof imports. Verdict: pass.
2. Compiled both files in import order using lcompile.py. Checked the sole sorry is
   exactly the public named propagation theorem, with no forbidden declaration or
   hollow definition. Explicit scratch-copy axiom checks show only the three
   permitted axioms and the expected sorryAx for the unfinished propagation step.
   Verdict: pass as a partial proof delivery.
3. Read the remaining split against Stacks Tags 09BG and 09BH. Tested zero source,
   zero target and zero coefficient ring (automatic), a one-point scheme (the
   generic hypothesis already covers every point), and the empty scheme (excluded
   by the generic point). The arbitrary-module argument uses one element at a time,
   so no finiteness is hidden. Etale trivializations need not be irreducible: the
   composite pointed neighbourhood has nonempty open image in X, which suffices.
   The split concludes only vanishing of stalk maps; the target separately uses
   joint faithfulness to conclude equality of sheaf morphisms. Repeated searches
   with different words via msearch.py (LeanFinder, Loogle, grep, and the unavailable
   LeanSearch), plus rg on both source roots. ConstantSubsheafGeneric has finite
   ring/module hypotheses; LisseGenericKernel has a different coefficient category,
   local-constancy predicate and monicity conclusion. Restriction's dense-open
   theorem requires vanishing on an open, which the generic stalk hypothesis does
   not supply. No exact replacement for propagation was found. Verdict: pass.
4. Used the shorter existing equality-detection route and removed the redundant
   split. All imports are used. Enumerated every old proof_dep above. Read
   dag/units/sk-thm-p1.json, including realized: this helper is below its realized
   nodes and keeps the local-constant/generic-point argument. No unit step or
   realized node is bypassed. Verdict: pass.
5. Checked the target's proof/proof_deps/proof_origin match the actual reduction;
   the new node's statement, Lean signature, module, source, unit, searches and
   proof-dependency union agree. Corrected the copied top-level statement and
   replaced unsubstantiated searches with searches performed during this reading.
   Verdict: pass.

Changes by the second reader: removed the redundant conservativity lemma and node;
used the existing jointly faithful stalk theorem; moved propagation to its own
module; expanded its proof docstring; corrected its node and search evidence;
updated the target node and completed the pruning report. One sourced geometric
propagation step remains open; closing it requires formalizing the pointed etale
neighbourhood argument, beyond a short repair.
