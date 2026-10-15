## What changed

`Sheaf.CategoryTheory.RingedSliceExtensionExactness` proves the unchanged
`SheafOfModules.ringedSliceExtension_exact_iff` by rewriting exactness of the
original short complex as image-kernel equality, then applying its preservation
and reflection halves. The two halves are new named theorems in
`Sheaf.CategoryTheory.RingedSliceExtensionPreservesExact` and
`Sheaf.CategoryTheory.RingedSliceExtensionReflectsExact`.

The second reader restored the existing signature byte for byte, expanded the
natural-language proofs of both remaining obligations, and removed the narrower
adjunction and precoverage-local-section imports from the new modules. Reflection
now explicitly imports the preservation half needed by its homology argument.
The target's existing public imports, definitions and docstring are unchanged.
No change record is needed: no existing statement, definition or public import
was changed.

## Proved and sorry left

Hole closed: `SheafOfModules.ringedSliceExtension_exact_iff`
(node `lem-weil-pbc-ringed-slice-extension-exactness`).

Holes added:

- `SheafOfModules.ringedSliceExtension_preserves_exact`
  (node `lem-weil-pbc-ringed-slice-extension-preserves-exact`).
- `SheafOfModules.ringedSliceExtension_reflects_exact`
  (node `lem-weil-pbc-ringed-slice-extension-reflects-exact`).

This is a decomposition, not a completed proof of exactness: one original hole
closed and two strictly smaller directional obligations added (net -1).
The target still depends on `sorryAx` through these obligations. No definition
was added, and no object was selected from an unproved existence theorem.

## No longer needed

Removed direct imports from the target:

- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`;
- `Sheaf.Paper.SiteSheafificationSectionsLocal`;
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`.

The first two are also removed from both new modules: their small-category or
precoverage/pullback hypotheses do not fit this theorem. The preservation module
does not need the underlying-set comparison import. Reflection retains
`Mathlib.CategoryTheory.Sites.PreservesSheafification` for the local unit argument.

Every old target `proof_deps` entry is replaced as a direct dependency:
`lem-pur-site-restriction-module-adjunction-exact`,
`def-weil-sheaf-of-modules-category`, `def-weil-extension-by-zero-presheaf`,
`def-pur-localized-ringed-site`, `lem-pc-sites-module-sheafification-interface`,
`lem-pc-sites-sheafification-underlying-sets`, and
`lem-weil-pbc-site-sheafification-sections-local`.
The target now has exactly the two half-results as proof dependencies. The
construction and sheafification nodes remain below those halves where used.
The new plans use the direct-sum adjunction construction and Mathlib's local
injectivity for covering sieves; neither uses the narrower adjunction theorem
or the precoverage-local-section theorem. No claim is made that either removed
module becomes unreachable from every target elsewhere in the library.

## Where the brief, the DAG or earlier work was wrong

The original plan described the existing exact-adjunction theorem as applying
on arbitrary ringed sites. Its actual Lean signature requires `SmallCategory C`,
a `Precoverage`, and the isomorphism, composition, base-change and pullback
conditions. The target instead has independent object/morphism universes and
an arbitrary Grothendieck topology. Likewise, the cited local-section theorem
uses a precoverage with those conditions. The new docstrings explain the
adjunction construction and the local argument directly with covering sieves,
without pretending that either restricted theorem can simply be instantiated.

The previous report called this a completed proof and omitted its net hole
count. Only the reduction is complete. Preservation still requires constructing
the general adjunction and proving preservation of monos; reflection still
requires constructing and proving injectivity of the natural unit. Mathlib's
`Functor.reflects_exact_of_faithful` can shorten the final reflection step once
that unit gives faithfulness, but does not supply the concrete unit itself.

## New nodes

`lem-weil-pbc-ringed-slice-extension-preserves-exact` is the forward implication.
Its proof plan constructs the adjunction by maps out of the direct sum, obtains
right exactness, and uses sectionwise injections plus exact sheafification to
preserve monos. This is a proper part of the original equivalence.

`lem-weil-pbc-ringed-slice-extension-reflects-exact` is the reverse implication.
Its proof plan constructs the monic unit using local injectivity, detects zero
objects, and uses preservation to identify the middle homology quotient after
extension. It imports the preservation module without a cycle. Both nodes have
self-contained statements, verbatim Lean signatures, sources, creation records,
and actual searches using leanfinder, loogle and grep. A separate LeanSearch
request returned Internal Server Error; its unavailability is recorded without
a mathematical verdict.

## Second reading by S1

1. Compared every delivered module against the repository. Only the exactness
   module existed there. Its theorem signature is now byte-for-byte identical;
   only proof-only imports and its proof body differ. No existing definition,
   public import, target statement, or other group's module changed. Verdict: pass.
2. Compiled all three delivered modules locally using `lcompile.py`. The only
   two `sorry` terms are the named new theorems listed above; no forbidden
   declarations, hollow definitions, or witness selections occur. Scratch copies
   with `#print axioms` compiled for all three declarations and showed exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is
   expected because the two documented obligations remain. Verdict: pass as a
   decomposition, not an axiom-free theorem.
3. Read both split statements, the direct-sum construction, the actual existing
   adjunction signature, the module/underlying-set sheafification interfaces,
   and Stacks Tags 03DJ and 0E8G. Checked the zero complex, objects with no maps
   to U (zero direct sum), and empty covering sieves (sheaf separatedness still
   applies). Both halves are true proper directional parts. Independent
   leanfinder, loogle and grep searches found generic exact/faithful-functor
   criteria but no duplicate at these universes and topology. The prior
   docstrings were too abbreviated; the repaired proofs include the adjunction,
   preservation of monos, and the exactness required for the homology quotient.
   Verdict: pass with those repairs.
4. The target reduces directly to the two directions, with no merely renamed
   equivalence. The current smaller-site adjunction is not a shortcut at the
   target's hypotheses. Removed the unused narrower imports; retained the
   underlying-set comparison only in reflection. Listed all seven old direct
   proof dependencies above. Read `dag/units/sk-thm-properbasechange.json`:
   this subsidiary node is not a realized statement or step, and the unit's
   statement, three steps, realized bindings and cited route stay intact.
   Verdict: pass.
5. Checked the existing node's proof, proof_deps and proof_origin against the
   actual two-direction reduction. Repaired both new node plans to match their
   complete docstring arguments, added preservation as a reflection dependency,
   removed inapplicable proof dependencies, and replaced vague search claims
   with the actual independent search results. Node signatures match the Lean.
   Verdict: pass.

Second-reading changes: restored signature whitespace; completed both proof
explanations; removed inapplicable imports and dependencies; made reflection's
preservation dependency explicit; corrected the node statements/searches and
report's hole accounting. No additional Lean hole was closed in this reading.
Sources read: https://stacks.math.columbia.edu/tag/03DJ and
https://stacks.math.columbia.edu/tag/0E8G.

The first preflight found a missing LeanSearch-category record on the new nodes.
The reader ran that service, recorded its Internal Server Error, and reran the
required delivery checks; successful independent search results were retained.
