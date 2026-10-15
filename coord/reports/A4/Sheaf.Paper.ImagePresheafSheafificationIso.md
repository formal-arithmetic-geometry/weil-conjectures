## What changed

Corrected CategoryTheory.imagePresheaf_sheafification_iso to use values
Type (max u v) on C : Type u with Category.{v} C. The former arbitrary independent
Type w signature is false, as already identified in the P3 review of
SiteSheafificationSectionsLocal. Both conclusions are retained; no target or definition
changes. Change record: coord/changes/imagePresheaf_sheafification_iso-size.md.

Replaced the sole sorry with a seven-line proof from Mathlib. Reflect local surjectivity
through presheafToSheaf, pass it to the image inclusion using the range factorization,
and apply the locally-bijective criterion for becoming an isomorphism after sheafification.
Removed the two unused Sheaf proof imports. The node now records that exact short route,
its corrected universe convention, and the review of its sole DAG citer. There are no
new nodes, new declarations, or forced adaptations.

The unchanged sole direct importer, Sheaf.Paper.CechNerveFreeHomology (held by T3), compiled
against the corrected module. A compiled example also checks the exact intended
application to Type u-valued presheaves on a SmallCategory in Type u. Temporary verification
files are kept under scratchpad and are not part of the delivery. The change record lists
every downstream module and its holder at inspection time; none contains an existing
application requiring adaptation. The sole DAG citer remains valid in its common universe u.

## Proved and sorry left

Closed CategoryTheory.imagePresheaf_sheafification_iso
(lem-weil-pbc-image-presheaf-sheafification-iso), after the explicitly documented universe
correction. This proves the corrected intermediate statement, not the false former signature.
There are zero sorries left in the item and zero holes added or split off. There is no
unproved dependency from Sheaf or WeilConjectures: the proof uses Mathlib only.

The module and its unchanged direct importer compile without errors or warnings.
#print axioms CategoryTheory.imagePresheaf_sheafification_iso reports exactly
propext, Classical.choice, and Quot.sound. No global build was run. The required
--no-push dry run is the final verification; nothing is delivered or pushed by this worker.

## No longer needed

Removed proof imports:

- Sheaf.Paper.SiteSheafificationSectionsLocal, node
  lem-weil-pbc-site-sheafification-sections-local. Mathlib's proved comparison replaces
  the hand-written local-representation and local-equality argument.
- Sheaf.CategoryTheory.SiteCoveringAxioms, node def-weil-pbc-sites-and-cohomology.
  No IsSiteForCoverings declaration is used; the theorem works with GrothendieckTopology.
  The conceptual site node remains a statement dependency, so this is import pruning,
  not a claim that the entire DAG notion disappears.

The longer planned proof no longer needs these separate proof-dependency nodes:

- lem-weil-pbc-sheafification-sets-exact;
- lem-weil-pbc-site-sheaf-sets-epi-locally-surjective;
- lem-weil-pbc-sheaf-sets-mono-epi-iso.

These are Mathlib leaves and have no separate Sheaf modules to withdraw. Their general
Mathlib API may occur internally in Mathlib's proved local-bijection results; no additional
project proof obligation is introduced. def-weil-pbc-sheafification also leaves proof_deps
but stays in stmt_deps and its Mathlib module stays publicly imported, since the statement
uses presheafToSheaf. The node's proof_deps is empty because the complete seven-line Lean
proof uses only Mathlib, meeting stages/1-dag.md section 2's closed-proof rule.
No unit statement or realized proof step is bypassed: sk-prop-h2 does not list this node
in its realized statement or steps. The Cech-nerve parent's image-replacement argument stays.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (former signature): HasWeakSheafify J (Type w) on a site whose universe
may be larger than w does not imply that weak sheafification reflects local surjectivity.
The candidate Mathlib proof in this node omitted the size condition on
J.WEqualsLocallyBijective (Type w). This is a mathematical error, not just failed instance
search. P3's reviewed correction of sheafification_sections_local already flagged this
specific item as false at that generality. No new false auxiliary theorem was introduced.

The existing U2 Boolean-site counterexample applies to this theorem as follows. Let A be
an infinite alphabet containing every Type w type, and let B be the complete Boolean algebra
of regular opens of A^N with join covers. Every Type w-valued sheaf is subterminal: two
distinct sections, restricted to a nonzero piece on which they never agree, would give
independent binary choices on an A-indexed disjoint partition of a cylinder. Gluing then
injects (A -> Bool) into a small section type, contradicting Cantor. The small sheaf reflector
still exists as sheaf closure of support inside the terminal sheaf. Both constant presheaves
1 and 2 reflect to the terminal sheaf. Hence the inclusion 1 -> 2 satisfies the old
sheafified-surjectivity hypothesis, while the second element has empty image sieve at the
nonzero top and cannot lift locally. The full argument, including the empty-cover,
pullback, cardinality, and universal-property checks, is in the change record and the
previous U2 report. This counterexample is natural-language mathematics, not claimed as a
Lean formalization of the negation.

The corrected value universe contains site objects and morphisms and matches the ordinary
plus construction. Both conclusions now follow without extra hypotheses. The sole DAG citer
lem-weil-pbc-cech-nerve-free-homology has SmallCategory C and Type u values, so its statement
and intended application are unaffected; the application was compiled separately.

Sources were read at the Stacks pages for [00WK](https://stacks.math.columbia.edu/tag/00WK),
[00WJ](https://stacks.math.columbia.edu/tag/00WJ),
[00WN](https://stacks.math.columbia.edu/tag/00WN), and
[00WM](https://stacks.math.columbia.edu/tag/00WM), because literature/stacks-project/sites.tex
is absent here. The exact Mathlib signatures and Type (max u v) instance were read locally.
LeanFinder, Loogle, and grep searches were run with msearch.py and are recorded in
searches.jsonl. No source library proof of the same theorem was found.

Edge cases: the proof never chooses an object or a global section; it works for empty
categories, empty presheaf values, empty covering sieves when they are covering, and
zero/empty image presheaves. The image inclusion is locally injective independently of
whether its objectwise images are inhabited. No arbitrary data is chosen from a theorem
with an unproved existence proof. There is no definition in this module.

## Second reading by A4

1. **Signatures and accidental changes — PASS.** I diffed the delivered module against
the repository version and found the proof-import removals and the intentional universe
correction from `Type w` to `Type (max u v)`. The changed theorem signature is declared in
`coord/changes/imagePresheaf_sheafification_iso-size.md` and in the node's
`statement_change`; no other declaration signature or definition changed. The sole DAG
citer uses `C : Type u` and `Type u` values, so its elaborated application is unchanged.

2. **Compilation and proof status — PASS.** The module compiles with
`python3 /home/ubuntu/weil-launcher/lcompile.py`, with no errors or warnings. The sole
former `sorry`, `CategoryTheory.imagePresheaf_sheafification_iso`, is closed. There are
no new sorries, axioms, unsafe or opaque declarations, and the proof uses Mathlib's
local-surjectivity comparison, range factorization, and locally-bijective criterion.
The declaration's checked axioms are `propext`, `Classical.choice`, and `Quot.sound`.

3. **Statements and split nodes — PASS.** No auxiliary statement or module was added,
so there is no split-off hole to validate and no duplicate library theorem. The corrected
universe statement is the strongest valid form supported by Mathlib's
`WEqualsLocallyBijective` instance; the former arbitrary-small-value form is recorded as
disputed with its counterexample in the report and change record.

4. **Route and pruning — PASS.** The proof follows a shorter direct Mathlib route: reflect
local surjectivity, transfer it through `Subfunctor.toRange_ι`, and apply
`W_of_isLocallyBijective` followed by `W_iff`. The two unused Sheaf proof imports and the
three longer proof-dependency leaves are recorded under `## No longer needed`. The
`sk-prop-h2` unit has no realized statement or step involving this node, so no unit route
was bypassed.

5. **DAG agreement — PASS.** The item's `proof`, empty `proof_deps`, and `proof_origin`
match the declarations actually used. Its Lean record reproduces the corrected theorem
signature verbatim, and the change record names the sole downstream citer and its holder.

I changed only this second-reading report section; the module, node, and change record
already satisfy the checks above.
