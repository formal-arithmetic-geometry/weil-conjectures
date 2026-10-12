## What changed

`Sheaf.RingTheory.LciConormalFreeRankCodimension` now proves
`Ideal.exists_basis_cotangent_localization_of_completeIntersection` with its original
signature and public imports unchanged. Its complete proof extracts a concrete presentation,
rules out the zero-ring branch using a prime over q, transports dimension through the
principal-localization open embedding and presentation homeomorphism, applies the existing
global complete intersection equidimensionality theorem, and combines a stable conormal
comparison with local-ring cancellation.

The returned duplicate `Ideal.dimAt_openEmbedding` has been removed. The item now
uses the existing `Algebra.dimAt_openEmbedding` from
`Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension` at both dimension transports.
The proof-only `import all` exposes that private theorem to proof elaboration without
changing any public import or adapting its defining module. The import-direction check
confirms that this introduces no cycle. The parent node records this dependency.

The remaining private, sorry-free helper `Ideal.basis_of_stably_free` constructs split
linear maps, derives projectivity and finite generation, applies Mathlib local freeness,
and computes finrank using products and finite function modules. No residue-field tensor
rank computation is needed. It changes no public signature or definition.

The new module `Sheaf.RingTheory.CompleteIntersectionPresentationStableConormal` states
`Ideal.stable_conormal_of_completeIntersection_presentation`, the localized comparison step
of the original plan for an explicit presentation. It concludes only a stable isomorphism,
not freeness, a basis, a dimension-at-q formula, or d ≤ n. Its full proof is documented and
its dependency imports retain the existing regular-sequence and comparison theory. The
parent node records the implemented route; the new node records the remaining argument.
No other module is adapted and no statement or definition is changed.

Both delivered modules compiled without errors or warnings with lcompile.py --all. Edge
cases checked mathematically: q excludes a zero quotient and hg excludes a zero principal
localization; t = 0 allows an empty regular sequence; m = t gives dimension zero; n = 0
forces the eventual conormal rank zero through the proved stable-rank equation. The
cancellation helper also covers a = b, a = 0, and the zero module without a positive-rank
hypothesis. All arithmetic uses the actual inequalities t ≤ m and m ≤ t+n, so no truncated
subtraction is used to infer an unjustified bound.

## Proved and sorry left

Closed the one direct hole in
`Ideal.exists_basis_cotangent_localization_of_completeIntersection`
(node `lem-weil-pbc-lci-conormal-free-rank-codimension`). No direct sorry remains in the item.

Added one direct hole, exactly the whole proof of the public theorem
`Ideal.stable_conormal_of_completeIntersection_presentation`
(node `lem-weil-pbc-complete-intersection-presentation-stable-conormal`), in its own module.
This is a decomposition: one upper hole closed and one strictly smaller hole added,
not a claim of an unconditional sorry-free proof or a positive net-hole reduction.
The new statement isolates original steps 3–5 and the local-ring identification from step 1;
the original theorem's presentation extraction, dimension argument, local freeness,
rank calculation, and bound are complete Lean proofs.

The existing imported equidimensionality, local regular sequence, regular sequence conormal,
and principal-localization comparison declarations retain their existing holes and were
not edited. They are existing downstream items, not holes introduced by this delivery.

## No longer needed

Removed these direct proof imports from the item:
`Sheaf.RingTheory.ConormalModulePrincipalLocalization`,
`Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence`,
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`, and
`Sheaf.RingTheory.RegularSequenceConormal`. They remain dependency imports of the new
stable-comparison module and are therefore moved, not globally pruned. Their nodes remain
needed through that new node. No former Sheaf module can be claimed to leave the targets'
import closure in this delivery.

The implemented argument no longer needs the scheme-level open-immersion route:
`lem-weil-pbc-principal-localization-open-immersion` and `def-weil-open-immersion`, or the
separate invocation of `lem-weil-pbc-dimension-at-point-open-subspace`. The reused
`Algebra.dimAt_openEmbedding` and Mathlib `PrimeSpectrum.localization_away_isOpenEmbedding`
replace those steps, and those three node ids were removed from the parent's proof_deps.
The definition module `WeilConjectures.Mathlib.Topology.KrullDimension` remains needed.
The final residue-field isomorphism and residue-field tensor dimension calculation are
unnecessary; the new comparison still uses local-ring identification, so
`lem-weil-pbc-localization-prime-residue-field-iso` itself is not pruned globally.

For completeness, the old parent proof dependencies absent from its new `proof_deps`
are exactly the following eleven nodes. Three are no longer used on this route:
`lem-weil-pbc-principal-localization-open-immersion`, `def-weil-open-immersion`, and
`lem-weil-pbc-dimension-at-point-open-subspace`. Seven are moved into the stable-comparison
node: `lem-weil-pbc-localization-prime-residue-field-iso`,
`lem-weil-pbc-global-complete-intersection-local-regular-sequence`,
`def-weil-pbc-regular-sequence`, `lem-weil-pbc-regular-sequence-conormal-free`,
`lem-weil-pbc-localization-module-exact`,
`lem-weil-pbc-conormal-module-principal-localization`, and
`def-weil-pbc-module-localization-away`. The remaining
`def-weil-pbc-mv-polynomial-ring` is still a statement dependency of both nodes;
it is no longer separately listed as a parent proof step dependency. This list records
changes to the direct route, not a claim that these modules leave the global import closure.

All remaining original proof dependencies either occur in the parent's implemented proof
or in the stable-comparison node. Statement imports remain public as before; new imports in
the item are proof-only imports. No unused newly added proof import remains in the item.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated an existing private dimension-transport theorem.
This repair deletes the duplicate and imports and uses the existing theorem exactly as
requested. Lean's `import all` makes it available in proofs; its defining module and
visibility are unchanged. The previous dry-run tool mismatch is historical; validation
is rerun for this repair without modifying any tool.

No mathematical error or disputed statement was found. The plan left substantial glue
implicit: Extension.Cotangent versus Ideal.Cotangent scalar actions, localization of the
regular-sequence conormal, and successive module localizations. The existing declarations
do not directly provide the assembled stable equivalence with the exact fraction-module
action used by the item. This glue is now an explicit sourced intermediate theorem.

The planned residue-field calculation can be shortened using Mathlib finrank_prod and
finrank_pi after freeness has been proved. Dimension transport reuses the existing theorem on
prime spectra, without scheme-level open-immersion machinery. These are changes below the
unit level. None of the sk-thm-p1 realized statement or step nodes is bypassed or changed.

The local literature/stacks-project/algebra.tex file is absent on this machine. The cited
last paragraph and comparison equation were checked against the official Stacks pages
https://stacks.math.columbia.edu/tag/00SC and https://stacks.math.columbia.edu/tag/00S6.
LeanSearch returned an internal-server error; this is recorded as unavailable, not as a
no-match result. LeanFinder, Loogle, Mathlib/source rg searches and blueprint searches ran.

## New nodes

`lem-weil-pbc-complete-intersection-presentation-stable-conormal`, in
`dag/nodes/sec-proper-base-change/`, states the stable comparison for an explicit quotient
presentation of S_g of dimension m-t. Its module is
`lean/Sheaf/RingTheory/CompleteIntersectionPresentationStableConormal.lean`. Its four proof
steps spell out prime/local-ring identification, local regularity, conormal localization,
and localization of the principal-presentation comparison. It inherits the parent's
chapter, unit and blueprint ancestry. It is strictly an intermediate step: the complete
local-ring cancellation and dimension-at-point argument are in the item. No change record
is needed because no existing public interface changes.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository versions. The existing target declaration has the same signature byte for byte; the new module adds only the split-off intermediate declaration. No existing definition or target statement changed.

2. Compiled both modules with `lcompile.py --all`; they compile without errors or warnings. The target proof contains no `sorry`; the sole remaining `sorry` is the named public intermediate theorem, with its source, proof description, and DAG node. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition was introduced.

3. Checked the split-off statement against the explicit presentation argument and the Stacks Project source. It is true and strictly weaker than the target: it asserts only a stable linear equivalence and does not assert freeness, a basis, a dimension-at-point formula, or the codimension bound. Its declaration is new in the library and its node records the statement, source, proof steps, and searches.

4. Read the proof from the target downward and checked the shorter Mathlib route used for local freeness and finrank arithmetic. The private dimension and stable-free helpers are proof-only, and the removed imports and pruned proof dependencies are listed above. The unit route remains represented by the stable comparison node and the existing equidimensionality dependency.

5. Checked the DAG against the Lean declarations: the parent node's proof steps and dependencies match the implemented proof, and the new node matches the split theorem and its module. The unit record is unchanged and still realizes the parent statement and route.

I changed only this report by adding this second-reading record; no Lean statement, definition, or proof was altered during the second reading.

## Second reading by A4

1. **Unchanged interface — pass.** Diffed the item against the read-only repository.
   The existing theorem signature is byte for byte identical, as are its docstring and
   public imports. The only other delivered Lean module is new; no existing definition,
   statement, visibility, or module held by another group changes. The parent node differs
   only in `proof`, `proof_deps`, and `proof_origin`; there are no change records required.

2. **Proof and axioms — pass as decomposition.** Recompiled both modules in import order
   using `lcompile.py --all`, with no errors or warnings. A scratch copy with `#print axioms`
   confirms that `Ideal.basis_of_stably_free` and the reused `Algebra.dimAt_openEmbedding`
   use only `propext`, `Classical.choice`, and `Quot.sound`. The main theorem and the new
   stable-comparison theorem additionally use `sorryAx`, exactly as expected from the
   reported open dependencies. The only direct `sorry` in the delivery is the entire named
   public stable-comparison theorem. No forbidden declaration, hollow definition, or arbitrary
   data chosen from an unproved existence statement is introduced. The equivalence is
   eliminated only within a theorem proof.

3. **Split statement — pass.** Read the split theorem and its full docstring argument
   against the last paragraph of Stacks 00SC and the equation of 00S6, checking all scalar
   rings and both free summand lengths. The hypotheses imply regularity of the equations
   at the pulled-back prime; exact localization and the existing presentation comparison
   then give precisely the asserted stable equivalence. It does not repeat the main item:
   dimension at q, cancellation, the bound, and a conormal basis remain genuine proved
   steps in the parent. Checked t=0, m=t, n=0, and the zero-quotient exclusion; an empty
   equation list gives the rank-zero conormal on that side, and an existing prime excludes
   a zero local ring. Fresh LeanFinder, Loogle, and grep queries with different terminology,
   plus searches of lean/Sheaf and lean/WeilConjectures, found no existing theorem with this
   assembled conclusion. Inspected `Ideal.tensorCotangentEquiv` (flat base change) and
   `Algebra.Generators.cotangentCompLocalizationAwayEquiv` (the special adjoined-variable
   presentation): neither directly supplies arbitrary-presentation comparison and the
   successive scalar/localization identifications. Closing this remaining glue is not a
   few-minute application of an existing lemma.

4. **Route and pruning — pass.** Read downward from the target: prime existence rules out
   the zero-ring branch; the existing open-embedding helper and equidimensionality provide
   local dimension; stable comparison feeds a split inclusion/projection, projectivity,
   finite generation, Mathlib local freeness, and finrank arithmetic. The inequalities
   m<=t+n and t<=m justify every natural subtraction. Public imports serve the unchanged
   statements; added proof imports are private, including `import all` used solely to reuse
   the existing private dimension helper. The split module keeps the imports needed by its
   documented proof plan. Checked `dag/units/sk-thm-p1.json`: neither this parent nor any
   replaced lower helper realizes a unit-level step, and all realized nodes remain unchanged.
   Expanded `No longer needed` to enumerate all eleven old parent proof dependencies
   absent from its new direct list and distinguish moved dependencies from pruned steps.

5. **DAG agreement — pass.** The parent steps match the implemented proof, including the
   private-helper reuse and Mathlib projectivity/finiteness/rank route. The new node matches
   the split statement and records its source, four complete proof steps, their dependency
   union, proof origin, three search kinds (including the explicitly unavailable service),
   split status, creator/item/group/date, blueprint ancestry, chapter/unit, and Lean record.
   It is a new node in its own new module; no unit realization changed.

Second reading changed only this report: made the direct dependency-removal accounting
exhaustive and added the independent checks above. No Lean proof or statement needed repair.
One upper hole is closed and one lower hole added: this remains a decomposition, with no
claim of an unconditional proof or positive net-hole progress.
