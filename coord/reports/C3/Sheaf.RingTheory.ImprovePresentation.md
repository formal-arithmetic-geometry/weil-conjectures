## What changed

Completed both proofs in `Sheaf.RingTheory.ImprovePresentation`, preserving every existing
signature, universe and visibility. The specified-presentation theorem is placed before
its existential corollary so the latter can apply it. The algebra is constructed as the
symmetric algebra of the presentation's conormal module, and the retraction is the explicit
`SymmetricAlgebra.lift 0`; no object is chosen from an unproved existence theorem.

Added two fully proved support modules, each with one public theorem and a DAG node:
`Sheaf.RingTheory.PresentationLocalizedConormalSplit` and
`Sheaf.RingTheory.LocalizedSymmetricDifferentialsSplit`. They assemble steps 3 and 5 of the
original plan from existing declarations and Mathlib. Updated the parent node's proof,
proof dependencies and proof origin to match the implementation.

The first helper uses the principal-localization naive-cotangent theorem to transfer
injectivity and cokernels, then Mathlib's projective splitting and polynomial differential
basis. The second uses symmetric-algebra base change and smoothness, the localization
pushout's Kähler base-change equivalence, and Mathlib's Jacobi–Zariski exactness. Freeness
in the parent follows by base-changing the free conormal-plus-differential product.

All three modules compile together using `lcompile.py --all`. The declaration comparison
reports no changed signatures and no interface changes in the existing module. No modules
held by another worker were adapted. The unit `sk-thm-p1` and its realized statements and
proof steps are preserved.

## Proved and sorry left

Closed the two original holes, both attached to `lem-weil-pbc-improve-presentation`:

- `Algebra.Presentation.symmetricAlgebra_improves`.
- `Algebra.exists_finiteType_retract_smooth_free_differentials`.

Also proved both new helper declarations completely:

- `Algebra.Presentation.localized_conormal_equiv`, node
  `lem-weil-pbc-presentation-localized-conormal-split`.
- `SymmetricAlgebra.localized_differentials_equiv`, node
  `lem-weil-pbc-localized-symmetric-differentials-split`.

No `sorry` remains in any delivered module. Holes added: zero. No theorem was merely moved
to another name, and neither helper is a restatement of the parent. The proofs still use
existing project declarations with their existing holes, notably
`Algebra.Generators.principal_localization_naive_cotangent`,
`SymmetricAlgebra.generators_and_finitePresentation`, and
`AlgebraicGeometry.cotangentComplex_symmetricAlgebra`. Those dependencies remain future
stage-3 work; this delivery does not claim the complete target closure is axiom-free.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.RingTheory.JacobiZariskiHomologySequence`:
  `lem-weil-pbc-jacobi-zariski-homology-sequence` is not needed anywhere in this proof.
  Mathlib's `Algebra.H1Cotangent.exact_δ_mapBaseChange` supplies the required injectivity,
  and `KaehlerDifferential.exact_mapBaseChange_map` supplies the differential tail.
- `Sheaf.RingTheory.JacobiZariskiQuotientSmooth`:
  `lem-weil-pbc-jacobi-zariski-quotient-smooth` is not needed anywhere in this proof.
  Mathlib's `Algebra.Extension.cotangentComplex_injective_iff` replaces its use.
- `Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent`: its declaration and node
  remain needed through `PresentationLocalizedConormalSplit`; this is a removed direct
  import, not a claim that its module can be discarded.
- `Sheaf.AlgebraicGeometry.CotangentComplexSymmetricAlgebra`: its declaration and node
  remain needed through `LocalizedSymmetricDifferentialsSplit`; this likewise only moves
  the dependency into the helper that uses it.

For completeness, the old parent `proof_deps` also removed
`def-weil-pbc-smooth-ring-map`, `lem-weil-pbc-polynomial-ring-smooth`, and
`lem-weil-pbc-polynomial-ring-kahler-basis` as direct edges. They remain used in
`PresentationLocalizedConormalSplit`; the smooth definition also occurs in the second
helper. Together with the four dependencies discussed above, these are all seven old
parent edges absent from the new parent list. Only the two Jacobi–Zariski nodes are
mathematically bypassed; the other five moved into the helpers.

Second reading also removed the redundant proof import
`Mathlib.RingTheory.Finiteness.Cardinality` from
`LocalizedSymmetricDifferentialsSplit`: the required finite-module generator theorem is
already available through its other imports, and the module compiled without this import.

A source import-closure comparison of the original item and the delivered overlay finds
exactly these seven project modules removed from this item's closure (other target routes
may still reach them):

- `Sheaf.Algebra.Homology.FreeResolutionSesSplit`, node
  `lem-weil-pbc-free-resolution-ses-split`.
- `Sheaf.Algebra.TorDimensionShiftFree`, node `lem-weil-pbc-tor-dimension-shift-free`.
- `Sheaf.Paper.TorLongExactFirstVariable`, node `lem-weil-pbc-tor-long-exact-first-variable`.
- `Sheaf.RingTheory.JacobiZariskiHomologySequence`, node
  `lem-weil-pbc-jacobi-zariski-homology-sequence`.
- `Sheaf.RingTheory.JacobiZariskiLeftTermVanishing`, node
  `lem-weil-pbc-jacobi-zariski-left-term-vanishing`.
- `Sheaf.RingTheory.JacobiZariskiQuotientSmooth`, node
  `lem-weil-pbc-jacobi-zariski-quotient-smooth`.
- `Sheaf.RingTheory.TwoTermKernelBaseChange`, node
  `lem-weil-pbc-two-term-complex-kernel-base-change`.

The parent proof retains the finite
presentation, symmetric universal property, symmetric finite generation, tensor
localization, symmetric base change, finite-projective symmetric smoothness and smooth
composition nodes. The polynomial smoothness and differential-basis steps remain in the
first helper, and the symmetric cotangent step remains in the second. No blueprint unit
statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature defect was found. The original plan overestimated the
needed Jacobi–Zariski machinery: the full homology sequence and the quotient-smooth
statement can be replaced by the already proved Mathlib facts named above. The existing
`SmoothLocalizationConormalSplit` statement concerns an explicit polynomial quotient in
one universe, whereas this item requires the conormal module of a supplied presentation
with independent ring universes. The new proved first helper provides precisely that
interface without changing another worker's module.

Checked the source against Stacks Tags 07CE and 031K. The source files cited by the DAG
are absent from this local clone, so their authoritative Stacks pages were read directly.
LeanSearch returned an internal-server error for both new statements; those attempts are
recorded as unavailable, with no mathematical verdict. LeanFinder, Loogle and source grep
succeeded, and their component results were used.

The new statements were checked for zero localizations, the zero module, and zero
polynomial variables or relations. They require no nontriviality or positivity assumption;
all tensor, quotient, exact-sequence and projective-splitting operations used remain valid
in these cases.

## New nodes

`lem-weil-pbc-presentation-localized-conormal-split` records
`Algebra.Presentation.localized_conormal_equiv` in
`lean/Sheaf/RingTheory/PresentationLocalizedConormalSplit.lean`. It is the localized
conormal-complement step of Stacks 07CE, proved from the existing principal-localization
statement and Mathlib. Its proof is complete; it creates no new hole.

`lem-weil-pbc-localized-symmetric-differentials-split` records
`SymmetricAlgebra.localized_differentials_equiv` in
`lean/Sheaf/RingTheory/LocalizedSymmetricDifferentialsSplit.lean`. It is the differential
splitting step of Stacks 07CE, with the split-exact argument of Tag 031K. Its proof is
complete; it creates no new hole. No change record is needed: the existing module's
signatures, visibility, public imports and commands are unchanged.

## Second reading by C3

1. **Unchanged interface — PASS.** Read the complete repository-to-sandbox diff.
   Both original theorem signatures, including whitespace, universes, hypotheses, composite
   algebra structures and conclusions, are byte-identical. Declaration order changes only
   to let the existential theorem apply the specified-presentation theorem. Public imports
   and visibility of the existing module are unchanged. No definitions or target statements
   changed; no change record or forced adaptation is needed.
2. **Proof and axioms — PASS.** Independently compiled all three modules in import order
   through `lcompile.py --all`, with no errors or warnings. Scanned all delivered Lean for
   forbidden constructs and holes: none. Compiled scratch copies with `#print axioms` for
   all four public declarations; each uses only `propext`, `Classical.choice`, `Quot.sound`
   and the transitive `sorryAx` of the existing imported open theorems. The symmetric algebra
   and zero-map retraction are explicit constructions. The choices of a finite presentation,
   finite generators, and splitting equivalences occur only in proofs; no arbitrary witness
   of an unproved existence statement defines delivered data.
3. **New statements — PASS.** Both helpers are proved, strictly intermediate steps, with
   complete source and proof docstrings and matching new nodes; no statements are split off
   with holes. Read the exact-sequence maps, scalar towers, projectivity transport and tensor
   cancellation. The conormal helper splits the localized polynomial cotangent sequence;
   the differential helper splits Jacobi–Zariski after relative smoothness kills H1.
   Zero localization, zero module, and zero variables require no nontriviality assumption.
   Repeated LeanFinder searches with different wording and searched project and Mathlib
   sources; no replacement with the same interface was found. Read the nearby
   `smooth_localization_conormal_split` and `symmetric_stabilization_differentials`:
   the former has a quotient-specific, single-universe interface and is still open; the
   latter treats reduced differentials over a different base and is also still open.
4. **Route and pruning — PASS after report repair.** The proof follows the construction,
   localized conormal complement, symmetric base change, smooth composition, and differential
   splitting. The two unused Jacobi–Zariski project lemmas are replaced by proved Mathlib
   facts. Checked `dag/units/sk-thm-p1.json`: neither this item nor its two helpers replaces
   any realized unit statement or step, and the unit route remains intact. Public imports
   supply signature notions; new project imports are proof-only. Removed one redundant
   Mathlib proof import after a successful omission compile. Completed the report's list of
   every old parent dependency omitted from its new direct list, distinguishing moved edges
   from genuinely bypassed nodes.
5. **DAG agreement — PASS.** Compared the old and delivered parent JSON: only `proof`,
   `proof_deps`, and `proof_origin` differ. Read all three delivered nodes against the Lean.
   Their steps describe the actual construction and equivalences; `proof_deps` is the union
   of their step uses. New nodes include sources, search records, creation identity,
   blueprint provenance, chapter/unit, and verbatim Lean statements. Existing Mathlib-backed
   node dependencies name the corresponding proved Mathlib facts used in the code.

Second reading changed only the redundant
`Mathlib.RingTheory.Finiteness.Cardinality` import and this report (complete removed-edge
accounting and independent review). No proof or statement repair was necessary. The item
closes two of two original holes and adds zero holes; its two new helper theorems are fully
proved relative to existing open dependencies.
