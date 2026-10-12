## What changed

Proved `AlgebraicGeometry.isUniversalFirstOrderThickening_spec` in
`Sheaf.AlgebraicGeometry.UniversalThickeningAffineCase`, with its original signature
and public imports unchanged. All proof-local helpers are private and fully proved.

The proof identifies maps into spectra with ring maps to global sections, transports
an affine test's surjective sections map through its quotient-by-kernel isomorphism,
and applies the given algebra universal property. Open pullbacks preserve square-zero
kernel ideals. Affine uniqueness implies uniqueness for arbitrary tests, which proves
overlap compatibility; Mathlib's morphism gluing supplies the global lift and the two
triangle identities. Surjectivity of the original algebra map supplies the closed
immersion, and the kernel computation proves its square-zero ideal sheaf.

Removed the redundant proof import `Sheaf.AlgebraicGeometry.Thickening`, already
publicly available through `UniversalFirstOrderThickening`. Updated the existing node's
proof and proof dependencies to describe the pullback implementation and pruning.
No definitions, theorem signatures, or other modules were changed.

Validation: the complete module compiled without warnings through `lcompile.py`.
`#print axioms AlgebraicGeometry.isUniversalFirstOrderThickening_spec` reports only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry` remains in the delivered file.
The proof imposes no nontriviality or nonemptiness assumptions; empty affine tests,
zero rings, and empty overlap covers are handled by the same sections and cover APIs.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isUniversalFirstOrderThickening_spec`
(node `lem-weil-pbc-universal-thickening-affine-case`).

No holes added, no statements split off, and no `sorry` left in this module.
The proof uses Mathlib's proved results and the existing concrete thickening definitions;
it does not rely on any project's unproved theorem.

## No longer needed

Removed direct import: `Sheaf.AlgebraicGeometry.Thickening` (still available transitively
because the public universal-thickening statement uses its definition).

Removed proof dependencies:
- `lem-weil-pbc-morphism-factors-through-open-subscheme`: restriction is implemented
  by pullback; the maps between restricted tests use the pullback universal property.
- `def-weil-scheme-over-base`: the theorem and proof use the explicit structure maps
  and commuting triangles, without a bundled scheme-over-base structure.

These two nodes are no longer needed by this proof. No claim is made that they are
unreachable from other targets. All other existing proof dependencies remain needed:
sections/spectra, closed immersions, square-zero ideal sheaves, restriction to opens,
affine covers, morphism gluing, and the concrete universal-thickening predicate.
No additional dependency modules were imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original six-step plan can be implemented entirely
with proved Mathlib APIs. Proving arbitrary-test uniqueness before gluing avoids a
second explicit affine cover of each overlap. The existing node is below the unit's
realized statement and proof steps; its unit route is unchanged.

Searches: Lean Finder returned `Scheme.Hom.liftQuotient` and formal-unramified APIs,
which do not directly state this result. Loogle returned the kernel and morphism-gluing
APIs used in the proof. Source searches found `IsClosedImmersion.spec_of_surjective`,
`Scheme.Hom.app_surjective`, and the ideal-sheaf open-pullback kernel formula.
LeanSearch was unavailable with an internal server error; this did not block the proof.
The cited Stacks 04F3 affine-case and gluing paragraph was read at
https://stacks.math.columbia.edu/tag/04F3 because this read-only clone lacks the fetched
literature files listed in `literature/LIST.md`.


## Second reading by U1

1. **Visible interface — pass.** Read the whole delivered module and its diff against
   the repository. The signature of `isUniversalFirstOrderThickening_spec`, from
   `theorem` through its result type, is byte-for-byte unchanged. In particular,
   `hφ`, surjectivity `hπ`, square-zero kernel `hK`, and the universally quantified
   algebra lifting hypothesis have not changed. The conclusion still includes the
   first-order thickening, the base triangle, and unique lifts for arbitrary schemes.
   The only added declarations are private, proved helpers; no existing definition
   changed, no change record is needed, and no other module is delivered. Read the
   affine-case paragraph of Stacks Tag [04F3](https://stacks.math.columbia.edu/tag/04F3),
   label `lemma-universal-thickening`: its algebra-to-scheme translation and gluing
   route agree with this conditional statement. Formal unramifiedness is used in
   that source to obtain the algebra extension, which is already a hypothesis here.

2. **Proof and axioms — pass.** Independently compiled the delivered file through
   `lcompile.py`: no errors or warnings (3.7 seconds). Compiled a scratch copy with
   `#print axioms` for the public theorem and all nine private declarations: every
   result lists only `propext`, `Classical.choice`, and `Quot.sound`. Scanned the file
   for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and `sorryAx`:
   none occurs. `specRingHom` is the explicit composite of the canonical spectrum
   sections isomorphism and `appTop`; it chooses no unproved existence witness.
   The chosen local lifts and affine ring lifts come from the supplied universal
   property, whose uniqueness determines them. Kernel transport uses injectivity
   of actual sections isomorphisms. No project theorem carrying a hole is needed.

3. **Split statements and small cases — pass.** No new public statement, new node,
   or split-off hole exists. Read each private helper: source and target naturality
   use the spectrum adjunction; the open-pullback helper has the required open
   immersion assumption; arbitrary-test uniqueness only restricts to affine cover
   members, and does not assume their overlaps are affine. In the affine helper,
   `j.app_surjective` applies because `T'` is affine and `j` is a closed immersion.
   The quotient is precisely by `ker j.appTop`, with square zero deduced by
   evaluating `hj.2` on the top affine open. `β.toAlgebra` and `hφ` ensure that the
   quotient map and the translated map really are maps of `R`-algebras. Empty tests,
   the zero ring, zero kernel, and empty overlaps require no extra hypothesis: the
   adjunction, quotient equivalence, and cover extensionality all apply unchanged.

4. **Route, search, and pruning — pass.** Searched `lean/Sheaf`,
   `lean/WeilConjectures`, and upstream `WeilConjectures` for universal thickenings
   and affine lifting; there is no existing proved replacement for this theorem.
   Read Mathlib's spectrum adjunction lemmas, `Scheme.Hom.app_surjective`,
   `Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`, and morphism gluing APIs.
   The proof already uses these proved results directly. The two public imports
   are statement dependencies: the universal-thickening predicate and
   `Ideal.Quotient.mkₐ` (defined in `Ideal.Quotient.Operations`). The removed direct
   plain import of `Thickening` is redundant through the first public import.
   Compared old and new `proof_deps`: precisely the two removals in
   `## No longer needed` are reported. Read `dag/units/sk-thm-p1.json`, including
   `realized`: this auxiliary node realizes none of the fixed unit steps, and its
   affine-to-global route preserves the source argument below those steps.

5. **DAG agreement — pass after repair.** Compared the complete node JSON.
   Only `proof`, `proof_deps`, and `proof_origin` change; `lean.statement`, the
   mathematical statement, and the unit remain unchanged. The six steps match
   the Lean: spectrum dictionary; closed immersion and square-zero ideal;
   quotient-kernel affine lifting; open pullbacks; arbitrary-test uniqueness and
   compatible gluing; assembly of the predicate. The union of their `uses` equals
   `proof_deps`. Found two stale textual citations to `def-weil-scheme-over-base`
   in steps 2 and 3 after that dependency had been removed from `uses`.
   Removed those citations: the proof uses explicit commuting triangles, as
   already explained in the pruning report. No extra node or dependency is needed.

**Second reading changed:** removed those two stale DAG proof-text citations and
added this review. No Lean repair was necessary. Independently verified the net
local change: one original hole closed, zero holes added, zero split-off statements.
