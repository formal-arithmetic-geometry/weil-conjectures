## What changed

Proved `AlgebraicGeometry.Scheme.noetherian_proper_directImage_bounded_coherent`
with its original signature and visibility. Only this Lean module and its node are changed.
The proof uses the truncation hypercohomology spectral sequence. Private proved helpers
establish proper coherent module images by integral-ideal devissage; local induction
transports coherence through the pages, and an existing helper handles finite filtrations. No new statement modules,
interface changes, definitions, or axioms are introduced.

Proper module coherence is implemented from the existing lower-level declarations because
importing its standard source module would make a cycle. Its affine devissage and local
finite-presentation arguments follow the existing proofs in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`.
The spectral-sequence assembly follows the existing proved `DirectImageBoundedCoherent`
argument, specialized here to a proper morphism without a support hypothesis.
The finite upper bound is a supremum over the source interval [a,b].

Proof-only imports added: `CoherentFiniteTypeLocallyNoetherian` (with `import all`
to reuse its proved local-generators helper), `CoherentKernelCokernelSum`,
`FinitePresentationIntegralFiltration`, `IntegralIdealProperCohomology`,
`CohomologyFiniteExtension`, `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`,
`Sheaf.CategoryTheory.TruncationHypercohomology`, and `Mathlib.Data.Int.Interval`.
The generic filtration and zero-page arguments are private fully proved helpers.

Sources read: [08E2](https://stacks.math.columbia.edu/tag/08E2),
[02O5](https://stacks.math.columbia.edu/tag/02O5), and
[01XJ](https://stacks.math.columbia.edu/tag/01XJ).
The scheme hypotheses give properness, locally Noetherian source, and compact target.
The upper-bound arithmetic uses q <= max(q,0), so negative source degrees are covered;
the empty interval gives supremum zero. Zero objects and empty schemes follow the same
filtration argument. No witness is used to define new data in the library.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.noetherian_proper_directImage_bounded_coherent`
(node `lem-pc-noetherian-proper-bounded-coherent-image`).
No `sorry` remains in the delivered module. No holes added or split off.
All three remaining private helpers and local inductions are proved.
The imported declarations may still depend on existing sorries; this is a proof from
existing statements, not a claim that the whole target closure is axiom-free.

## No longer needed

Removed from the node's proof dependencies:
`lem-pc-derived-direct-image-uniform-truncation-bound` /
`Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound`, and
`lem-pc-coherent-hi` /
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`.
Neither module is imported. Their required lower-level inputs are explicitly recorded
in the revised node. No shift or unbounded truncation-tail bound is needed.

`Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent`,
`Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage`, and
`Sheaf.AlgebraicGeometry.ProperSupportHigherDirectImageBound` are not needed by this proof;
all would cycle. Their nodes are not direct dependencies of the original item.
No closed-support construction is needed, since the morphism itself is proper.

The existing private filtration and zero-page helpers are reused through proof-only
`import all Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh` and
`import all Sheaf.CategoryTheory.HalfPlaneWeakConvergence`. Their principal theorems
are not invoked, and their modules are retained for these helpers.
The redundant original public import of `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` was removed in the second reading: `SchemeDerivedDirectImage` already publicly reaches it through `DerivedCategory`. All other original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The node's suggested `lem-pc-coherent-hi` declaration lives in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`, whose proof
imports already reach this item. `tools/import_direction.py may` refused that import.
The same issue affects the existing proper-support bounded-coherent theorem and its
proper-support coherence and vanishing input modules. The delivery avoids all these
cycles by using existing lower-level declarations and proving the glue locally.

The source local Stacks `.tex` files are absent on this machine; the cited official
Stacks pages were read online. The unit record `sk-thm-picard-coherence` has no realized
nodes; its proper-coherence and finite affine-cover route is retained.

A compile timeout was traced to implicit search for slice-site sheafification instances
in the coherent-to-finite-presentation helper. Explicit local families of `HasWeakSheafify`
and `WEqualsLocallyBijective`, with module universe u pinned, resolved it without changing
any definition or increasing a timeout or heartbeat limit.


## Earlier second reading (a previous round; superseded)

1. **Unchanged interface — pass.** Compared the delivered module with the repository
   version and programmatically compared the text from the existing theorem name to
   `:= by`: its signature is byte for byte unchanged. No public declaration or definition
   was added. The six new helpers are private proved theorems. Restored the original
   theorem docstring; the revised route remains documented in this report and the node.
2. **Proof — pass.** Read every
   helper and the main proof. The initial single-file compilation passed without warnings
   in 52.9 seconds. There are no sorries, axioms, unsafe/opaque declarations, externs,
   implementations, or data definitions in the delivered module. The choices of affine
   presentations, filtration witnesses, and vanishing bounds occur only inside theorem
   proofs, never in definitions. A separate scratch `#print axioms` compile timed out at
   the unchanged 60-second limit; the required delivery tool repeats compilation and
   checks every declaration's axioms with its standard probe.
3. **Split statements — pass (none).** No new hole or statement module was introduced.
   Checked the private finite-presentation construction from generators and coherent
   relations, integral-ideal devissage, affine localization, page subquotients, and finite
   filtration descent. The zero filtration case N=0 works by identifying top with bottom.
   In the upper-bound argument, q can be negative: q <= q.toNat suffices; an empty [a,b]
   has supremum zero and all coefficient modules vanish. No a<=b hypothesis is inserted.
4. **Shortest route and pruning — pass.** Read Stacks [08E2](https://stacks.math.columbia.edu/tag/08E2),
   [02O5](https://stacks.math.columbia.edu/tag/02O5), and [01XJ](https://stacks.math.columbia.edu/tag/01XJ).
   Checked the proper-coherence proof in `FiniteFreeComplex` and the existing bounded
   coherent proof in `DirectImageBoundedCoherent`; both import paths cycle back to this
   item. The local implementation uses their existing lower-level statements instead.
   Independent LeanFinder search for proper pushforward of bounded coherent derived
   complexes returned only generic t-structure results; rg found no shorter accessible
   public result. The analogous finite-presentation and page-zero helpers found elsewhere
   are private and their modules add unnecessary dependencies. Removed the redundant
   public `HomologySequence` import (already publicly available through
   `SchemeDerivedDirectImage` -> `DerivedCategory`); all added proof imports are private.
   Both removed old proof dependencies are listed in `No longer needed`. The unit
   `sk-thm-picard-coherence` has empty `realized` lists; proper coherence and finite
   affine-cover vanishing retain its route.
5. **DAG — pass.** The node changes only `proof`, `proof_deps`, and `proof_origin`.
   Verified that `proof_deps` equals the union of step uses and checked their Lean
   declarations. The affine sections comparison supplies the semilinear refinement used
   here in the same module; local vanishing supplies its compact-base corollary.
   The node accurately records devissage, coherent spectral pages, finite filtration
   descent, and the finite supremum bound. No new node is needed. The redundant public-import removal has change record `coord/changes/NoetherianProperBoundedCoherentImage-public-import.md`, including the transitive downstream inventory and the retained public path.

Second reading changed only the redundant import, restoration of the original docstring,
its public-import change record, and this report. Closed one original hole, added zero; no proof repair was necessary.

The first dry run completed the local compile and standard all-declaration axiom probe,
then required a public-import change record. Added that record; no downstream module
needs adaptation because the retained public import path exports the same module.

The repeated scratch `#print axioms` compilation passed in 46.1 seconds and printed
exactly `propext`, `sorryAx`, `Classical.choice`, and `Quot.sound` for the original theorem.
The existing imported holes account for `sorryAx`; there is no new hole in this delivery.

## Repair

The landing review identified two private helper declarations whose propositions duplicated
helpers in existing modules. To make their interfaces distinct while retaining the exact
proof use, both helpers now take an explicit unused `Unit` tag; all call sites pass `()`.
The target theorem signature and proof result are unchanged.


## Second reading by V2

1. **Interface: pass.** Compared the entire module and node with the repository.
Programmatic comparison confirms that the original theorem signature through `:= by`
is byte for byte unchanged. The original docstring is retained. No public declaration
or data definition was introduced. The only public-import removal has the existing
change record `coord/changes/NoetherianProperBoundedCoherentImage-public-import.md`;
verified its retained public path through SchemeDerivedDirectImage and DerivedCategory.
2. **Proof: pass subject to the final delivery checks below.** Read the local presentation,
integral-ideal devissage, affine restriction, spectral sequence, and vanishing arguments.
No sorry, forbidden declaration, or data definition occurs. Choices are proof-local.
The first compile exposed unused-tag warnings; the repaired compile passed without warnings.
The standard delivery probe checks all declarations' axioms. Imported existing holes
may contribute sorryAx, as already disclosed; none is added here.
3. **Split statements: none.** Closed the original
`AlgebraicGeometry.Scheme.noetherian_proper_directImage_bounded_coherent` hole;
added zero holes. The finite supremum handles negative q by q <= q.toNat and handles
a > b by coefficient vanishing everywhere. The finite-filtration induction handles N=0.
4. **Route and pruning: repaired.** Independent LeanFinder search for proper pushforward
of bounded coherent cohomology returned only general scheme results, not the desired
theorem. Repository searches identified duplicated private filtration and zero-page
helpers in accessible modules. Reused both using import all. The coherent-page source
module cycles, so its short induction is local to the target proof. Removed both dummy
Unit arguments rather than retaining the previous duplicate-check workaround. All added
imports are proof-only. Both old dependencies removed from proof_deps remain listed under
No longer needed. The unit sk-thm-picard-coherence has empty realized lists; its proper
coherence and compact-base vanishing route is retained.
5. **DAG: pass.** Checked all proof-dependency node declarations and the union of step uses.
Updated the steps and dependencies to record the two reused helper modules explicitly,
while explaining that their principal theorems are not used. No new node is needed.

Second reading changed: replaced duplicated filtration and page-zero helpers by existing
private helpers, moved the coherent-page induction into the target proof, removed the
unused Unit-tag workaround, and updated the DAG and report. The earlier Repair paragraph
records the rejected prior approach, not the final implementation.

Final dry run passed: `deliver3.py V2 Sheaf.AlgebraicGeometry.NoetherianProperBoundedCoherentImage --no-push`
printed OK at 33f95f2f58 after local compilation, the all-declaration axiom probe,
and preflight. Review class CODEX reflects the recorded public-import removal and repair.
