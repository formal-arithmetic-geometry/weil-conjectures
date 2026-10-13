## What changed

Proved `CategoryTheory.BigradedExactCouple.finitePage_image_quotient` from an intrinsic
finite-cycle kernel presentation and a normalized colimit kernel calculation. The
comparison isomorphism is constructed by `Abelian.epiDesc` in both directions;
epimorphism cancellation proves the inverse identities and the prescribed equation.
All existing signatures and public imports are unchanged.

Added `Sheaf.CategoryTheory.NormalizedGradedFiniteKernel`, fully proved. Its proof
establishes the quotient kernel by factorization tests, invertibility of left-half-plane
cocone maps using the existing alpha isomorphism theorem, the iterated cocone equations with transports, and cancellation
of the final cocone isomorphism in the subobject pullback.

Added `Sheaf.CategoryTheory.FiniteCycleKernelPresentation` to isolate the remaining
finite-derived-image and original-g projection induction, independently of every
half-plane and colimit assumption. This module retains the proof-only import of
`DerivedCoupleExact`, used by its pending proof plan.

Validation: compiled the three modules together through `lcompile.py`. Edge cases:
at r=0 the intrinsic formula reduces to the kernel of initialG, namely the incoming
alpha image; for negative p the normalized formula uses invertible cocone maps and
still applies. No data is chosen from an unproved existence theorem in any definition.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.BigradedExactCouple.finitePage_image_quotient`
(node `lem-sp-finite-page-image-quotient`). No sorry remains in the item module.

Added and completely proved
`CategoryTheory.BigradedExactCouple.normalizedGraded_finite_kernel`
(node `lem-sp-normalized-graded-finite-kernel`), including all private helpers.

One new hole remains:
`CategoryTheory.BigradedExactCouple.finiteCycle_kernel_presentation`
(node `lem-sp-finite-cycle-kernel-presentation`). This is a decomposition, not a
complete proof without sorry dependencies: one upper hole closed, one lower hole
added. The remaining statement is strictly the intrinsic finite-page argument: it
has no A, normalized cocone, half-plane condition, graded piece, or comparison iso.

## No longer needed

Removed direct proof imports `Sheaf.CategoryTheory.ExactCouple` and
`Sheaf.CategoryTheory.Filtration` from the item: its unchanged public import of
`ExactCoupleConvergence` already exposes both. Moved the direct proof import
`Sheaf.CategoryTheory.DerivedCoupleExact` to `FiniteCycleKernelPresentation`.
The duplicate `alpha_iso_nonpositive` proof is removed; the existing
`HalfPlaneDiagonalColimits.alpha_iso_left` supplies that step.
The old direct proof dependencies `def-sp-exact-couple`, `def-sp-filtration` and
`lem-sp-derived-couple-exact` leave the parent node's direct `proof_deps`: the first
two remain through the normalized kernel node, and the third through the intrinsic
finite-cycle node. `def-sp-convergence` remains a direct dependency.
No original dependency node is pruned from the full delivery closure; the derived
image theorem remains needed by the remaining intrinsic proof. No unit statement
or realized unit proof step is bypassed. Neither `FinitePageImageLift` nor
`FinitePageGradedQuotient` is imported: their nonnegative-index/boundedness
hypotheses and absence of the original-g projection equation do not fit this item.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing refusal: removed the duplicate private theorem
`alpha_iso_nonpositive` from `NormalizedGradedFiniteKernel`. Its call now uses
`alpha_iso_left` from `Sheaf.CategoryTheory.HalfPlaneDiagonalColimits`, imported
with `import all` because that existing theorem is private. The matching node now
records `lem-sp-half-plane-diagonal-colimits` as a proof dependency. No existing
module or declaration visibility was changed.

No statement error found. The listed dependency declarations provide the exact
couple structures, derived-image recurrences and tower equations, but not the
finite intrinsic kernel comparison itself. That induction is explicitly isolated
as the remaining node. The current unit record has no realized node for this
spectral-sequence statement, so this reduction does not remove a unit realization.

## New nodes

`lem-sp-finite-cycle-kernel-presentation` records the remaining epimorphism and
intrinsic alpha-pullback kernel of the finite-cycle projection. The proof in words
spells out the image epimorphism induction, projection compatibility and exactness.
Its module has one public statement with proof exactly `by sorry`.

`lem-sp-normalized-graded-finite-kernel` records the completely proved normalized
colimit calculation, with no finite-cycle or next-D vanishing hypotheses. Each
node inherits the original chapter, unit and source; the parent node records the
actual proof route. No change record is needed; no interface was changed.


## Second reading by Y3

1. **Interfaces: pass.** Compared the item with the repository by `diff`; its only
   changes are private proof imports and the former sorry body. The existing
   theorem signature is byte-identical, and the public import, visibility,
   definitions and docstring are unchanged. The other two modules are new.
   No definition or statement change record is required.
2. **Proofs and axioms: pass as a decomposition.** Compiled all three delivered
   modules together with `lcompile.py`; no errors or warnings. Scratch copies
   with `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound` for
   `normalizedGraded_finite_kernel`. The item and
   `finiteCycle_kernel_presentation` additionally use `sorryAx`, as reported.
   Scanned every delivered Lean file: the sole sorry is the named intrinsic
   theorem, with its sourced proof docstring and matching node. No forbidden
   declaration mechanism or hollow definition occurs. The comparison iso is
   explicitly built by two `epiDesc` maps; epi cancellation proves both inverse
   identities and `comp_epiDesc` proves the prescribed equation.
3. **Remaining statement: pass.** Read the derived-image recurrences, exactness
   identities and tower projection recurrences. At r=0, the finite cycle map is
   initialG, the incoming iterate is the single incoming alpha, and the formula
   is exactness at D; hnext makes initialG epic. At r=1, the image epimorphism
   onto derived D followed by derived g agrees with original g into cycles
   modulo boundaries by `DerivedMaps.g_comm` and `projection_succ`; its kernel
   is the pullback of the double alpha image. Zero D/E objects and negative
   p cause no exception. The general induction in the docstring is the same
   finite argument and uses no half-plane or colimit data. It is strictly part
   of the original proof, not its restatement. Fresh Lean Finder, Loogle and
   Mathlib grep searches, plus searches across both library roots, found no
   replacement. The finite-page lift and quotient declarations require other
   bounds and do not supply the original-g/tower-projection equation. Closing
   this induction is substantial work, beyond a brief repair.
4. **Route and pruning: pass.** The normalized kernel calculation is proved
   independently, reusing the existing private `alpha_iso_left` through a
   proof-only `import all`, with no repeated alpha isomorphism proof. Checked
   the quotient-kernel factorization tests, iterate cocone identities and
   cancellation of the invertible cocone map. Imports support statements or
   actual proofs; `DerivedCoupleExact` supplies the pending intrinsic induction.
   The unit's `realized` arrays are empty, so no realized unit statement or
   step is bypassed. All old parent proof dependencies are now explicitly
   accounted for under No longer needed; none is pruned from the delivery's
   full import closure. One hole closed and one added means net zero holes,
   not a completed proof without sorry dependencies.
5. **Nodes: pass.** Checked each Lean statement against its node's verbatim
   `lean.statement`, and each `proof_deps` against the union of step `uses`.
   The parent records the two kernel calculations and the epiDesc comparison;
   the new nodes record respectively the remaining finite induction and the
   proved normalized calculation, including its reused half-plane helper.
   Both new nodes have source, proof origin, three search records, created,
   blueprint, chapter/unit and Lean records as required.

Second reading changed only the report: made the disposition of every old
proof dependency explicit and added this independent review. No Lean repair
was needed. Scratch axiom probes were removed before delivery.
