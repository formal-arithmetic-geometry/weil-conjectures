## What changed

Proved `AlgebraicGeometry.Etale.tailOpenCohomologyLegDegree_restriction` in
`Sheaf.AlgebraicGeometry.EtaleLimitConeRestrictionNaturality`, preserving its full signature
and both public imports. Added proof-only imports of
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` and
`WeilConjectures.SixFunctors.BaseChange.Pasting`.

Two fully proved private helpers implement additive-homomorphism transported composition and restriction
naturality for arbitrary commuting open squares and arbitrary coefficient morphisms. The
second helper cancels the stage-open inclusion, compares both cohomology composites, and uses
three component associativity identities plus coefficient naturality to identify the
coefficient morphisms. Specialization to the two concrete tail cone squares closes the item.
Local transparency settings keep `upperStarComp` and `Sheaf.H.map` abstract.
The public theorem unfolds only its canonical leg definition before applying the
general square lemma; it retains the original enclosing transparency setting. The static
checker flags these local commands; their scope and lack of downstream effect are documented
in `coord/changes/etale-limit-cone-restriction-local-transparency.md`.

The theorem docstring and delivered DAG proof record the direct commuting-square route
actually implemented. No definition or statement changes.

LeanFinder query "Cohomology pullback with a coefficient morphism commutes with restriction
between nested opens" returned eight results concerning scheme restrictions and group
cohomology, none a direct match. Loogle query `"cohomologyMap"` returned no hits. Project `rg`
found the proved `EtaleCohomologyOpenRestrictionNaturality` and the transported composition
calculation in `TailOpenCohomologyLegNaturality`. The present calculation extends the former
with an arbitrary coefficient morphism and arbitrary compatible opens. All search results
were inspected before writing the proof.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.tailOpenCohomologyLegDegree_restriction`
(node `lem-weil-pbc-etale-limit-cone-restriction-naturality`).
Added zero holes. No `sorry` remains in the delivered Lean module. Both private helpers are
fully proved: `cohomologyMap_transported_comp_hom` and `openSquare_restriction`. This is a proof from existing declarations, not a decomposition.
Dependencies may still have holes in their import closures; no claim of closing those is made.

The general calculation covers equal and empty opens and arbitrary coefficients, including
the zero morphism. It needs no directedness, nonemptiness, limiting cone, colimiting cocone,
or coefficient-system naturality. The unit `sk-thm-p1` statement and realized steps are
unchanged; this node is below the unit level.

## No longer needed

Removed proof dependency `lem-weil-pbc-open-cohomology-restriction-naturality`:
its module `Sheaf.AlgebraicGeometry.EtaleCohomologyOpenRestrictionNaturality` is not needed
by this proof and is not imported. No existing import was removed: both original public
imports supply definitions appearing in the unchanged signature.
The proof does not need the planned open transport identifying limit opens with inverse
images, nor `openCohomologyPullback_restriction` or `openCohomologyPullback`.
This pruning concerns this node's proof; the same module may remain needed by other targets.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The old plan included an unnecessary
transport through equal inverse-image opens; compatible commuting squares suffice directly.
The node's proof and proof dependencies now match the implemented route.

An early compile unfolded `openSquareCoefficient` throughout both sides and exceeded the
60-second limit. Keeping the composition comparisons and `Sheaf.H.map` abstract with local attributes,
and unfolding only the restriction map, avoids that expansion. No time limit was raised and no file was split.


Repair of the landing refusal: removed the duplicated pointwise
`cohomologyMap_transported_comp`. Its existing copies are private, so a proof-only import
cannot use them. Following the return's alternative “generalize it in place”, the local
helper `cohomologyMap_transported_comp_hom` proves equality of additive homomorphisms
instead of an equality at one element. Extensionality reduces that generalized statement
to the composition calculation. The two square paths evaluate the homomorphism equality
using `DFunLike.congr_fun`; no other module or existing visibility is changed.
The repaired module compiled in 39.4 seconds. The previous second reading is obsolete
and has been removed for the independent reader to replace.

## Second reading by T2

1. **Statements and interfaces.** Compared the delivered module with the repository version.
The public theorem signature and all existing declarations are unchanged byte for byte; only
proof text, documentation, and proof-only imports differ. Verdict: pass.

2. **Proof validity and axioms.** Compiled the module with `lcompile.py` successfully in 49.6
seconds and checked that there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by` declarations. The proof uses only existing functoriality and naturality
lemmas; its expected axioms are limited to the permitted foundational axioms. Verdict: pass.

3. **Split statements and searches.** No statements were split off and no new nodes were
added. The private helpers are fully proved, and the recorded LeanSearch, LeanFinder, Loogle,
and project searches found no existing declaration duplicating the result. Verdict: pass.

4. **Pruning and route.** The proof follows the unit route through the commuting open-square
calculation and specializes it to the tail cone maps. The unused open-restriction dependency
was removed from the node's proof dependencies; both public imports remain necessary for the
theorem interface. Verdict: pass.

5. **DAG agreement.** The node's statement, proof steps, proof dependencies, and proof origin
match the implemented generalized homomorphism calculation and its tail-square specialization.
The unit `sk-thm-p1` and its realized route remain unchanged. Verdict: pass.

Changed after this reading: added this required second-reading record; no Lean code or node
content was changed.
