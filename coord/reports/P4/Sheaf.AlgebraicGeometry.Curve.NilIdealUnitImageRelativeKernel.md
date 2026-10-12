## What changed

Repaired the returned delivery by removing all three duplicate private lemmas:
`AlgebraicGeometry.Scheme.isUnit_of_surjective_appTop`,
`AlgebraicGeometry.Scheme.surjective_units_appTop`, and
`AlgebraicGeometry.Scheme.locallySurjective_gmSheafToLowerStar_of_thickening`.
Added the proof-only `import all Sheaf.AlgebraicGeometry.Curve.ReductionUnitsEpi`
and reused its existing general thickening helper in
`epi_gmSheafToLowerStar_nilIdeal`. The other two lemmas are dependencies of that
existing helper. No declaration in ReductionUnitsEpi was changed.

The item's theorem, signature and public imports are unchanged. The remaining
three private helpers prove nil-ideal epimorphy, compatibility with pushforward
composition, and the abelian kernel/image comparison. Updated the DAG proof and
proof dependencies to record the reused helper and its owning node.
No statement, definition, target, or module held by another group was changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.nonempty_nilIdealUnitImageRelativeKernelIso`
(node `lem-sc-nil-ideal-unit-image-relative-kernel`). All remaining private
helpers are proved. No sorry remains and no hole was added or split off.
This is a proof, not a decomposition.

Single-file compilation through `lcompile.py` succeeds without warnings.
The delivery dry run also checks the theorem's axioms.
The argument handles the empty scheme and I=J, I=0, and J=0. It needs only J to
be nil, as follows from the unchanged hypotheses. The unit's statement and
steps are untouched (`sk-prop-h2.realized` contains no realization by this node).

## No longer needed

Removed original direct proof imports:
- `WeilConjectures.CategoryTheory.Sites.Torsor`: torsors are not used; Gm comes
  from the existing public import `WeilConjectures.AlgebraicGeometry.Sites.Gm`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: already publicly
  imported by Gm; its pushforward definitions and preservation lemmas remain used.

Removed the returned delivery's direct proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`: its unit-detection lemmas
are used inside the existing imported helper, not directly here.
Removed the three duplicate local helper proofs listed above.
All five original proof-dependency nodes remain used; added
`lem-sc-reduction-units-epi` for its module's general thickening helper.
No node or module is claimed to leave the targets' transitive closure.
The new import reaches the reduction and topological-invariance modules;
the repaired delivery makes no claim to prune those modules.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery copied three already proved private statements from
ReductionUnitsEpi. The landing check correctly refused those duplicates.
Although its public theorem concerns reduction, its private thickening helper
already has exactly the required general statement. A proof-only `import all`
makes that helper available without changing any existing declaration or
visibility. This repair removes all three copies and uses that existing proof.

The remaining argument is unchanged: full support gives epimorphy of p;
pullback pasting identifies its composite with q_I; the induced kernel map is
a pullback of p and hence epi; image uniqueness and preservation of kernels
give the requested isomorphism. No new node or unsourced hole was introduced.
The previous second reading predates this repair and has been removed so the
independent reader can review the repaired delivery.


## Second reading by P4

1. **Interface — PASS.** Compared the sole delivered module against the repository
   with `diff -u` and checked the entire existing theorem signature byte for byte.
   The hypotheses X, J ≤ I and I ≤ X.nilradical, the categorical image, and the
   pushed-forward relative kernel are unchanged. Both public imports remain
   identical. There is no changed definition, statement or visibility, and no
   change record or forced adaptation is needed.
2. **Proof and trust — PASS.** Compiled the delivered module locally through
   `lcompile.py`, without errors or warnings. Compiled a scratch copy with
   `#print axioms` for the public theorem and all three private helpers: every
   result uses only propext, Classical.choice and Quot.sound. No sorry remains,
   no forbidden trust mechanism occurs, and no definition or arbitrary witness
   was introduced. Read the reused thickening helper in ReductionUnitsEpi: it
   lifts units on the affine cover after base change, using surjectivity on
   points to detect units. Read the composition calculation and the constructed
   kernel pullback universal property; the final image isomorphism has the
   correct orientation, followed by inverse kernel preservation.
3. **Split statements and reuse — PASS.** No statement is split off and no hole
   is added. Searched Gm and the curve modules, and Mathlib's abelian and kernel
   files, for composition, kernel/image and kernel/pullback results; additionally
   ran msearch grep with `kernel.*pullback|pullback.*kernel`. The results supply
   generic infrastructure, not a duplicate of the three remaining helpers.
   The previously duplicated unit-lifting and thickening lemmas are absent and
   their existing proof is reused by the proof-only `import all`. For I=J the
   relative restriction is an identity and both sides vanish; I=0 forces J=0;
   for J=0 the kernel/image comparison reduces to the kernel itself. The empty
   scheme and zero rings cause no exception. No square-zero or reducedness
   hypothesis is used. The categorical helper requires only p epi, as stated.
4. **Route and pruning — PASS.** The proof first reuses the fully proved
   thickening helper and Mathlib's pullback stability of epis and image
   uniqueness; it does not hide the target in an equivalent open lemma.
   The two public imports support the signature, and the sole private import
   supplies the general thickening helper. The report names both removed old
   proof imports. All five old proof-dependency nodes still supply definitions
   or kernel preservation; none is falsely claimed pruned. Read sk-prop-h2's
   statement, step and realized record: this node realizes no unit step, and
   the Kummer/Brauer route is unchanged.
5. **DAG — PASS.** Compared the node JSON with the repository: only proof,
   proof_deps and proof_origin differ. The statement and Lean record stay
   unchanged. Verified that proof_deps is exactly the union of the three steps'
   uses. Those steps record nil support and reused thickening epimorphy,
   pullback pasting, then the kernel pullback/image comparison and preservation
   of kernels. The added ReductionUnitsEpi dependency explicitly records use
   of its general private helper, not its reduction-specific public conclusion.
   There are no new nodes to validate. The cited blueprint source file is not
   installed on this machine; the unchanged node statement and the actual
   proof and dependency modules were read directly.

Second reading changed only this report: added the independent checks and
verdicts. No repair to the Lean proof or node was necessary. Closed one original
hole, added zero holes, split off zero statements; no transitive module pruning
is claimed.
