## What changed

Proved `AlgebraicGeometry.Scheme.ideal_power_local_maps_eventually_agree` in
`Sheaf.AlgebraicGeometry.IdealPowerLocalMapsEventuallyAgree`, without changing its
signature, visibility, original public imports, or existing docstrings.

Restrict the two maps to their overlap and subtract. Proved private local helpers
for naturality, affine section-power ranges, the inclusion D(f) in the surjective
stalk locus, radical annihilation of a finite image, affine vanishing, and passage
from sections to morphisms on subopens. A finite affine cover and the maximum of
its vanishing degrees finish the proof by Mathlib sheaf separation. The node now
records this route. No new public statements or nodes were introduced.

Added proof-only imports of the ideal-product affine-sections module and the
affine finite-type module (using `import all` for their existing proved private
helpers), `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Mathlib.RingTheory.Support`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
and `Sheaf.AlgebraicGeometry.FormalPolynomialPowerLifts`. No other modules were
adapted. The original unit route is preserved; this node realizes none of the
unit's own statement or numbered steps.

The source injectivity and finite-cover arguments were checked against
[Stacks 01PM](https://stacks.math.columbia.edu/tag/01PM) and
[Stacks 01PQ](https://stacks.math.columbia.edu/tag/01PQ).

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.ideal_power_local_maps_eventually_agree`
(node `lem-weil-pbc-ideal-power-local-maps-eventually-agree`).
Added 0 holes, split off 0 statements. No `sorry` remains in any delivered file.
All seven new private helpers are proved. This is a proof, not a decomposition.

The module compiles without warnings through the launcher. An explicit
`#print axioms AlgebraicGeometry.Scheme.ideal_power_local_maps_eventually_agree`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; even its used
transitive dependencies contain no proof hole. The independent second reader reproduced this axiom list against the locally
compiled delivered module, covering all seven used private helpers transitively.

Edge cases are handled by the proof: n=0 uses the identity power and J^0;
J=0 and the zero ring are included in the radical/power argument; empty overlap
uses an empty finite cover with m=n and sheaf separation on the empty cover.
Only compactness of the overlap is used, with no separatedness assumptions.

## No longer needed

No original import was removed: all three public imports support the existing
statement. The planned dependency `lem-weil-pbc-glue-sheaves-of-modules` and module
`Sheaf.Topology.GlueSheavesOfModules` are not needed by this proof and are not
imported. Mathlib sheaf separation supplies the required uniqueness directly.

The original direct proof dependencies
`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-spec-module-tilde-sections` are replaced by the already proved
`lem-weil-pbc-affine-module-basic-open-localization` interface. They remain
transitive ingredients of that localization interface; this report does not
claim their modules leave the targets' import closure.

The attempted imports `Sheaf.AlgebraicGeometry.IdealPowerEvaluationAffineEventuallyZero`,
`Sheaf.AlgebraicGeometry.AffineSectionCoverTwistGeneration`, and
`Sheaf.AlgebraicGeometry.CoherentAffineMapSupportRadical` were removed before
delivery. None is needed by the final proof. In particular, no coherent-module
or line-bundle twisting theory is imported merely to use its private helper.
All other original planned dependencies remain needed in the updated node.

## Where the brief, the DAG or earlier work was wrong

The previously stated affine eventual-zero theorem takes a global morphism on X,
so it cannot be applied directly to the two locally defined maps. Its source file
also contained newer private helpers absent from the compiled baseline. The
local argument here uses the already compiled product and finite-type helpers
and proves the necessary version for a morphism over an arbitrary open T.

The monomial exponent calculation in the old proof plan is mathematically valid,
but unnecessary: localization of the finite image gives a radical-annihilator
bound, and the range equality for powers gives the required exponent n+k. The
finite maximum and sheaf separation then need no new gluing theorem.


## Second reading by J1

1. Compared the entire delivered Lean module with the repository version. The
   existing theorem signature, visibility, docstring, three public imports, and
   all definitions are byte-for-byte unchanged. The additions are seven private
   proved helpers, six proof-only imports, and the replacement proof. No interface
   change or change record is needed. Verdict: pass.
2. Read all seven helper proofs and the complete target proof, and compiled the
   delivered module locally without errors or warnings (44.8 seconds). No `sorry`,
   forbidden declaration, hollow definition, or arbitrary witness from an unproved
   existence theorem occurs. A scratch copy with the appended axiom check timed
   out; compiling the actual module to the sandbox output (53.1 seconds) and
   importing it into a scratch axiom-check module succeeded (2.0 seconds), with
   exactly propext, Classical.choice, and Quot.sound. The first delivery dry run
   printed OK but its larger all-declaration probe timed out; the independent
   target check covers every new helper, all of which the target uses. Verdict: pass.
3. No statements were split off and no new holes were added. Checked the finite
   affine image, radical-annihilator bound, and power-range argument in the cases
   n=0, J=0, the zero ring, and the empty overlap. Every chosen exponent or cover
   is supplied by a proved theorem. Verdict: pass.
4. Checked the upstream basic-open denominator lemmas, the product-range and
   finite-type helpers, and the existing global eventual-zero theorem. The latter
   has a global-map interface, while this proof needs a map on an arbitrary overlap;
   using the existing lower-level lemmas is a direct valid route. Each added import
   supports those proof ingredients. The three removed old proof dependencies
   (affine tilde/Gamma, Spec tilde sections, and sheaf gluing) are all accounted for
   under No longer needed. The node is absent from sk-thm-p1's realized statement
   and steps; its unit route is preserved. Verdict: pass.
5. Compared the old and delivered node JSON. Only proof, proof_deps, and
   proof_origin changed. The proof steps describe the actual Lean reductions;
   proof_deps is exactly the union of their uses. The localization dependency
   names the two upstream lemmas actually used, and no new nodes need auditing.
   Verdict: pass.

Second reading changed only this report, adding the independent review record
and replacing the unsupported claim that the timed-out delivery probe ran with
the successful explicit target-axiom check.
No Lean or DAG repair was needed.
