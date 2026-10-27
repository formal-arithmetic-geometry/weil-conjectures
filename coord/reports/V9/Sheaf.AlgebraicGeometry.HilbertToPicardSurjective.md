## What changed

Proved `AlgebraicGeometry.surjective_hilbertToPicardMorphism`, with its complete original
signature and public imports unchanged. A proved private helper generalizes the adopted
source's `exists_abelClass_eq` from degree equal to the genus to `d ≥ genus`: the only
mathematical change to that effectiveness argument is the final integer inequality.
The helper constructs the nonzero section's zero divisor and verifies its Hilbert degree.
The main proof identifies the given universal class with `abelClass` using `hD`, establishes
the classifying equality for every test scheme by naturality, and lifts geometric points.

Added the private proof import `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`, whose
existing proved Abel-map and fppf geometric-section APIs provide the shorter route.
No adopted source file, definition, target or public signature is changed. Updated the item
node's proof, proof dependencies and proof origin to match this route. The existing theorem
`exists_toSheafify_app_eq_of_isAlgClosed` had no DAG attachment; one new node attaches it
without adding a declaration or module. The unit's Riemann–Roch → nonzero section → effective
divisor → Hilbert point → surjectivity argument is retained.

Validation: the final module compiled on the project compile server with no errors or
warnings (last semantic compile: 12.5 seconds; formatting warnings subsequently repaired). The degree-genus boundary gives χ=1, including genus=d=0;
for larger d positivity only improves. The empty effective divisor is allowed by the Hilbert
functor, and the proof uses no positive-degree assumption. Algebraic closures of residue
fields stay in the specified universe. No new mathematical hypothesis is introduced.

## Proved and sorry left

Closed 1 of 1 existing holes: `AlgebraicGeometry.surjective_hilbertToPicardMorphism`
(node `lem-sc-hilb-to-pic-surjective`).

The private helper `exists_abelClass_eq_of_genus_le` is fully proved.
There are zero `sorry`s left in the delivered module, zero holes added, and zero split-off
holes. Existing dependencies remain subject to their own proof status; this delivery does
not claim to eliminate their transitive axioms.

## No longer needed

Removed the following private imports (public imports are preserved):

- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.CartierDivisorFinite`
- `Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier`
- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`
- `Sheaf.Paper.EulerCharacteristicWellDefined`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`
- `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`
- `WeilConjectures.AlgebraicGeometry.DensePoints`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
- `WeilConjectures.AlgebraicGeometry.Hilbert.Defs`
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`
- `WeilConjectures.AlgebraicGeometry.Picard.Degree`
- `WeilConjectures.AlgebraicGeometry.Picard.RationalPoint`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper`

The direct route does not need `lem-pc-rational-points-dense`, `thm-pc-pic-split`,
`lem-pc-rational-hyp`, or `def-pd-degree-morphism`: evaluate sheafification over an algebraic
closure instead of splitting the Picard functor using a rational point of C.
`lem-pc-cartier-divisor-finite-over-field` and its module
`Sheaf.AlgebraicGeometry.CartierDivisorFinite` are unnecessary for this proof: the adopted
source's smooth-proper-curve theorem `isFinite_subschemeι_comp` suffices, recorded on the
existing `def-sc-effective-cartier-divisor` node. The more general proper dimension-at-most-one
statement is not invoked. `Sheaf.Paper.EulerCharacteristicWellDefined` is an obsolete duplicate;
the source cohomological formulas already supply what is needed.

The direct `Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier` import is unnecessary:
the proved source zero-locus API supplies the invertible ideal criterion directly. Its
mathematical step stays in the DAG. The other removed imports are already available through
the preserved public imports and the single explicit Jacobian proof import; removing them
does not claim their mathematical facts are unnecessary. No module is withdrawn, and these
pruning claims concern this proof, not every other consumer in the project.

## Where the brief, the DAG or earlier work was wrong

The plan's arithmetic and divisor argument are correct, but its additional rational-point
and Picard-splitting work can be avoided for topological surjectivity. It is enough to lift
points over algebraic closures of residue fields, using the complete existing source
`exists_toSheafify_app_eq_of_isAlgClosed`. The adopted source also already implements nearly
the entire effectiveness argument at degree equal to the genus. Reused that implementation
and generalized its integer calculation instead of introducing new unproved intermediates.

The existing declaration docstring is preserved as requested by the Lean skill; the revised
DAG and this report describe the more economical geometric-point implementation.

## New nodes

`lem-sc-fppf-sheafification-geometric-section` records the existing proved source theorem
`AlgebraicGeometry.exists_toSheafify_app_eq_of_isAlgClosed` in
`WeilConjectures.AlgebraicGeometry.Picard.Jacobian`. It is a generic tool for the geometric
point step, from Stacks 00WK and 01TF. Its proof obtains a local representative and pulls it
back along the section of an fppf cover over an algebraically closed field. The exact
source signature is recorded; no new Lean file, statement, proof hole, or arbitrary witness
definition is introduced. Searches of the DAG's Lean attachments and full statements found
no existing attachment. Blueprint searches for "sheafification" and
"sheafification algebraically" found no blueprint statement of this specialization.
The first preflight classified added `open` commands as interface changes. Removed those
commands and qualified all names explicitly; the project interface checker now reports
no changes. No change record is required: no existing statement or definition changed.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
