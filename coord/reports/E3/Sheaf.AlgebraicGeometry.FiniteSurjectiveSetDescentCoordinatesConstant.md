## What changed

Proved `AlgebraicGeometry.finiteSurjectiveSetDescent_coordinates_constant` in
`Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentCoordinatesConstant`.
The theorem signature is preserved verbatim, and its original docstring and all
imports are preserved. Added private notation from the earlier attempt was expanded
to full names, and the original universe command is preserved; the static interface
comparison reports no changes. All added declarations are private, real definitions or
proved helpers; no public interface or dependency module is changed.

The proof identifies restriction of stalk units on germs, builds the map Q from
a second stalk unit and the composition isomorphism, and proves Q R_f = R_k.
Injectivity of the supplied coordinates gives R_f c = identity, hence d Q = c.
A common geometric lift and compatibility of the two comparison sections then
give equal coordinates. Private transport helpers use primitive casts, with a
proved conversion from categorical eqToHom evaluation. The node copy records this
argument and keeps the same three proof dependencies and the unit route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finiteSurjectiveSetDescent_coordinates_constant`
(node `lem-weil-pbc-sets-finite-descent-coordinates-constant`).
Added zero holes; no `sorry` remains in the delivered module. This is a proof,
not a decomposition. The existing inverse-image germ and composition-unit
theorems are both already proved. The temporary coordinate at the common lift is
used only within theorem proofs; no arbitrary witness is put into a definition.

The full module compiles without warnings through the required `lcompile.py`,
with the diagnostic heartbeat limits removed. The theorem signature was compared
verbatim with the repository version. The delivery dry run also checks axioms.

## No longer needed

None. Both original proof imports are used, and all three original dependency
nodes remain needed: `lem-weil-pbc-sets-etale-inverse-image-stalk-germ`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`, and
`def-pc-fibre-product`. The public imports supply the definitions used by the
unchanged statement. No new module or node is required.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface discrepancy was found. The earlier sandbox
attempt had a complete tactic proof but failed kernel checking at the transport
step. Using abstract common-composite parameters and primitive casts in private
helpers repairs the costly conversion without modifying a library definition,
raising the final compilation limits, or splitting off a hole. The first dry run
flagged the earlier attempt's local notation and the added universe command as an
interface change. Removing these commands resolved that finding; no change record
or second-reading text was fabricated.

The planned common-refinement argument for arbitrary germs is replaced by the
stalk-map identity Q R_f = R_k and injectivity of c. This is below the unit level;
the unit statement and its realized route are preserved. The argument does not
choose a lift when the fibre is empty, and a section of an empty sheaf is never
assumed to exist. It also does not need finiteness for the coordinate calculation;
the existing finite-morphism hypothesis remains unchanged.

The literature directory is absent in this clone. The source passages were read
at the official Stacks pages: [09Z2](https://stacks.math.columbia.edu/tag/09Z2),
[09Z3](https://stacks.math.columbia.edu/tag/09Z3), and
[03Q1](https://stacks.math.columbia.edu/tag/03Q1).
The earlier attempt's recorded LeanFinder, Loogle and grep searches found no
exact coordinate theorem; fresh local searches found only the assigned theorem
and its caller. Loogle also confirmed the categorical transport composition
lemma; the final equality-induction argument needs no additional import.


## Second reading by E3

1. Compared the delivered module with the repository version. The target theorem signature and all existing declaration signatures are byte-for-byte unchanged; only the proof body and private proof helpers differ. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings and contains no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declarations. The proof closes the original target hole and adds no holes. Verdict: pass.

3. Checked the private helper arguments and the coordinate argument on edge cases, including the empty-fibre situation: the proof only uses a lift after one is supplied by the pullback universal property, and never constructs an arbitrary witness from mere existence. The existing target statement remains exactly as strong as before. Verdict: pass.

4. The route uses the imported inverse-image stalk-germ, composition-unit, and fibre-product declarations, and the DAG proof steps and `proof_deps` match the proof. No unused imports or nodes were found. Verdict: pass.

5. The unit route is preserved: the item node still realizes the same unit statement and proof route, while the shorter coordinate calculation is below the unit level. Verdict: pass.

Changed only the proof body, restored the original author header, and added this second-reading record.
