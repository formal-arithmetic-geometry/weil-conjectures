## What changed

Replaced the sorry in AlgebraicGeometry.etale_infinitesimal_pointwise with a complete
proof combining the existing Artinian smoothness criterion, a new theorem providing its
Artinian tests, a proved private fibre-dimension lemma, and the existing étale shrinking
lemma. The theorem signature and all public imports are unchanged.

Added Sheaf.AlgebraicGeometry.ArtinianLiftingFromEtaleInfinitesimal, with a single public
statement for the test-diagram lifting part of Stacks Tag 0A43. Its statement does not
require the finite-type, quasi-compactness or Noetherian hypotheses: those are needed
when applying the existing smoothness criterion, not for factoring Artinian tests.

The private fibre_dimension_zero_of_etale_closed_baseChange is proved without additional
holes. It factors the residue-field point through a closed immersion, pastes pullbacks,
obtains an étale fibre projection and computes local dimension using discreteness.

Both modules compile through lcompile.py --all, without errors or warnings.

## Proved and sorry left

Closed the one original hole: AlgebraicGeometry.etale_infinitesimal_pointwise
(lem-weil-pbc-etale-infinitesimal-pointwise).

Added one hole: AlgebraicGeometry.artinian_lifting_tests_of_etale_infinitesimal
(lem-weil-pbc-etale-infinitesimal-artinian-tests), in its own module. This is a
decomposition, not a complete proof independent of sorry. The original module has
no sorry left. The existing smoothness and étale shrinking theorems remain dependencies.

## No longer needed

Removed proof imports Sheaf.AlgebraicGeometry.BaseChangeConventions,
Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres,
Sheaf.AlgebraicGeometry.FormallySmooth, and Sheaf.AlgebraicGeometry.Thickening.
Their notions needed in signatures are already exposed by the necessary imports;
FormallySmooth and Thickening may be needed downstream for the new Artinian-tests item,
but are not used by this module's proof.

The direct proof dependency lem-weil-pbc-etale-smooth-zero-dimensional-fibres and its module
Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres are bypassed by the proved private
fibre-dimension argument. Its subsidiary Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
is likewise unnecessary on this branch. No global unreachability is claimed for these modules.

## Where the brief, the DAG or earlier work was wrong

The original plan does not state the Artinian-test lifting bridge needed to apply
smooth_near_iff_artinian_lifting_at_point. Also, knowing zero fibre dimension for the
zeroth base change requires transporting it to the original fibre. The delivery supplies
the former as one strict intermediate statement and proves the latter directly.

The local Stacks source file is absent on this machine; checked the statement and proof
at https://stacks.math.columbia.edu/tag/0A43. LeanSearch returned an Internal Server Error;
LeanFinder, Loogle and local grep were usable. No statement dispute or interface change.

## New nodes

lem-weil-pbc-etale-infinitesimal-artinian-tests records the Artinian-test factorization
and lifting step of Stacks Tag 0A43. The proof in words explains nilpotence of the
Artinian maximal ideal, factorization through one infinitesimal neighbourhood,
first-order lifting there and projection back to X. The statement was checked on
empty closed subschemes (the point hypothesis is impossible), nonreduced schemes,
and arbitrary nilpotent test extensions. No arbitrary data is defined from its sorry.
No change records or forced adaptations.

## Second reading by F2

1. **Signatures unchanged.** Compared the delivered pointwise module with the repository version; the
public theorem `AlgebraicGeometry.etale_infinitesimal_pointwise` has the identical signature and
statement. The added Artinian lifting declaration is a new split-off theorem with its own DAG node.
Verdict: pass.

2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`; the pointwise theorem has
no `sorry`, and the only remaining `sorry` is the named split theorem
`AlgebraicGeometry.artinian_lifting_tests_of_etale_infinitesimal`. No prohibited declarations or
hollow definitions were introduced. Verdict: pass subject to the declared split theorem.

3. **Split statement.** Checked the Artinian lifting statement against the cited Stacks Tag 0A43
argument and small cases (including nonreduced Artinian tests and arbitrary nilpotent extensions).
It is a strict intermediate statement, has a source and proof docstring, and is not duplicated in
the library or Mathlib. Verdict: pass.

4. **Pruning and route.** The pointwise proof uses the smoothness criterion, the new Artinian test
bridge, the zeroth-neighbourhood étaleness, the direct fibre-dimension argument, and the existing
étale shrinking theorem. Unused proof imports and the bypassed zero-dimensional-fibre module are
listed above; the unit route remains represented by the target and its split dependency. Verdict:
pass.

5. **DAG agreement.** The target node records the actual proof dependencies and the new node records
the split theorem, source, proof steps, Lean declaration, and unit/chapter metadata. Verdict: pass.

Changed only the two delivered modules, the new node, and this report section; no target statement or
definition was changed.
