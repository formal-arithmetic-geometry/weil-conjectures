## What changed

The item theorem is proved from an integral hypersurface presentation and a proved
geometric-integrality transfer lemma. Both proof dependencies have new modules and nodes.
The target signature and all existing public imports remain unchanged.
The second reader removed the unused geometric-irreducibility public import
from the new integral-presentation module, and three redundant proof imports
from the new transfer module (already publicly reachable through its imports).
The original scheme is shown integral using Mathlib, then the same n, Q and field
isomorphism supplied by the presentation are retained in the conclusion.

The transfer lemma is proved: affine base change is identified with a tensor algebra;
localizing the domain after field extension produces the common fraction-field tensor;
flatness preserves the injection of the second section ring into that domain.
It needs neither finite type nor a hypersurface assumption.

## Proved and sorry left

Closed: AlgebraicGeometry.exists_field_hypersurface_function_field_model (1 original hole).
Proved without sorry: AlgebraicGeometry.geometrically_integral_of_fractionRing_equiv,
including its private affine-base-change and tensor-localization helpers.
Added: AlgebraicGeometry.exists_integral_field_hypersurface_presentation
(lem-sbc-field-hypersurface-integral-presentation), the only remaining sorry.
This is a decomposition, with one hole closed and one added, not a complete proof
of the separating-generator construction.

## No longer needed

The original module had no proof-dependency imports to prune.
Second reading removed Mathlib.AlgebraicGeometry.Geometrically.Irreducible
from the new presentation module and the redundant imports
Mathlib.RingTheory.Localization.BaseChange, Mathlib.RingTheory.Flat.Basic, and
Mathlib.LinearAlgebra.Basis.VectorSpace from the transfer module. The latter
remain transitively available through its public geometric-property imports;
no project DAG node or module is pruned by these import cleanups.
No old DAG node or module is bypassed. The unit record has no realized nodes for
this construction. The new transfer module does not import finite-type or
multivariate-polynomial modules, since its general proof needs neither notion.

## Where the brief, the DAG or earlier work was wrong

The original node had three non-elementary steps but no proof dependencies. The
new nodes supply the missing interfaces without altering the statement or unit route.
Empty spectra are excluded by integrality. Purely transcendental fields, including
L=K, use the extra variable Q=T in the construction's documented proof. A finite
separable field extension is also covered by the presentation, whose hypotheses
intentionally do not require geometric irreducibility.

## New nodes

lem-sbc-field-hypersurface-integral-presentation: separating generators and a
primitive minimal-polynomial numerator produce an integral hypersurface over K
with the same fraction field. This remaining construction does not assert
geometric integrality and does not assume geometric irreducibility.

lem-sbc-field-fraction-ring-geometric-integrality: the fully proved transfer of
geometric irreducibility and reducedness between integral affine schemes with
an isomorphism of fraction fields fixing the base sections.

## Second reading by B3

1. Compared every delivered module with the repository. Only the item module
already exists: its theorem signature is byte for byte unchanged, as are its
original public imports. Its only changes are proof imports and the proof.
The two other modules are new. No existing definition or statement changes,
no change record is required, and no arbitrary witness is chosen in a definition.
Verdict: pass.

2. Compiled all three modules with lcompile.py and independently compiled scratch
copies with #print axioms. The transfer theorem uses only propext, Classical.choice
and Quot.sound; the item theorem additionally uses sorryAx solely through the
named integral-presentation theorem. There is exactly one sorry, in that theorem;
no forbidden declarations or hollow definitions occur. Reviewed the tensor
localization denominators, base-field compatibility, affine pullback identification,
and flat injection individually. Verdict: pass as a decomposition, net zero holes.

3. The integral presentation is a strictly smaller part of the original argument:
it constructs an integral hypersurface without asserting geometric integrality and
requires no geometric irreducibility. Its source, full prose proof and node agree.
Checked K itself and purely transcendental extensions (Q=T in an extra variable),
finite separable extensions (the minimal polynomial), and a non-geometrically
irreducible integral source. Empty schemes are excluded by IsIntegral; purely
inseparable algebraic extensions fail geometric reducedness. Repeated searches
with leanfinder for a one-equation presentation of a finitely generated separable
field, loogle for IsSeparablyGenerated, and grep for primitive-element and
fraction/geometric results. Also searched both library roots. Primitive-element,
transcendence-basis and fraction-ring equivalences are available separately, but
no existing declaration supplies this presentation. Closing it is not a short
proof repair. Verdict: pass; one construction hole remains.

4. The item first derives integrality using proved Mathlib declarations, applies
the smaller construction, and uses the independently proved transfer. No original
proof_deps existed, so none are omitted from No longer needed. The unit
sk-prop-normal-form has empty realized lists; its fixed normal-form and slicing
route is preserved. The new helper is a tool below that route. Reviewed import
visibility and removed the unused public Irreducible import in the construction
module, and three redundant proof imports from the transfer module, whose
declarations remain transitively available. Verdict: pass.

5. All three node lean.statement strings match their Lean signatures exactly.
The existing node changes only proof, proof_deps and proof_origin; its dependencies
are precisely the two theorems applied. The new nodes have the required creation,
source, blueprint, Lean and search records; the transfer node records the actual
Mathlib tensor/localization proof and has no unproved project dependencies.
Verified the cited construction in [Stacks Tag 0559](https://stacks.math.columbia.edu/tag/0559),
with [030W](https://stacks.math.columbia.edu/tag/030W) and
[030Q](https://stacks.math.columbia.edu/tag/030Q) for geometric reducedness and
separating generators; [035W](https://stacks.math.columbia.edu/tag/035W) and
[054Q](https://stacks.math.columbia.edu/tag/054Q) support the generic-point transfer.
Verdict: pass.

Changed: removed one unused public import from the new integral-presentation
module and three redundant proof imports from the transfer module; expanded this report with independent checks and the decomposition verdict.
No proof or statement required repair.
