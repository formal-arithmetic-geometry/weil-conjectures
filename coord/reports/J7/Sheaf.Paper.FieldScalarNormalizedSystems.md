## What changed

Replaced the original upper sorry by a complete family-assembly proof. Finite type
and quasi-compactness over the field scheme give Noetherianity of X and Y, hence of T.
The proof chooses single-inclusion data inside the existence proof and applies the
identity and successive comparison statements to those very choices. Its private
cofinal_ramification theorem proves ell = unit * uniformizer^h with h positive,
then proves the exact ideal-power formula, including exponent zero.

Moved the seven existing record/abbreviation declarations verbatim into
Sheaf.Paper.FieldScalarNormalizedData, publicly re-exported by the original module.
This prevents a cycle between the shared record types and the split proof lemmas.
No target or existing theorem signature changes. The original theorem docstring stays.
Change record: coord/changes/J7-field-scalar-record-extraction.md.

Validation: all five Lean modules compiled through lcompile.py. The first compile
identified a final principal-ideal rewrite and style warnings; both were corrected,
and the main module then compiled cleanly. Record signatures and bodies were compared
against the original and are identical. Delivery repeats compilation and preflight
with probes after removal of the unused private imports.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.FieldScalar.field_scalar_normalized_systems.
Proved its private cofinal_ramification helper without additional holes.

Added exactly three named holes, each the whole proof of a public theorem in its own
module:

- AlgebraicGeometry.ProEtale.FieldScalar.field_scalar_single_inclusion.
- AlgebraicGeometry.ProEtale.FieldScalar.field_scalar_identity_comparison.
- AlgebraicGeometry.ProEtale.FieldScalar.field_scalar_successive_comparison.

This is a decomposition: 1 upper hole closed, 3 strictly partial holes added, net -2.
The first omits all identity and successive-extension data; the other two assume
already supplied data and prove only their respective coherence. None asserts Family
or restates the original hypotheses and conclusion. No sorry occurs in a definition,
private declaration, or partial proof. The data module has zero holes.

## No longer needed

No mathematical dependency is withdrawn or globally pruned. No declared dependency
is discarded: the former proof plan is distributed among the three new nodes. The original proof
requirements remain below the three new statements, with their original declared
nodes retained there. The upper theorem now directly uses only those three lemmas,
the Noetherianity Mathlib leaf, the coefficient-extension vocabulary and the shared
data node. Its node proof_deps are updated accordingly.

The original public imports are preserved through the data module. The unused private import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
is removed. Mathlib.AlgebraicGeometry.Noetherian is removed from the extracted data
header and imported explicitly by the upper theorem and the single-inclusion statement.
No route of the blueprint unit is bypassed. No unused upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The source statement is not disputed. The original plan's scalar tools concern
several encodings (internal modules, section-action sheaves, generic semilinear systems).
They do not directly state the packaged field-specific ScalarData and its normalized
whole-system identity/successive squares. Those bridges are the three remaining steps,
rather than unsupported uses of independently chosen derived evaluation isomorphisms.
Their docstrings give the generator, transition, K-flat, and localization arguments.

Edge cases checked mathematically: identity embeddings multiply scalars; successive
identity embeddings give the same multiplication; independent integral bases need
not compose; ramified extensions still use ell-power quotients; n=0 in the cofinal
formula gives the unit ideal; the empty scheme does not affect the tensor or descent
arguments. Noetherianity is used only for constructibility in the single-inclusion
lemma. Identity and successive comparisons require no finite-type hypothesis.

Searches used LeanSearch, LeanFinder, Loogle and Mathlib/project rg. Mathlib supplies
ordinary ModuleCat tensor compositors and left-adjoint uniqueness, but not these
normalized strict-system records. The existing DAG dependencies are used as the plan
for the split statements, rather than restated as new generic tools.

## New nodes

- def-sp-field-scalar-normalized-data records only the seven moved definitions.
- lem-sp-field-scalar-single-inclusion carries the basis, exact extension,
  preservation and integral reduction comparison part of paragraph (1).
- lem-sp-field-scalar-identity-comparison carries the multiplication unitor and its
  ordinary/derived normalization and reduction square for given scalar data.
- lem-sp-field-scalar-successive-comparison carries the tensor compositor and its
  reduction square for three given scalar data.

All inherit sec-smooth-purity / sk-lem-sp-field-extension and identify paragraph (1)
of det-sp-field-extension-towers as their blueprint origin. Each statement has a full
proof in words and the existing node dependencies for its steps. The extraction and
public re-export are documented in coord/changes/J7-field-scalar-record-extraction.md.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
