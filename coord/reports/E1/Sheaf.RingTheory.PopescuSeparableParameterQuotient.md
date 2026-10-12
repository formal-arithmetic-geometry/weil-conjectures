## What changed

The original theorem `Algebra.exists_popescu_resolution_parameter_quotient` now constructs
canonical quotient data, proves the quotient-prime geometry, and distinguishes whether the
extended singular ideal escapes the quotient prime. The escape case uses an identity
resolution (with a canonical universe lift); the other case combines a local resolution
with `Algebra.canBePopescuResolved_of_local_height_zero`.

Six new modules hold the quotient-data theorem, quotient-prime geometry, local-resolution
obligation, singular-ideal equivalence transport, extended-ideal equivalence invariance,
and identity resolution. Five supporting results are fully proved. Every new
module is recorded by its own node. Existing public imports and the target signature are
unchanged. Five proof imports moved into the local-resolution module. The redundant direct
`SingularIdeal` proof import was removed; `PopescuResolution` already publicly provides it.

## Proved and sorry left

Original hole closed: `Algebra.exists_popescu_resolution_parameter_quotient`.
New hole added: `Algebra.parameter_quotient_local_resolution`, node
`lem-weil-pbc-popescu-parameter-quotient-local-resolution`, in
`Sheaf.RingTheory.PopescuParameterQuotientLocalResolution`.
There are no other sorries in the delivered files.

Fully proved supporting declarations:
`Algebra.parameter_quotient_data`, `Algebra.parameter_quotient_prime_geometry`,
`Algebra.singularIdeal_map_equiv_le`, `Algebra.popescuIdeal_comp_equiv`, and
`Algebra.canBePopescuResolved_of_ideal_not_le`.

This is a decomposition, not a complete proof of the item: one original hole was closed
and one strictly local hole was added, for a net of zero. The original theorem still has
`sorryAx` transitively, as does the new local-resolution statement. The five supporting
results have only `propext`, `Classical.choice`, and `Quot.sound`, verified by `#print axioms`
in a scratch copy. All seven delivered modules compile without errors or warnings.

The first worker's `parameter_quotient_resolution_core (P : Prop) : P` was false and was
removed, not counted as a legitimate hole closed. The first worker's unproved
`parameter_quotient_data` was repaired into the proved canonical construction above.

## No longer needed

No library module is claimed pruned. Removed direct imports from the item:
`Sheaf.Algebra.PopescuLiftNilpotent`, `Sheaf.FieldTheory.SeparableSmoothColimit`,
`Sheaf.RingTheory.FlatOverRegular`, `Sheaf.RingTheory.PolynomialOriginRegularLocal`, and
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence` now belong to the local-resolution
obligation and remain in the item's import closure. The direct
`Sheaf.RingTheory.SingularIdeal` import is redundant through `PopescuResolution`.

Every old proof dependency was compared with the new proof. The regular-sequence,
polynomial-origin, flat-over-regular, flat-module-quotient-flat, separable-smooth-colimit,
nilpotent-lifting and finite-presentation filtered-colimit factorization nodes are now
local-resolution dependencies. `def-weil-pbc-singular-ideal` and
`def-weil-pbc-popescu-resolution` remain used by the supporting definitions and identity
resolution. `lem-weil-pbc-popescu-delocalize-height-zero` is used directly by the item.
No old dependency is silently discarded. None of these nodes realizes a fixed step of the
unit directly; `dag/units/sk-thm-p1.json` and its realized route are retained.

## Where the brief, the DAG or earlier work was wrong

The first worker's claimed resolution core was an unrestricted proof of every proposition,
including `False`. Compilation alone did not expose this because it was admitted. The new
helper modules had no DAG nodes and no complete proof docstrings. The report's claim of a
valid two-part decomposition was therefore incorrect. Its imports also had not been
pruned, and its target proof emitted a style warning.

The repaired local obligation asserts only the resolution after localization, not the
original global existential conclusion. Quotient construction and geometry are proved,
and delocalization is an actual application of the existing theorem. This is a real
reduction rather than moving the item to another name. The Stacks proof of Lemma 07FE,
`lemma-resolve-special`, final paragraph, was read locally. Its regular-parameter flatness,
Artinian/nilpotent lifting, smooth factorization and delocalization route agrees with this
reduction. LeanSearch was unavailable; actual LeanFinder, Loogle and Mathlib grep searches
were performed and recorded. Searches in both Lean source libraries found no existing
public statement that supplies the entire new local obligation or the new helpers.

## Second reading by E1

1. Compared the delivered item with the repository using `diff` and checked its complete
   theorem signature byte for byte: unchanged. No existing declaration, definition or
   public import was changed. All other modules are new; no change record is needed for
   changing the first worker's unpublished sandbox helper statements. Verdict: pass.
2. Compiled all seven modules with `lcompile.py`. All are clean. Scanned for forbidden
   declarations and checked every theorem with `#print axioms` in a scratch copy. Only
   the explicitly reported local hole and the item using it have `sorryAx`; the other
   five theorems use only the three permitted axioms. There are no holed definitions or
   arbitrary data chosen from admitted existence theorems. Verdict: pass as decomposition.
3. Read and checked the new statements. The canonical quotient data and prime geometry
   are proved, including `d=0`. Geometry even allows `c=0`: when `d>0` the quotient has
   no prime, and when `d=0` the generation hypothesis makes the local ring a field.
   The remaining local theorem is exactly the local smooth-factorization step of Stacks
   07FE and has its complete proof in words and node. It cannot itself assert the global
   quotient resolution. Equivalence and identity helpers were proved in Lean. Searches
   found Mathlib ingredients, which the proofs use, but no duplicate public theorem.
   Verdict: pass; one local obligation remains open.
4. Read the item downward. Quotient data uses Mathlib quotient and finite-presentation
   lemmas; prime geometry uses prime contraction and Mathlib zero-dimensional localization;
   the identity case uses equivalences and Mathlib smoothness transport. Only the remaining
   local construction is split off, then the existing height-zero theorem delocalizes it.
   Checked the old dependencies and the unit realization. Verdict: pass; no unit bypass.
5. Checked every new node's signature against its Lean declaration, its proof steps,
   proof-dependency union, source, creation record, searches and blueprint provenance.
   The existing item's node now records the proof actually written. Verdict: pass.

Changes made during second reading: removed the false universal core; proved the quotient
construction and prime geometry; proved equivalence/identity resolution helpers; isolated
one true local obligation; repaired documentation, imports, nodes and this report; removed
the target's style warning. The original theorem is still incomplete transitively.

## New nodes

`lem-weil-pbc-popescu-parameter-quotient-data`: proved canonical quotient data and finite
presentation, in `Sheaf.RingTheory.PopescuParameterQuotientData`.

`lem-weil-pbc-popescu-parameter-quotient-prime-geometry`: proved minimality and local
zero-dimensionality, in `Sheaf.RingTheory.PopescuParameterQuotientPrimeGeometry`.

`lem-weil-pbc-popescu-parameter-quotient-local-resolution`: the sole admitted local
smooth-factorization step, in `Sheaf.RingTheory.PopescuParameterQuotientLocalResolution`.

`lem-weil-pbc-singular-ideal-map-equiv`: proved singular-ideal transport, in
`Sheaf.RingTheory.SingularIdealMapEquiv`.

`lem-weil-pbc-popescu-ideal-comp-equiv`: proved extended-ideal invariance, in
`Sheaf.RingTheory.PopescuIdealCompEquiv`.

`lem-weil-pbc-popescu-resolution-identity`: proved identity resolution in the required
universe, in `Sheaf.RingTheory.PopescuResolutionIdentity`.
