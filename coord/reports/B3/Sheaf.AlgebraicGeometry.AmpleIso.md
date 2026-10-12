## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isAmple_iff_of_iso` in
`Sheaf.AlgebraicGeometry.AmpleIso`, keeping its signature and existing docstring unchanged.
Three proved private helpers construct tensor-power isomorphisms, prove linearity of stalk
maps over the commutative scheme stalk ring, and identify the nonvanishing loci of transported
sections. The main proof preserves compactness, exponents, affine opens, and their pointwise
nonvanishing predicates, in both directions. The copied node records these actual steps.

The only remaining import is the existing public statement import
`Sheaf.AlgebraicGeometry.Ample`. No public interface, definition, or statement changed.
The unit `sk-thm-curveestimate` has only `thm-sc-proper-cohomology` as its realized statement
and no realized steps; this internal isomorphism-transport lemma preserves the unit route.

Searches: LeanFinder for isomorphic invertible sheaves having the same ampleness returned
morphism-property invariance results, with no matching ampleness theorem. Loogle confirmed
`Submodule.smul_top_le_comap_smul_top`; local searches of Mathlib and both library roots
found no absolute ampleness invariance result and exposed the recursive source `tensorPow`.

## Proved and sorry left

Proved the original sole sorry, `AlgebraicGeometry.Scheme.Modules.isAmple_iff_of_iso`
(node `lem-sc-ample-iso`). All three private helpers are proved. No sorry remains in the
item, and none is added elsewhere. Local single-file compilation is clean.

## No longer needed

Removed proof imports:
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Topology.PresheafModuleStalkFunctor`

Removed proof-dependency edges to `def-pur-sheaf-tensor-product` and
`def-weil-pbc-module-stalk`. Their corresponding modules listed above are unnecessary for
this proof. The source monoidal tensor and recursive `Scheme.Modules.tensorPow` are already
available through `Ample` and `WeilConjectures.AlgebraicGeometry.Modules.Invertible`;
the general change-of-rings and positiveTensorPower APIs are unused. Mathlib's germ maps
and stalk module action suffice directly, without the general ring-valued stalk functor.
The source invertible-module node is recorded as the tensor-power construction dependency.
These are local pruning claims; other callers may still need the removed modules.
Statement dependencies and the underlying tensor/stalk notions remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original plan labels stalk transport elementary,
but its recorded stalk functor is over the ring-valued stalk, whereas `IsAmple` uses the
commutative-ring-valued stalk. These are not definitionally the same scalar type. The proof
establishes the needed commutative-stalk linearity directly by the common-neighborhood germ
argument, without changing either definition. It applies to arbitrary modules for locus
transport, so zero modules, zero sections, and the empty scheme require no exceptions.

## Second reading by B3

1. **Unchanged visible statements.** Compared the delivered module with the repository version. The existing theorem signature and docstring are byte-for-byte unchanged; only proof imports, private proof helpers, and the theorem proof differ. The DAG node changes only proof metadata and proof dependencies, with no statement change.

2. **Proof and trust.** Compiled `Sheaf.AlgebraicGeometry.AmpleIso` with `lcompile.py`; compilation succeeds with no errors and no `sorry`. `#print axioms AlgebraicGeometry.Scheme.Modules.isAmple_iff_of_iso` in a scratch copy reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The proof contains no forbidden declarations or hollow definitions. The helper arguments establish stalk linearity, transport of maximal-ideal membership, and tensor-power isomorphisms directly, and the main theorem applies the inverse isomorphism for the converse.

3. **New or split statements.** No public statements were split off and no new DAG nodes were added. The private helpers are proof-local and introduce no library interface. The existing target statement remains exactly the original ampleness-invariance claim. Checked degree zero (the unit object), identity isomorphisms, zero sections and zero stalk modules (both nonvanishing predicates are false), and the empty scheme (the pointwise obligation is vacuous).

4. **Pruning and route.** Confirmed the proof needs only `Sheaf.AlgebraicGeometry.Ample`; the removed tensor-product and ring-valued stalk-functor imports are unused. The recorded `proof_deps` and proof steps now match the actual route through `tensorPow`, stalk germs, and `IsAmple`. An independent search of the source tensor-power API and Mathlib stalk module API found no shorter applicable iso-transport result: Mathlib supplies germ scalar compatibility, while the source relative ampleness predicate differs from this absolute predicate. The unit route remains intact because this item is not a realized unit statement or step.

5. **DAG and report consistency.** Checked the item node, its proof/proof_deps/proof_origin, and the unit record against the delivered Lean proof and report. The sole original hole is closed, no holes are added, and no target or definition is changed.

Changed during second reading: appended this review section only; no Lean or DAG repairs were needed.
