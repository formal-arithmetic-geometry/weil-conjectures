## What changed

Proved `AlgebraicGeometry.Scheme.exists_dense_open_lisse_finite_source` with its
signature unchanged. Unpack the original lisse stratification and use the union
of its stratum interiors. Remove the closed image of the complement to obtain
the dense base open, then apply the existing abelian pullback-preservation theorem.
Added proof imports of `FiniteGenericFiberStratumInteriors`, `LisseStratumInteriors`
and `PullbackFiniteLocallyConstant`; no public import of the original module changed. Removed the proof imports
of `EtaleInverseImageAlgebraicStructures`, `IrreducibleLisseStrata` and
`UniversalHomeomorphismInvariance` from the target module; their necessary
sheaf-theoretic content is retained in the new gluing node's proof plan.

The new module `FiniteGenericFiberStratumInteriors` proves that the generic fibre
lies in those interiors. Its proof uses Mathlib's discrete fibres of finite maps,
Noetherian source, generic points of components, and locally closed strata.
The new module `LisseStratumInteriors` isolates the finite-set-stalk gluing argument.
The target's node now records this route and its actual dependencies.

All three sandbox modules compile. Edge cases checked: empty source or generic
fibre (the pointwise assertion is vacuous and the remaining open restriction may
be empty), identity map, finite disjoint unions, nonreduced source, and vertical
components. No reducedness or dominance hypothesis was added. In particular,
image containment in a stratum is handled by a fibre product, not by asserting
a scheme factorization through its possibly different scheme structure.

## Proved and sorry left

- Proved the original `AlgebraicGeometry.Scheme.exists_dense_open_lisse_finite_source`
  (node `lem-weil-pbc-finite-source-generic-lisse`): no sorry remains in its module.
- Proved `AlgebraicGeometry.Scheme.generic_fiber_subset_stratum_interiors`
  (node `lem-weil-pbc-finite-generic-fiber-stratum-interiors`): no sorry in this module.
- One new sorry remains: `AlgebraicGeometry.Scheme.lisse_on_stratum_interiors`
  (node `lem-weil-pbc-lisse-stratum-interiors`). This statement has no finite map,
  integral base or dense-open conclusion: it is only the sheaf-theoretic gluing
  part. Its source and complete proof are in its docstring and node.

The existing imported `pullback_finite_locally_constant` remains an upstream item;
its sorry is unchanged by this delivery.

## No longer needed

Removed proof imports from the target module:
`Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`,
`Sheaf.AlgebraicGeometry.IrreducibleLisseStrata`, and
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`.
All original public statement imports are unchanged.
The proof no longer needs `lem-weil-pbc-irreducible-lisse-strata` or its module
`Sheaf.AlgebraicGeometry.IrreducibleLisseStrata`. Its refinement branch
`lem-weil-pbc-irreducible-refinement` /
`Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement` is likewise unnecessary for
this proof. The original stratification suffices.

The finite-type/Noetherian and finite-components nodes remain needed in the proved
topological helper. Universal-homeomorphism invariance and the inverse-image/forget
comparison remain needed in the lissity helper's fibre-product argument; they are
no longer used to reduce the entire source before the generic-fibre argument.
Finite integrality, closedness, and pullback preservation remain used by the target.

## Where the brief, the DAG or earlier work was wrong

The original generic-fibre argument hid the incomparability/Artinian calculation
and the assembly of lisse open neighbourhoods. Mathlib's finite-fibre discreteness
closes the point-identification directly, and locally closedness of the original
strata gives the neighbourhoods without irreducible refinement or source reduction.

The proved source-library generic-constancy theorem has a Grothendieck abelian
coefficient interface with finitely generated stalks. It cannot simply be applied
to the set-valued finite-stalk predicates here. The new gluing statement retains
finite underlying sets rather than replacing them by finitely generated groups.
The raw blueprint Markdown is absent from this clone; the proof paragraphs preserved
in the DAG and the source-library generic-constancy/refinement proofs were read.
No target statement or definition changed; the unit realization has no steps to bypass.

## New nodes

`lem-weil-pbc-finite-generic-fiber-stratum-interiors`, in
`dag/nodes/sec-smooth-purity/lem-weil-pbc-finite-generic-fiber-stratum-interiors.json`,
records the proved generic-fibre topological assertion in
`lean/Sheaf/AlgebraicGeometry/FiniteGenericFiberStratumInteriors.lean`.

`lem-weil-pbc-lisse-stratum-interiors`, in
`dag/nodes/sec-smooth-purity/lem-weil-pbc-lisse-stratum-interiors.json`, records the
remaining lissity gluing assertion in
`lean/Sheaf/AlgebraicGeometry/LisseStratumInteriors.lean`. Blueprint searches found
no exact duplicate; `prop-constructible-generic-constancy` is related but its Lean
interface requires abelian coefficients and uses different stalk finiteness.
No change record is needed, because existing statements and definitions are unchanged.

## Second reading by J2

1. Compared the target module against the repository version with `diff`.
   Its declaration signature, definitions, and public imports are byte for byte
   unchanged. Only its proof and proof imports change. The two helper modules
   are new, with signatures matching their node records. Verdict: pass.
2. Compiled all three modules in import order with `lcompile.py --all`.
   The target and generic-fibre helper have no sorry; the only new sorry is
   the named `lisse_on_stratum_interiors`, documented above and in its node.
   No forbidden declaration or hollow definition occurs. The axiom probes
   show only `propext`, `Classical.choice`, and `Quot.sound` for
   `generic_fiber_subset_stratum_interiors`; the target and gluing lemma
   additionally use `sorryAx`, as expected from the reported open statements. Verdict: pass, subject to the explicitly open gluing
   and existing pullback-preservation statements.
3. Read both new statements and their natural-language proofs. Finite fibres
   are discrete, so a generic-fibre point is a component generic point; the
   coborder argument then supplies an actual ambient open neighbourhood.
   The gluing lemma has neither a finite morphism nor a generic/dense-open
   conclusion and is strictly the sheaf part of the reduction. A surjective
   immersion is closed; its fibre-product construction avoids an unjustified
   factorization through a stratum's scheme structure. Checked empty source,
   empty fibre, identity map, nonreduced strata and vertical components.
   Searched with distinct queries for descent along open covers, constant
   sheaves and isomorphisms using leanfinder, loogle, grep, and `rg` in the
   library. The source-library generic-constancy and immersion-independence
   results require abelian local constancy and finitely generated stalks;
   they do not directly state finite underlying-set stalk lissity. Verdict:
   no false or duplicate split statement found.
4. The proof uses the original stratification, Mathlib's finite-fibre
   discreteness, closed-image shrinking and the existing pullback theorem.
   Public imports of the new helpers supply names in their signatures;
   QuasiFinite is a plain proof import. The updated pruning section now names
   all removed proof imports and all old dependencies absent from the new
   target proof; dependencies retained through the helper plans are explained.
   The unit `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`,
   so no realized unit route is bypassed. Verdict: pass.
5. Checked node statements and Lean signatures, proof steps and unions of
   dependency lists, sources, origins, search records, creation records,
   blueprint links, chapter and unit. The generic-fibre node records the
   Mathlib topological argument; the gluing node records the remaining
   sourced sheaf argument. Verdict: pass.

Changed only this report: corrected its outdated assertion that no original
proof imports were removed, and recorded this independent reading. Tried the
existing `finite_local_abelian_forget_iff` to combine the source library's
abelian gluing proof with finite-stalk identifications. Its module has no
compiled object in the last green library on this machine, so the local
compiler refuses the import. Reverted that attempted proof and left the
original, truthful split statement; no replacement lemma was introduced.
