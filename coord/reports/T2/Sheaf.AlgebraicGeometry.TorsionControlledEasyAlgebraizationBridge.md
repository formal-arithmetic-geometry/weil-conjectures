## What changed

Completed a genuine decomposition of `Sheaf.AlgebraicGeometry.TorsionControlledEasyAlgebraizationBridge`.
The original declaration and docstring are unchanged. Its proof now constructs the coherent
restrictions on the affine-open cover, restricts the formal source, transports the given bound
through a quotient-projection-normalized comparison, applies affine algebraization on each open,
and passes the resulting local triples to descent. The underlying natural-transformation equation
is extracted from the full-subcategory factorization by `congrArg`; no hole remains in the assembly.

Added three modules, one statement each: `TorsionControlledFormalRestriction`,
`TorsionControlledAffineAlgebraization`, and `TorsionControlledAlgebraizationDescent`.
All added imports in the bridge are plain proof imports. There are no definition or existing
signature changes, forced adaptations, or change records. Updated the bridge node's proof,
proof_deps and proof_origin to describe the assembly actually performed in Lean.

## Proved and sorry left

Hole closed in the item: `AlgebraicGeometry.torsionControlled_easy_algebraization_bridge`,
node `new-stage3-torsion-controlled-easy-algebraization-bridge` (1 of 1).
This is a decomposition, not a complete axiom-free proof of algebraization.

Holes added, each the entire proof of one public theorem in its own module:

- `AlgebraicGeometry.torsionControlled_formal_restriction`, node
  `lem-weil-pbc-torsion-controlled-formal-restriction`: only the canonical open restriction
  dictionary and transport of the original bound; constructs no algebraization.
- `AlgebraicGeometry.torsionControlled_affine_algebraization`, node
  `lem-weil-pbc-torsion-controlled-affine-algebraization`: only the affine construction;
  assumes IsAffine and performs no descent on a nonaffine scheme.
- `AlgebraicGeometry.torsionControlled_algebraization_descent`, node
  `lem-weil-pbc-torsion-controlled-algebraization-descent`: only descent, assuming actual
  local triples. It does not derive any local algebraization from formal torsion.

Three holes added, one closed, net -2. The coherence locality and formal restriction object
property are existing named dependencies, not new holes of this delivery. Full-library theorem
axioms still include the existing and new pending proofs. No data definition uses a new hole.
The comparisons chosen inside the proof are determined by their quotient-projection equations.

## No longer needed

No baseline import was removed: the baseline contained only the statement import
`Sheaf.AlgebraicGeometry.CoherentFormalModule`, which is necessary. No existing module is
claimed to be pruned from the targets' closure. Removed from the bridge's direct `proof_deps`: `lem-weil-pbc-formal-systems-annihilated-by-power`.
It remains used inside the affine construction plan and is not globally unnecessary. The finite-cover/common-exponent step is isolated in
descent, while the bridge uses all affine opens and their Mathlib covering theorem.

The cyclic parent `Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationConstruction`
and `GrothendieckExistenceEasyTorsionTriple` are not imported. The earlier duplicate
`TorsionControlledEasyAlgebraizationBridgeLocal` remains excluded from the delivery.
No unit statement or realized step of `sk-thm-p1` is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old bridge node listed only the annihilation equivalence for its affine construction,
gluing, and common-exponent argument. That equivalence supplies no algebraization or descent;
the new nodes expose these genuine steps and name the existing ring-level and gluing tools.
The previous local-input helper duplicated the full global construction theorem and was rejected.
None of the three new assertions has that signature: one contains no algebraization conclusion,
one assumes an affine scheme, and one assumes already constructed local triples.

Canonicality is essential in descent. Arbitrary local isomorphisms between restriction of completion
and completion of restriction could twist the maps to H. The new restriction theorem records the
quotient-projection equations, and descent explicitly requires them. The assembly supplies those
equations. On overlaps use uniqueness of torsion-controlled triples, not faithfulness of completion
on arbitrary coherent modules. Intersections of affine opens need not be affine; descent is stated
for all opens and uses the existing global lifting/extensionality tools on their Noetherian schemes.

Checked empty opens and empty schemes, zero ideals, and unit ideals. For a unit ideal the torsion
condition forces kernels and cokernels to vanish, and the identity triple works; unrestricted triple
uniqueness is not asserted. For a zero ideal completion is the constant identity system. The
restriction bound is unchanged and can even be zero. Descent uses a finite subcover and maximum
with 1, including the empty-subcover case.

Read Stacks https://stacks.math.columbia.edu/tag/0889 and
https://stacks.math.columbia.edu/tag/0ALK; the local literature/stacks-project/coherent.tex
is absent on this machine. WANTED: that source for the affine and descent nodes. LeanSearch
was attempted and returned an internal server error, recorded as unavailable. LeanFinder and
Mathlib/source rg searches found no exact replacement. Existing exact global shortcuts are cyclic.

## New nodes

`lem-weil-pbc-torsion-controlled-formal-restriction` corresponds to
`lean/Sheaf/AlgebraicGeometry/TorsionControlledFormalRestriction.lean`. Its quotient equations
specify the comparison and its bound clause is only transport under open restriction.

`lem-weil-pbc-torsion-controlled-affine-algebraization` corresponds to
`lean/Sheaf/AlgebraicGeometry/TorsionControlledAffineAlgebraization.lean`. Its plan uses the
existing affine equivalence, annihilation equivalence, formal-gluing isogeny and finiteness criterion.

`lem-weil-pbc-torsion-controlled-algebraization-descent` corresponds to
`lean/Sheaf/AlgebraicGeometry/TorsionControlledAlgebraizationDescent.lean`. Its plan uses the
existing completion-map lifting and extensionality tools for unique overlap isomorphisms,
sheaf descent, local coherence, and finite-cover annihilation. No change record is needed.

## Second reading by T2

1. Compared the delivered bridge with the repository version using `diff -u`: its existing
   declaration signature and docstring are byte for byte unchanged. The only code changes
   are five plain proof imports and the proof replacing `sorry`. The three added modules
   contain only new theorem statements; there is no changed definition or change record.
   Verdict: pass.
2. Compiled all four modules in import order with `lcompile.py --all`; all compiled without
   errors or warnings. A scratch copy of the actual delivered bridge, with `#print axioms`
   for all four declarations, compiled and printed only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. Exactly the three reported public theorems retain `sorry`;
   no prohibited declaration or hollow definition occurs. The chosen gamma is determined
   componentwise by its equation after the epimorphic quotient projection; Hlocal and
   Nlocal are actual restrictions, not arbitrary existence witnesses. Verdict: pass as
   a decomposition, not as an axiom-free proof.
3. Read all three new signatures, docstrings and nodes against Stacks Tags
   [0889](https://stacks.math.columbia.edu/tag/0889) and
   [0ALK](https://stacks.math.columbia.edu/tag/0ALK). Restriction constructs no triple;
   affine construction assumes IsAffine; descent assumes actual local triples. Thus none
   merely renames the full bridge. Checked zero and unit ideals, zero modules, empty opens
   and empty schemes: zero-ideal completion is identity; unit-ideal formal objects vanish
   and the identity triple works; restriction permits t=0; empty descent takes bound 1.
   Descent needs no affineness of intersections. Read the exact hom-lift-exists and
   torsion-completion-ext statements: maps respecting H and completion lift, and both
   data together give uniqueness. Searched independently through msearch LeanFinder,
   Loogle and grep, and rg over Sheaf/WeilConjectures. The proved general formal pullback
   theorem supplies an isomorphism but does not expose the required quotient-normalization
   equation. The proved idealPowerProduct_restrict_isZero_iff supplies a part of bound
   transport, not the complete restriction assertion. Global construction shortcuts import
   this bridge and are cyclic. No complete split theorem could be closed in a few minutes
   from these public interfaces. Verdict: the three sourced, strictly smaller holes are valid.
4. Read the assembly top down: coherence locality constructs Hlocal, formal restriction
   constructs Nlocal, the canonical gamma transports the original exponent, the affine
   theorem supplies local triples, and congrArg extracts exactly the descent equation.
   Every proof import is used, and the sole public import is required by signatures.
   Read sk-thm-p1.json `realized`: this delivery changes none of its realized statements
   or steps and only decomposes a lower algebraization tool. Corrected No longer needed
   to explicitly list the removed direct annihilation dependency; no module is pruned.
   Verdict: pass.
5. Checked each delivered node against its Lean declaration, and checked that proof_deps
   equals the union of the steps' uses. The bridge's five dependencies match its actual
   proof. New nodes have source, full proof plan, search records, provenance, chapter,
   unit, creation and Lean fields. Replaced the three normalized single-line Lean statement
   records with verbatim multiline signatures. Existing tower-limit DAG cycles are reached
   through the affine annihilation dependency: tower-limit-exact-surjective-kernels ->
   new-tower-limit-induced-maps -> tower-limit-exact-surjective-kernels, and the analogous
   cycle through new-tower-limit-exact-coordinate-maps. Neither cycle contains a new node
   or a modified edge of this delivery; this is reported for maintainer repair. Verdict:
   delivered node/Lean agreement passes; the pre-existing DAG issue remains upstream.

Second reading changed only this report and the formatting of the three new nodes' Lean
signature records. No Lean proof or statement repair was necessary. One item hole closed,
three named holes added, net -2; the delivery remains explicitly a decomposition.
