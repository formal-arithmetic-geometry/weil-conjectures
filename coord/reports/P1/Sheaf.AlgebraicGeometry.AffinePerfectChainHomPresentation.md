## What changed

Replaced the earlier attempt's invalid `True`-hypothesis restatement with two separate
parts of the affine calculation. The existing declaration
`AlgebraicGeometry.exists_affinePerfectChainHomPresentation` retains its complete
signature and is proved by combining the scalar-extension Hom diagram with the
module-to-geometric Hom comparisons. The stage equivalence is `ident.trans stage`;
the limit equivalence is `e.trans limit`. `congrArg` applies the geometric equivalence
to each algebraic compatibility equation, and `Equiv.apply_symm_apply` cancels the
intermediate identification. All four equations in the original statement are supplied.

Added `ScalarExtensionChainHomDiagram.lean` for the purely module-theoretic diagram
construction and `AffinePerfectChainGeometricModels.lean` for affine bounded projective
models and the geometric comparison. No data is selected from an unproved existence
theorem inside a definition: the final construction eliminates existentials in a
proof. No existing signature, definition, public import, or visibility is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_affinePerfectChainHomPresentation`
(node `lem-pc-affine-perfect-chain-hom-presentation`). Its proof is complete.

The remaining affine construction is
`AlgebraicGeometry.exists_affinePerfectChainGeometricModels`
(node `lem-pc-affine-perfect-chain-geometric-models`), with proof exactly `by sorry`.
It constructs finite-projective models and direct module/geometric equivalences, with
two compatibility equations; it does not construct H, its functor laws, d, its
naturality, or the algebraic diagram-identification equations.

Also proved `AlgebraicGeometry.exists_scalarExtensionChainHomDiagram`
(node `lem-pc-scalar-extension-chain-hom-diagram`) without sorry: the diagram is
constructed from homotopy Hom sets, lifted to the required universe. Tensor
associator unit and composition equations give the functor and cocone laws, and
Mathlib's K-projective localization bijection gives the two derived Hom
equivalences and their chain-map equations. K can be arbitrary; only the
bounded projectivity of E is used.

Holes closed: 1 original. Holes added: 1, the geometric-model theorem above.
This is a decomposition, with net hole delta 0, plus a proved generic algebraic
construction. The item's module itself has no sorry. No other delivered theorem
has sorry. All three delivered modules compile together in import order without warnings
through lcompile.py (12.8 s, 8.2 s and 15.9 s reported). The original theorem's
signature was compared byte-for-byte with the repository and is identical.

## No longer needed

Removed the eight direct proof imports from the item: PerfectImpliesQCoh,
AffineDerivedPullbackTensorTilde, AffineQCohDerivedEquivalence,
PerfectAffineBoundedProjective, SchemeIsoPerfectTransport,
SchemeIsoDerivedLocalizations, SchemeIsoDerivedEquivalence and SchemeIsoDerivedQCoh
(all under Sheaf.AlgebraicGeometry). They remain proof dependencies/imports of
AffinePerfectChainGeometricModels; this is relocation, not pruning from the target
closure. No original node or module is claimed pruned. No unit statement or proof
step is bypassed.

The earlier sandbox-only `exists_affinePerfectChainHomPresentation_with_extra` is
removed. It was never a genuine reduction or a library dependency.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox theorem added only `h : True` to the original statement. Applying
it with `trivial` moved the entire hole and did not prove any part of the argument.
The prior claim that smaller intermediate statements cannot be expressed is incorrect:
the algebraic diagram and geometric chain-map comparison have now been stated
separately, and the original conclusion is assembled by a compiling Lean proof.

The original DAG plan remains the mathematical route, with its coordinate diagram,
affine bounded-projective criterion, tilde pullback naturality and counit-pinned
composition comparisons. Those geometric steps are documented in the new node and
its theorem docstring. The unit record has no realized node that this change bypasses.

Edge cases were checked mathematically: zero rings and zero complexes require no
nonempty points; the tail contains its initial object i; a singleton tail still has
the identity and cocone equations; arbitrary transition ring maps need not be flat
because the complexes' projective terms compute derived extension. The generic
scalar diagram needs neither geometry nor directedness and asserts no Hom descent.

LeanFinder and Loogle searches found ordinary scalar-extension functors and the
K-projective localization bijection, but no affine combined comparison. Mathlib and
project grep located scalar coherence and homotopy/K-projective helpers. LeanSearch
returned Internal Server Error; this is recorded without a negative mathematical
verdict. The local Stacks source is absent on this machine, so the sources were read
online: [09RE](https://stacks.math.columbia.edu/tag/09RE),
[08EB](https://stacks.math.columbia.edu/tag/08EB) and
[08DW](https://stacks.math.columbia.edu/tag/08DW).

## New nodes

`lem-pc-affine-perfect-chain-geometric-models`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-perfect-chain-geometric-models.json`,
is the coordinate-ring/model construction and the geometric part of the comparison.
Its Lean module is `Sheaf.AlgebraicGeometry.AffinePerfectChainGeometricModels`.

`lem-pc-scalar-extension-chain-hom-diagram`, in
`dag/nodes/sec-picard-framework/lem-pc-scalar-extension-chain-hom-diagram.json`,
is the generic diagram and cocone for module-derived Hom sets with bounded
finite-projective source and arbitrary target. Its Lean module is
`Sheaf.AlgebraicGeometry.ScalarExtensionChainHomDiagram`. It is independent of the
geometric-model node, so neither intermediate repeats the complete target.

The parent node's proof and proof_deps now record the actual Lean assembly from
these two parts. No change record is needed: existing interfaces remain identical.

## Second reading by P1

1. Compared the delivered parent module with the repository version. The theorem
   signature is byte-for-byte unchanged; only its proof and proof-only imports differ.
   The two added modules and node files are new declarations with matching signatures.
   Verdict: passed.
2. Compiled all three delivered modules with `lcompile.py`; there are no errors,
   forbidden declarations, or accidental `sorry`s. The sole remaining `sorry` is the
   named geometric-model theorem and is documented above with its node. Verdict: passed.
3. Checked the split statements against their docstrings, edge cases, and searches
   recorded above. The scalar diagram is strictly algebraic, while the geometric
   theorem contains only the affine model/comparison portion. Neither restates the
   parent target. Verdict: passed.
4. The parent proof follows the two split declarations and assembles the four
   required equations by equivalence composition and `congrArg`; no shorter existing
   declaration was found. Removed imports are listed above, and the unit route is
   preserved. Verdict: passed.
5. DAG `proof`, `proof_deps`, `proof_origin`, and both new node records agree with
   the Lean declarations and actual proof dependencies. Verdict: passed.

Independent scratch `#print axioms` checks show only `propext`, `Classical.choice`
and `Quot.sound` for the scalar diagram. The parent and geometric obligation also
use `sorryAx`, as expected from the remaining geometric hole. Fresh LeanFinder search
for affine finite-projective models and compatible derived base-change morphisms
returned ordinary affine scheme results, not this comparison. Fresh Loogle search
for `CochainComplex.IsKProjective` and project grep found the existing K-projective
tools and individual affine model results, with no combined geometric statement.
The unit's realized statement and step lists are empty; no realized step is bypassed.

This second reading changed only the report, recording the independent checks.
No Lean or DAG repair was necessary, and no additional hole was closed or added.
