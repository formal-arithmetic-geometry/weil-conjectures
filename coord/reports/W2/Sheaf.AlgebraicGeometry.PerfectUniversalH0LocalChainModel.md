## What changed

Proved the specified-arrow part of
`Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel`, with its public signature
unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel`,
`Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
The proved private helper `bottom_component_isIso` recovers invertibility of the
middle component from invertibility of homology when both differentials vanish.

The source complex is the actual construction `single(B.X 0)`. Exact restriction
and its homology comparison identify the restricted M with B.X 0. Its finite-free
retract comes from B's strict perfectness. The affine representative theorem gives
an actual representative of the conjugated specified arrow; the homology comparison
and zero-differential calculation prove its degree-zero component invertible.
Isomorphism cancellation proves the square for the original a.

Added `Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel`, isolating the endpoint
model construction from steps 1 and 2 of the original plan. It contains neither M,
a, H0(a), a source complex, a representing chain map, nor the compatibility square.
The original DAG node records this reduction and the proved arrow argument.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.perfect_universalH0_local_chain_model`
(node `lem-sc-perfect-universal-h0-local-chain-model`); no sorry remains in the item.
The private `bottom_component_isIso` is proved without sorry.

Added one smaller hole:
`AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model`
(node `lem-sc-perfect-universal-h0-bottom-model`), in the new module
`Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel`.
This is a decomposition, not a net reduction in the number of holes: one closed,
one added. The remaining geometric work is residue-model shrinking and vanishing
of the outgoing differential by the injective-square-matrix argument. The specified
source and arrow argument is complete.

The two modules compile locally; the delivery dry run checks the axiom probe.
No arbitrary existential witness is used to define public data: B is obtained
inside a theorem proof, and A is explicitly constructed from B.X 0.

## No longer needed

No original import was removed. No module or node is pruned globally.
`lem-pc-perfect-affine-map-representative` remains directly used.
`lem-sc-perfect-finite-free-residue-model`,
`lem-pc-derived-pullback-open-restriction-universes`, and
`lem-sc-square-injective-free-map-dual-coker-zero` move from direct planned proof
dependencies of the item to the new bottom-model node's proof dependencies.
They remain needed for the same geometric steps and are not claimed as pruning.
The square-map node is already a Mathlib composite rather than a Sheaf module.
No unit-level statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical dispute or signature change. The planned geometric facts are
sufficient in meaning, but their existing interfaces do not package the shrinking,
rank comparison, localized homology identification, and square-matrix calculation
as a bottom-model theorem. The new node states precisely those first two steps.

The arrow step needs no further trivialization of M: strict perfectness only asks
for finite-free retracts, and B.X 0 supplies such a retract. The exact-functor
homology comparison already exists and is proved upstream. Both facts are used
instead of adding separate source-model or homology-comparison holes.

Edge cases: rank zero gives a zero degree-zero term in the geometric argument;
empty schemes have no point s. The arrow proof also handles zero terms by isZero,
uses no nonzero-rank assumption, and works for arbitrary localization universe w.
The geometric docstring uses the injective-square argument over arbitrary rings,
so it introduces no reducedness assumption. Stacks Tags 0BDL, 0BCD, and 0EWY were
checked against their published text.

## New nodes

`lem-sc-perfect-universal-h0-bottom-model`,
`dag/nodes/sec-abelian-varieties/lem-sc-perfect-universal-h0-bottom-model.json`,
records the endpoint-only affine bottom-model existence statement in
`lean/Sheaf/AlgebraicGeometry/PerfectUniversalH0BottomModel.lean`.
Its full proof in words is steps 1 and 2 of the original model plan, from Stacks
Tags 0BDL, 0BCD, and 0EWY. Recorded searches include unavailable LeanSearch,
LeanFinder, Loogle, and Mathlib grep; none gives the scheme-level statement.
Blueprint searches for perfect/universal and lowest found no duplicate statement.
No change record or forced adaptation is needed: all existing signatures,
definitions, and public imports are unchanged.

## Second reading by W2

1. **No accidental interface changes.** Compared the delivered local-chain module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, the proof body, and the separately documented new bottom-model module were added.

2. **Compilation and proof hygiene.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The target theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The only remaining `sorry` is the named bottom-model theorem, with its source, docstring, and DAG node recorded. The proof uses only ordinary classical/category-theoretic instances; no arbitrary witness is used to define public data.

3. **Statements and split-off node.** Checked the bottom-model statement against the endpoint construction required by the source plan. It is strictly smaller than the target: it contains only the affine endpoint model and omits M, the specified arrow, and the compatibility square. Its hypotheses and conclusion are unchanged from the delivered node and the docstring gives the complete matrix-chart argument. Searches recorded in `searches.jsonl` found no existing equivalent declaration.

4. **Route and pruning.** The proof follows the unit route: first the endpoint bottom model, then exact restriction and homology transport, then the affine chain-map representative, then the zero-short-complex homology calculation. No unit-level step is bypassed. All original public imports remain needed; the added imports are proof-only except for the new bottom-model module's public dependencies.

5. **DAG agreement.** The local-chain node's proof steps and `proof_deps` match the Lean proof, including the new bottom-model node and the affine representative node. The bottom-model node records its source, proof origin, Lean declaration, and split status. No statement dispute or forced adaptation was found.

I changed only this report section during second reading; no Lean statements or proofs required repair after compilation.
