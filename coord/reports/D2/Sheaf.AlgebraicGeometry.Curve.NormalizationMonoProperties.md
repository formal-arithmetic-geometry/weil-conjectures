## What changed

`AlgebraicGeometry.normalization_mono_properties` now has a complete Lean proof with its
original signature. Proved private helpers for constructibility of the constant quotient
sheaf, constructibility of its open extension, and finiteness of open-extension geometric
stalks. Retained proof-only imports of `OpenClosed`, `KernelCokernel`, and `FiniteComparison`;
added `IdealSheaf.Subscheme` and two new intermediate modules as proof-only imports. The item’s public imports were preserved.

The proof constructs source and target constructibility instances, applies the existing
constructible cokernel theorem, and proves vanishing by finite-stalk bijectivity. Exact
pullback and stalk functors preserve the monomorphism; equivalent finite stalk sets turn
the injection into a bijection. Stalk conservativity gives an isomorphism after pullback,
and preservation of cokernels identifies the restriction with the zero cokernel of an epi.

## Proved and sorry left

Proved `AlgebraicGeometry.normalization_mono_properties` (node
`lem-weil-pbc-normalization-mono-cokernel`), plus all three private helpers. There is no
`sorry` in the item's module.

Two new public theorems remain with exactly `:= by sorry`:

- `AlgebraicGeometry.finite_pushforward_open_constantModSheaf_constructible`, node
  `lem-weil-pbc-finite-pushforward-open-quotient-constant`, module
  `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant`.
- `AlgebraicGeometry.normalization_comparison_on_iso_locus`, node
  `lem-weil-pbc-normalization-comparison-on-iso-locus`, module
  `Sheaf.AlgebraicGeometry.Curve.NormalizationComparisonOnIsoLocus`.

Neither new theorem mentions α or its cokernel. The first proves constructibility of the
middle comparison term; the second identifies the objects over V without claiming that any
map between them is invertible. Both have source citations and complete proof plans.
Edge cases checked: empty opens, empty schemes, zero quotient ring, and arbitrary infinite Λ
with finite Λ/(ℓ). Density and the primality assumption are preserved in the item signature,
but the local finite-stalk argument needs neither.

Local compilation of all three modules succeeds. The delivery dry run provides the server
compile and the project's axiom and static checks. The two intermediate theorems remain
proof obligations; this delivery does not claim a sorry-free transitive closure.

## No longer needed

All three original public imports are preserved. Five original proof imports were removed:
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian`,
`WeilConjectures.ConstructibleSheaf.Defs`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and
`WeilConjectures.SixFunctors.Finite.BaseChange`.
The last three are supplied transitively by retained imports. Every retained proof import
is used. The second reader also removed the unused public import of
`WeilConjectures.ConstructibleSheaf.Defs` from the new comparison-object module. `prop-weil-pbc-inverse-image-modules-exact` and its module
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` are not needed on this branch:
the native `Etale.upperStar` exactness/preservation instances already provide the necessary
monomorphism and cokernel preservation for ModuleCat sheaves.

`lem-weil-pbc-finite-pushforward-constructible-noetherian`,
`lemma-weil-pbc-finite-exchange`, `lemma-constructible-pullback-constant`, and
`lemma-weil-pbc-finite-pushforward-extension-zero` are no longer direct dependencies of this
item. The first three remain relevant below the two new nodes; no global pruning is claimed.
The `FiniteComparison` module remains used for its extension-by-zero stalk formulas.
The unit `sk-thm-p1` route is retained; none of its realized statements or steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan's finite-pushforward constructibility declaration is for an abelian sheaf whose
underlying set sheaf has finite constructible stalks. It cannot directly supply the desired
ModuleCat constructibility instance for an arbitrary Λ. The bridge through the finite
quotient ring, including simultaneous trivialization of its operations, is now isolated in
a new node. The isomorphism of comparison objects on V also needs substantial base-change
glue, isolated in a second node. Both follow the existing source plan without changing any
statement or definition.

Mathlib search: LeanSearch returned an Internal Server Error. LeanFinder returned generic
etale/presheaf/condensed results and no exact comparison or constructibility result. Loogle
found `Function.Injective.surjective_of_finite`, which is used in the proof. Repository grep
found the existing open-extension and cokernel theorems and the geometric-stalk formulas.

## New nodes

`lem-weil-pbc-finite-pushforward-open-quotient-constant`: constructibility of ν_*j_!Λ/(ℓ)
over a Noetherian base. Its module is
`lean/Sheaf/AlgebraicGeometry/Curve/FinitePushforwardOpenQuotientConstant.lean`.

`lem-weil-pbc-normalization-comparison-on-iso-locus`: isomorphism of the two comparison
objects restricted to V, without a map hypothesis or any coefficient finiteness assumption.
Its module is `lean/Sheaf/AlgebraicGeometry/Curve/NormalizationComparisonOnIsoLocus.lean`.

The existing item's node now records the Lean proof route and these two dependencies.
No change record is needed: no existing public signature or definition was changed.

## Second reading by D2

1. Compared the delivered item with the repository using `diff`. Its theorem signature
   and existing docstring are byte-for-byte unchanged; no existing definition changed.
   The two additional modules contain new statements only. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`. The item and its three private
   helpers contain no sorry. The only two sorries are the public theorems listed above.
   A scratch copy with `#print axioms` for all six declarations showed only `propext`,
   `Classical.choice`, and `Quot.sound` for the private helpers; the item and two split
   theorems additionally use `sorryAx`, as expected from the two open obligations.
   There are no forbidden declarations or hollow definitions. Verdict: pass as a partial
   proof, not a proof with a sorry-free dependency closure.
3. Read both split statements, docstrings and nodes. For finite pushforward, finiteness
   of Λ/(ℓ), not of Λ, justifies refinement to trivialize every coefficient operation;
   finite morphisms preserve Noetherianity of the source. For the comparison, restriction
   of ν to V being an isomorphism and the Cartesian square identify the open pieces;
   arbitrary coefficient rings work. Empty opens/schemes, the zero quotient, V empty,
   and ν an identity all satisfy the conclusions. Neither statement restates the mono
   cokernel item: neither mentions α, its monicity, or its cokernel. Independent
   LeanFinder, Loogle and Mathlib/repository grep found no exact replacement; existing
   finite exchange, finite-open comparison and constant pullback supply components,
   not the entire missing glue. Neither obligation closes in a few routine steps.
   Verdict: both are true intermediate obligations with complete prose arguments.
4. Read the proof from the theorem downward. It uses native exactness instances,
   constructible cokernel closure, finite source stalks, the comparison-object iso,
   injective-implies-surjective for equivalent finite sets, stalk conservativity and
   preserved cokernels. All five removed old proof dependencies are named under
   `No longer needed`. Checked `dag/units/sk-thm-p1.json` realized statement and steps:
   this reduction is below their level and bypasses none. Verdict: pass.
5. Compared the original and delivered node records and checked each dependency’s
   recorded Lean declaration. The item’s proof steps and dependency union match the
   Lean; both new nodes have source, proof, search, creation, blueprint and Lean records.
   Removed unused statement dependencies from the new nodes (constructibility from
   the comparison node, inverse image from the finite-pushforward node). Verdict: pass.

Changes by this reading: corrected the removed-import inventory, removed the unused
constructibility import from the new comparison module, gave the two new module
headers specific titles and source/blueprint references, removed two irrelevant new-node
statement dependencies, and recorded independent searches. The mathematical proof and
all theorem statements were retained.
