## What changed

Implemented `WeilConjectures.scalarPullbackTower_existsUnique` and
`WeilConjectures.scalarTensorTower_existsUnique` without changing their statements,
normalization predicates, or definitions. A proved private generic helper factors out the common tower assembly and avoids
expanding the concrete finite-operation data in each naturality proof. Each proof
applies the finite-level
normalization specifications, constructs all tower components with
`NatTrans.ofOpSequence`, proves naturality in the input complexes, and proves
uniqueness by componentwise extensionality.

The generator calculations for consecutive reductions are isolated as two
strictly smaller public lemmas in separate new modules, imported privately by
the item. Neither new lemma asserts existence or uniqueness of a tower map.
The original node records the two actual assembly proofs and their dependencies.

For the per-file compile limit, the already complete ordinary tensor chain proof
is extracted into `NormalizedIntegralOrdinaryTensorChain`. The existing complete
internal-Hom completeness proof and its three private helpers are likewise moved
to `IntegralScalarInternalHomComplete`. The original theorem
applies it with exactly the same normalization. Local irreducibility of
`scalarIntegralClosed` and `scalarIntegralModels` prevents repeated expansion of
large structure data; their definitions and public transparency are unchanged.

Validation: `lcompile.py --all` compiled all five modules successfully (exit 0),
including both complete extracted proofs and the item. The compiler accepted
every file under its per-file time gate. DAG proof-dependency unions and the
verbatim new theorem signatures were also checked.

## Proved and sorry left

Original holes: 7. Original holes reduced: 2. New holes: 2. Net holes closed: 0.
This is a decomposition, not a proof of either entire comparison argument.

The complete assembly proofs replace the original holes in:

- `WeilConjectures.scalarPullbackTower_existsUnique`.
- `WeilConjectures.scalarTensorTower_existsUnique`.

Five original holes remain unchanged, attached to
`lem-pur-integral-operations-scalar-extension`:

- `WeilConjectures.scalarPullbackLevel_existsUnique`.
- `WeilConjectures.scalarTensorLevel_existsUnique`.
- `WeilConjectures.scalarPullbackOrdinary_existsUnique`.
- `WeilConjectures.scalarTensorOrdinary_existsUnique`.
- `WeilConjectures.scalarOperationsOrdinary_tower`.

Two holes are added, each the entire proof of a public theorem with source,
complete proof in words, and its own node:

- `WeilConjectures.integralScalarPullbackLevelReduction`, node
  `lem-pur-integral-scalar-pullback-level-reduction`.
- `WeilConjectures.integralScalarTensorLevelReduction`, node
  `lem-pur-integral-scalar-tensor-level-reduction`.

The packet therefore has 7 holes altogether: 5 in the item and 1 in each new
module. Existing definition data is unchanged; no hole is added to a definition. Both
extracted modules retain complete proofs and add zero holes.

## No longer needed

No whole module or existing node is pruned: extracted proofs still need their
original dependencies. The following direct proof imports move out of the item
and into the extracted modules:

- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.
- `Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.Algebra.Homology.ScalarHomTensorCoherence`.
- `Sheaf.CategoryTheory.NativePrincipalCompletenessSmallModel`.
- `Sheaf.CategoryTheory.NativeRingedRestrictionDerivedHom`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
- `Sheaf.Paper.PrincipalKoszulStrictReplacement`.
- `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence`.
- `Sheaf.Paper.SfDerivedCompleteLegacyComparison`.

The following nodes cease to be direct proof dependencies of the parent; they
remain dependencies of the extracted proofs (and some remain statement
dependencies of the parent):

- `def-sfb-derived-change-of-rings-cochain-model`.
- `lem-a1-principal-koszul-strict-replacement`.
- `lem-pur-native-principal-completeness-small-model`.
- `lem-pur-native-ringed-restriction-derived-hom`.
- `lem-pur-roos-intrinsic-completeness-equivalence`.
- `lem-sf-derived-complete-legacy-comparison`.
- `lem-sf-ringed-derived-closed-symmetric-monoidal`.
- `lem-sf-ringed-finite-free-tensor-complex`.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
- `lem-weil-scalar-extension-composition`.

Existing proof plans remain for the five untouched holes. All new proof imports
are used.

## Where the brief, the DAG or earlier work was wrong

The tower proof descriptions formerly hid the separate consecutive reduction
square behind the phrase "the same generator formula". Finite-level naturality
in input complexes does not supply this coefficient-level square. The delivery
makes that exact remaining obligation explicit, while proving all the tower
assembly and uniqueness glue.

The declared dependencies were inspected before splitting. In particular,
`IntegralTensorTransitionCompatibility` concerns reduction of an ordinary tensor
at one coefficient field; it does not state the square for scalar extension
between E and L required here. Mathlib's `NatTrans.ofOpSequence` does supply the
assembly, and `NatTrans.ext` supplies uniqueness. Searches used LeanFinder,
LeanSearch, Loogle, and ripgrep in Mathlib and both project roots.

The latest blueprint's derived-operations file has moved to
`sec-proetale-coefficients/sk-prop-sf-open-closed-triangle`; the older path in the
parent node no longer exists in latest. The new nodes instead cite the available
Stacks source `sites-modules.tex`, section tensor-product, its sheafification and
pullback lemmas, and the finite quotient construction of Bhatt--Scholze 3.4.10.
No unit statement or route is changed.

## New nodes

`lem-pur-integral-scalar-pullback-level-reduction` records just compatibility of
normalized scalar pullback level maps with a consecutive quotient reduction.
The proposed argument uses the scalar and pullback adjunctions, the existing
transition generator formula, local surjectivity of the finite projection and
sheaf separatedness. It applies to zero complexes, identity coefficient maps,
ramified extensions and empty sites; it assumes no flatness or nonemptiness.

`lem-pur-integral-scalar-tensor-level-reduction` records the analogous consecutive
square for normalized scalar total-tensor maps. Its proof reduces to the two
pure tensor entries and then extends through local generation and coproducts.
The same edge cases apply. Each module contains only this one statement, and
neither imports the parent item. No change record is needed: existing public
signatures, attributes, imports, and construction data are preserved. All
transparency settings introduced in this packet are local to the item.

`lem-weil-normalized-ordinary-scalar-tensor-chain` records the extracted, fully
proved ordinary chain comparison. Its public statement displays the existing
normalization explicitly, avoiding an import cycle with the item. This adds no
holes and changes no existing signature or construction data.

`lem-pur-integral-scalar-internal-hom-complete` records the extracted, fully
proved completeness theorem. The actual ambient internal Hom and completeness
predicate are unchanged; the full existing proof, including its small-site and
local completeness helpers, is retained. This adds zero holes.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
