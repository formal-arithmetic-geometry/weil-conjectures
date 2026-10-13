## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.koszulRegularImmersion_self_ext_exterior`
with a complete Lean reduction. Its statement, universes, binders and original docstring
are unchanged. The proof obtains a global exterior-to-self-Ext morphism surjective on
stalks, chooses a regular affine chart at each point, obtains two finite stalk bases with
the same index set, and applies Mathlib
`OrzechProperty.bijective_of_surjective_of_injective`. The source-library module stalk
criterion makes this morphism an isomorphism; its inverse has the required orientation.

Added `Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection` and
`Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases`, one named theorem per module, and their
nodes. Updated the parent node's proof, dependencies and proof origin to match the Lean.
The first new theorem isolates global Yoneda generation; it does not assert injectivity.
The second is a calculation on one affine chart; it does not construct a global map or
assert compatibility of stalk bases. Their combination uses the commutative-ring Orzech
property without a Noetherian hypothesis. No object is defined using an unproved
existence theorem, and no existing interface or target statement is changed.

All three modules compile through `lcompile.py --all`, without warnings. Edge cases were
checked against the statements: empty V has no stalk obligations; degree zero uses a
singleton wedge basis and the unit product; n above the local length uses empty bases
and zero modules; length zero is included. Characteristic two is covered by contraction
squares being zero, not by deducing alternation from skew symmetry.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.koszulRegularImmersion_self_ext_exterior`
(node `lem-sc-koszul-self-ext-exterior`). No `sorry` remains in the item's module.

Added exactly two holes, each the entire proof of a public theorem:

- `AlgebraicGeometry.koszulRegularImmersion_self_ext_yoneda_surjection`
  (node `lem-sc-koszul-self-ext-yoneda-surjection`).
- `AlgebraicGeometry.koszulRegularImmersion_self_ext_stalk_bases`
  (node `lem-sc-koszul-self-ext-stalk-bases`).

This is a decomposition: one upper hole closed, two strictly partial argument statements
added. It is not claimed as a net reduction in the targets' closure hole count.

## No longer needed

Removed these seven direct proof imports from the item's module:

- `Sheaf.RingTheory.KoszulProjectiveResolution`
  (`new-j3-koszul-projective-resolution`).
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
  (`lem-sc-affine-quotient-resolution-sheafification`).
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
  (`lem-sc-derived-internal-hom-restrict-open`).
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`
  (`lem-sc-derived-hom-finite-free-model`).
- `Sheaf.RingTheory.KoszulConormalBasis` (`lem-sc-koszul-conormal-basis`).
- `Sheaf.AlgebraicGeometry.AffineConormalFrame` (`lem-sc-affine-conormal-frame`).
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison`
  (`lem-sc-exterior-sheaf-local-free-comparison`).

These dependencies remain below the two new statements: none is pruned from the import
closure. No other node or module is claimed unnecessary. The parent proof avoids gluing
local inverses; only the intrinsic forward product map has to be constructed globally.

## Where the brief, the DAG or earlier work was wrong

The previous attempt treated the absence of a ready-made affine-to-global isomorphism
interface as a blocker. The permitted decomposition resolves that interface gap. The
original final DAG step grouped intrinsic products, compatibility and gluing of inverse
maps as elementary, but these are substantial missing formalization steps. The new
surjection node isolates the necessary global forward-map construction. Injectivity and
global invertibility are now proved in the parent, rather than postponed in that step.

The statements were checked against Stacks Tags 0BQW and 0BQY online. Searches found no
existing exact theorem for either new interface. LeanSearch returned Internal Server
Error and is recorded as unavailable; LeanFinder, Loogle, source grep and whole-blueprint
searches were also performed. The unit's route and its realized nodes are unchanged.

## New nodes

`lem-sc-koszul-self-ext-yoneda-surjection`:
`dag/nodes/sec-picard-framework/lem-sc-koszul-self-ext-yoneda-surjection.json`.
This is the intrinsic boundary/Yoneda-product construction and generation statement,
with a source and complete natural-language proof in the new module's docstring.

`lem-sc-koszul-self-ext-stalk-bases`:
`dag/nodes/sec-picard-framework/lem-sc-koszul-self-ext-stalk-bases.json`.
This is the local zero-differential Koszul calculation and conormal/exterior frame
calculation at one stalk, with the same finite basis index on both sides. It requires
regularity only on the specified chart. No change record is needed: all existing
statements and visibility are preserved, and there are no forced adaptations.

## Second reading by J3

1. **Reading and statement comparison.** I compared the delivered parent module with the repository version. The theorem signature and all existing declaration statements are unchanged byte for byte; only proof text and proof-only imports differ. The two added theorem signatures are self-contained and match their DAG nodes.

2. **Compilation and proof checks.** I compiled all three modules with `lcompile.py --all`; they compile without errors or warnings. The parent contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The two split-off theorems contain exactly their named `sorry` proofs, and neither definition contains `sorry`.

3. **Truth and strength of split statements.** The Yoneda theorem asserts only existence of the intrinsic exterior-to-self-Ext morphism and stalkwise surjectivity. The stalk-bases theorem asserts two finite bases indexed by the same powerset-cardinality set on one specified regular chart, with no compatibility or map claim. These are strictly partial, true consequences of the cited Koszul calculation and are exactly what the parent uses. Edge cases `n = 0`, `n > m`, `m = 0`, characteristic two, and empty `V` are covered by the statements and documented proofs. Searches found no existing declarations duplicating either interface.

4. **Pruning and route.** The parent proof uses only the two new interfaces, `Mathlib.RingTheory.FiniteType`, and the existing stalk-isomorphism criterion; the seven removed imports are therefore proof-only dependencies no longer needed by the parent. The removed declarations remain imported by the split-off modules, whose DAG nodes retain the corresponding proof dependencies. No hollow definition or arbitrary existence witness was introduced.

5. **DAG and unit agreement.** The parent and new node `proof`, `proof_deps`, and `proof_origin` records agree with the Lean proof and docstrings. The unit `sk-thm-picard-duality` route and realized target node are unchanged. The delivery is a permitted decomposition: one upper hole is closed and two strictly simpler named holes remain.

I changed only this second-reading report section after reviewing the worker delivery; no Lean source or DAG statement required repair.
