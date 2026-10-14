## What changed

Proved `AlgebraicGeometry.normalization_comparison_on_iso_locus` in
`Sheaf.AlgebraicGeometry.Curve.NormalizationComparisonOnIsoLocus` without changing its
signature or definitions. Added the proof-only import
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.

The proof uses extension-by-zero base change on the original Cartesian square and
`Scheme.upperStarConstantSheafIso` to identify ν^*(j_!R) with j′_!R. Restriction and
`squareUpperStarIso` identify the corresponding objects over W = ν⁻¹(V). The unit
of the inverse-image/direct-image adjunction for the isomorphism ν|_V, together with
open base change, gives the required isomorphism. Updated the node's proof,
proof_deps, and proof_origin to describe this assembly. The unit `sk-thm-p1` and
all of its realized steps are preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.normalization_comparison_on_iso_locus`
(node `lem-weil-pbc-normalization-comparison-on-iso-locus`).
No holes remain in the delivered module, and none were added anywhere.
No split-off theorems, adaptations, or new definitions were needed.
The second reader's single-file compile succeeded without warnings. An axiom probe
reported exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed the original proof-only imports
`WeilConjectures.SixFunctors.Finite.BaseChange` and
`WeilConjectures.ConstructibleSheaf.Defs`. Finite base change is unnecessary because
the restriction map V.ι is open, hence étale; the existing étale restriction exchange
proves the same identification. The constant-sheaf pullback declaration remains
available through the retained imports. Removed the first worker's redundant added
import `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`, which is already
publicly imported by the retained extension-by-zero base-change module.

The old proof dependency `lemma-weil-pbc-finite-exchange` is no longer used and is
replaced by `lem-weil-pbc-etale-underived-exchange-restriction`. Both other old
proof dependencies remain used. The original plan's auxiliary pullbacks U×_X V and
U′×_X V are unnecessary; inverse-image composition on the restriction square
provides the identification directly. No module or node was dedicated to those
auxiliary pullbacks. These are local import and dependency removals; no claim is
made that any module has left the targets' whole import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The DAG has no Lean attachment for
`sbc-prop-extension-by-zero-and-arbitrary-base-change`, but the needed sheaf-level
result already exists as
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap` in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.
This delivery uses that existing result directly and creates no duplicate.

The blueprint source path named by the existing node is absent in this local
checkout. The existing declaration docstring, node proof, unit record, and
source signatures of the library ingredients were read. The complete Lean
assembly uses proved ingredients and introduces no unproved source claims.
The first worker used finite exchange where the simpler open restriction exchange
suffices; the second reading corrected that route while preserving the signature.

## Second reading by X2

1. PASS: compared the only delivered Lean module with the repository using `diff`.
   The existing theorem signature, declaration visibility, universes, variables,
   and docstring are byte for byte unchanged. No definition or statement was
   changed, and no change record is needed. The only node changes are proof,
   proof_deps, and proof_origin.
2. PASS: compiled the complete module through `lcompile.py`, without errors or
   warnings. A scratch-copy `#print axioms` probe of
   `AlgebraicGeometry.normalization_comparison_on_iso_locus` reports only
   `propext`, `Classical.choice`, and `Quot.sound`. There are no local holes,
   forbidden declarations, new data definitions, or unproved witness choices.
   The square orientations, inverse exchange maps, and adjunction-unit endpoints
   were checked against the source signatures.
3. PASS: there are no split-off statements or new nodes. Independently searched
   the library with `rg` and Mathlib with `msearch.py` grep and LeanFinder, using
   inverse-image/extension-by-zero and Cartesian-square terms. No whole-item
   shortcut was found. Empty V, empty U, zero coefficients (including ℓ=1), and
   ℓ=0 require no extra hypotheses: the same functorial isomorphisms apply.
4. PASS after repair: replaced finite base change with the proved étale exchange
   for the open restriction V.ι, removed the finite-exchange import and dependency,
   and removed redundant ConstructibleSheaf.Defs and Coherence direct imports.
   The final two public imports supply signature definitions; the one added
   plain import supplies the proof. Checked every original proof dependency:
   only finite exchange is no longer used, and it is listed above. The unit's
   realized statement and all four step lists remain unchanged; the replacement
   restriction exchange is an existing closed library tool.
5. PASS after repair: the node's three proof steps match the constructed
   extension-by-zero isomorphism, the inverse-image square isomorphism, and the
   invertible unit followed by open exchange. proof_deps is exactly the union
   of those steps' uses; proof_origin describes the final route. Node statement,
   stmt_deps, Lean attachment, chapter, and unit are unchanged.

Second reading changed the base-change theorem used in the proof, removed three
redundant or unnecessary direct imports from the first worker's version, updated
the corresponding node route, and corrected this report. No holes were added.
