## What changed

Replaced the sorry in `Algebra.exists_popescu_algebraic_residue_enlargement`
with the proved separable-power reduction and assembly. The private
`Algebra.exists_separable_power` uses Mathlib's separable contraction of an
irreducible minimal polynomial, evaluation, and minimal-polynomial divisibility.
Characteristic transfers through the injective field map k→residueField A₀.
All existing public signatures and public imports are unchanged.

Added `Sheaf.RingTheory.PopescuSeparableResidueRealization`, imported only for
the proof. Its `Algebra.exists_popescu_separable_residue_realization` is now
fully proved from the existing `Algebra.exists_finiteEtale_artinian_residue_lift`.
Residue compatibility identifies the input algebra with the canonical one.
Faithful flatness makes the supplied map injective; its k-algebra image supplies
A. Finiteness, étaleness, flatness, and the maximal-ideal equality give
admissibility. The canonical residue algebra gives the requested scalar tower,
compatibility and formal étaleness. No data definition chooses an arbitrary
witness from an unproved theorem.

## Proved and sorry left

Closed original hole: `Algebra.exists_popescu_algebraic_residue_enlargement`
(node `lem-weil-pbc-popescu-algebraic-residue-enlargement`), one of one original
holes. The private `Algebra.exists_separable_power` is proved from Mathlib.

Added fully proved theorem: `Algebra.exists_popescu_separable_residue_realization`
(node `lem-weil-pbc-popescu-separable-residue-realization`). The second reading
closed the first worker's proposed lower hole in this theorem. No sorry remains
in either delivered module; zero holes are added. The proof uses the existing
Artinian residue-lift theorem; the scratch axiom checks and delivery probe verify
its actual transitive trust dependencies. Ledger progress is determined against
the pinned import-closure baselines, not by the number of deliveries.

## No longer needed

No existing import was removed: every original public import is needed by the
existing public statement. All added imports are proof-only except the new
module's public statement imports.

The following old proof dependencies are no longer direct dependencies of the
item (the record replaces them with the proved power reduction and separable
residue realization):

- `lem-weil-pbc-artinian-local-noetherian-nilpotent`
- `lem-weil-pbc-artinian-local-unique-prime`
- `def-weil-pbc-popescu-admissible-subalgebra`
- `def-weil-pbc-separable-algebraic-extension`
- `lem-weil-pbc-finite-separable-extension-etale`
- `lem-weil-pbc-henselian-of-nil-maximal-ideal`
- `lem-weil-pbc-henselian-finite-etale-equivalence`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`
- `lem-weil-pbc-etale-ring-base-change`
- `lem-weil-pbc-henselian-etale-retraction`
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`
- `def-weil-pbc-flat-ring-map`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `def-weil-pbc-essentially-finite-type-algebra`
- `def-weil-pbc-finite-type-algebra`
- `lem-weil-pbc-artinian-local-essentially-finite-type-residue`

This is a complete comparison against the old `proof_deps`. These nodes are not
all globally pruned: the Artinian residue-lift theorem has its own dependencies.
The new realization proof uses the existing residue-lift theorem, not a fresh
henselian construction. In particular the residue essential-finite-type criterion
and noetherian-local quotient route are unnecessary: finite module transport
makes A Artinian, and essential finite type follows by composition through A₀.
No removed module is claimed to leave the targets' global import closure.
The unit `sk-thm-p1.json` and its `realized` route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original statement is correct. The first worker missed
`Algebra.exists_finiteEtale_artinian_residue_lift`, which already gives the
abstract finite étale local Artinian algebra, flat local map, and element with
specified residue. The remaining image and residue transport can be proved
without splitting off a new hole. The first worker's decomposition was therefore
unnecessary; the second reading replaced it by a proof.

Independent searches used LeanFinder (finite étale embedded lift), Loogle
`IsSeparable, Subalgebra`, and grep through Mathlib, lean/Sheaf and the upstream
WeilConjectures checkout. The search service returned supporting declarations;
repository grep found the Artinian residue-lift family. There is no existing
admissible-image theorem with this statement. The existing local lifting theorem
is used directly. Read https://stacks.math.columbia.edu/tag/07FI, algebraic branch,
and the supplied existing theorem and its core/capture/flat modules.

## New nodes

`lem-weil-pbc-popescu-separable-residue-realization` in
`dag/nodes/sec-proper-base-change/` records the now fully proved characteristic-
independent geometric realization. Its proof and dependencies have been updated
to the existing Artinian residue lift, faithful-flat injectivity, finite image,
and canonical residue algebra. Its module is
`lean/Sheaf/RingTheory/PopescuSeparableResidueRealization.lean`.
No existing statement or definition changes; no change record is required.

## Second reading by G3

1. Compared the item with the repository by diff, and mechanically compared the
   entire existing theorem signature byte for byte. Pass: no public signature,
   definition, visibility, or public import changed. No adapted existing module.
2. Compiled both modules locally in import order. Pass: no errors or warnings,
   no sorry in either module, no axiom/unsafe/opaque/implemented_by/extern, and
   no added data definition. Checked the private power helper and both public
   theorems by `#print axioms` in a scratch copy, plus the delivery-wide probe.
3. Checked the proposed split statement: β=0 and β in F₀ are covered by the
   identity extension; the field case and characteristic zero are included;
   inseparable β is excluded and handled by the item's power reduction. Pass:
   the statement is true and a strict geometric part of the original argument.
   It is now fully proved. The compatible supplied residue algebra is explicitly
   identified with the canonical one before applying the existing lifting result.
   Independent searches found no duplicate admissible-image result.
4. Checked shorter routes and imports, and compared all old proof dependencies.
   Pass after repair: used the existing Artinian lift, retained public statement
   imports, added only proof imports, and reported every removed direct dependency.
   The unit's realized statements and steps are kept; no unit route is bypassed.
5. Read both node records with the Lean files. Pass after repair: the old node
   keeps its statement and records power extraction and assembly; the new node
   records the actual existing lift and image/residue transport. New-node fields,
   declaration statement, source, origin, chapter and unit agree with the code.

Changed by the second reading: proved the proposed geometric hole using the
existing residue-lift theorem and Mathlib transport; updated its proof docstring,
DAG route and dependencies, and the report; restored signature whitespace exactly. The original
mathematical statement and original docstring are unchanged.
