## What changed

Completed and checked the earlier sandbox reduction of
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows`.
The existing public theorem and every existing public import retain their signatures/visibility.
Two new proof-only imports state the distinct sheaf-pullback and coherent-base-change
steps. The lifted structure sheaves are explicit constructions, not arbitrary chosen witnesses.
The private helpers `surjective_sheafH_zero` and `exists_frobenius_model` are fully proved.
The final proof combines the section-data/exactness declarations, the two new lemmas,
cohomology naturality, tensor subtraction and cancellation.

All three modules compile with lcompile.py --all. The inherited searches and additional
LeanSearch/Loogle/Mathlib grep were checked; no exact existing theorem supplies the
canonical scalar-compatible comparison or specified Artin--Schreier pullback rows.
Stacks Tags 0A3P, 0A3J, 02KH, 03P2 and 02O6 were read online because this checkout
holds literature lists but not the downloaded documents.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.IsCurve.exists_artinSchreier_frobenius_exact_rows`
(node `lem-pbc-artin-schreier-frobenius-exact-rows`). Its module has no remaining sorry.
This is a decomposition, not a sorry-free proof of its import closure: two holes added,
so the local net is minus one.

Added and left exactly these two named public holes:
- `AlgebraicGeometry.IsCurve.exists_artinSchreier_pullback_rows`
  (`lem-pbc-artin-schreier-pullback-rows`). This concerns only the sheaf maps and row
  transport; it asserts no coherent cohomology or Frobenius model.
- `AlgebraicGeometry.IsCurve.exists_additive_scalar_base_change`
  (`lem-pbc-additive-scalar-base-change`). This concerns the scalar-compatible coherent
  comparison and canonical pullback; it asserts no Artin--Schreier rows or Frobenius.

No holes were added in definitions, private helpers, or the combining proof.
Existing imported holes are unchanged. Semilinearity and pure-tensor Frobenius
compatibility are proved in Lean rather than asserted by a new helper.

## No longer needed

No original imports removed: all five public imports preserve the statement interface.
Removed unused imports from the NEW modules: `WeilConjectures.AlgebraicGeometry.Curve`
from ArtinSchreierPullbackRows, and `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
from AdditiveScalarBaseChange. The second reader also removed
`WeilConjectures.LinearAlgebra.SemilinearFrobenius` from that new module;
its signature already obtains tensor products and finite-dimensionality from Curve.
No module is claimed globally pruned.
The original route's direct use of
`lemma-weil-pbc-smooth-curve-artin-schreier-proper-degree-zero` and
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierProperDegreeZero` is unnecessary:
the proved helper uses Sheaf.H.equiv_0 directly, avoiding a derived-to-Ext transport.
The direct scalar-model dependency `lem-sc-additive-cohomology-finite-scalar-model`
and `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel` is also unnecessary;
the new canonical comparison supplies the needed scalar action in the Ext model.
The original `lem-sc-as-sequence` / `Sheaf.AlgebraicGeometry.ArtinSchreierSequence`
is replaced by the already stated section-data and section-exactness nodes, which
apply to C' without manufacturing an IsCurve instance.
`lem-weil-pbc-sheafH-ext-derived-comparison`, `lem-sc-flat-base-change-coherent`,
`lem-sc-etale-zariski-qcoh-comparison`, and `lem-pc-cech-computes` are no longer
DIRECT dependencies of this module; they remain in the proof plan of the new
additive-base-change node and are not claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had compilable Lean but no node copies or report, so it was not
ready to hand off. Added the missing records and made the DAG follow its actual proof.
The original plan mixed the derived and Ext cohomology interfaces. Degree zero needs
no conversion; degree one still needs a canonical comparison with scalar/base-change
naturality, which the existing nonempty flat-base-change linear equivalence alone
cannot assert. No existing statement or definition was changed.

The additional proof-DAG audit found a PRE-EXISTING cycle beneath proper coherent
finiteness: `lem-pc-coherent-hi` ->
`lem-pc-e2-integral-ideal-proper-cohomology` -> `lem-pc-euler-additive` ->
`lem-pc-coherent-hi`. These nodes and edges are unchanged and outside this item.
Reachability checks from each delivered node show that no cycle contains any
delivered node. The inherited finiteness-plan cycle needs maintainer attention.

Edge cases checked: p is prime, hence positive; empty schemes are excluded by the
main connectedness hypothesis, but the new pullback-row statement allows them and
short exactness transports on the zero sheaf category. The main curve interface
allows dimension zero: coherent H^1 and its tensor extension vanish in that case,
while global functions and degree-zero surjectivity remain valid. With k'=k and the
identity pullback, the formulas specialize to the usual scalar and identity maps.
The new additive comparison has properness, so its finiteness assertion does not
rely on finiteness of arbitrary nonproper structure-sheaf H^1. Both helper statements
are strictly parts of the argument, not renamed versions of the delivered theorem.
The unit sk-thm-p1 Artin--Schreier/coherent route is retained; none of its realized
unit statements or steps is bypassed.

## New nodes

`lem-pbc-artin-schreier-pullback-rows`, in
`dag/nodes/sec-proper-base-change/lem-pbc-artin-schreier-pullback-rows.json`,
states the section-specified sheaf pullback and exact-row transport argument.
Its one statement is in `ArtinSchreierPullbackRows.lean`, with the source and complete
proof in its docstring. It depends on the existing constant-sheaf pullback comparison.

`lem-pbc-additive-scalar-base-change`, in
`dag/nodes/sec-proper-base-change/lem-pbc-additive-scalar-base-change.json`,
states the scalar-compatible canonical first coherent cohomology comparison.
Its one statement is in `AdditiveScalarBaseChange.lean`, with its proof in the docstring.
The original comparison, finiteness, Cech and flat-base-change nodes remain below it.
Blueprint searches for Artin and base change found only more general surrounding
statements, not these precise naturality packages; no duplicate exact node was found.
No change record is needed: no existing signature, definition or visibility changed.


## Second reading by J1

1. Compared all three delivered modules with the repository. The two new modules
   have no repository counterpart. The original theorem's full signature is now
   byte-identical, its docstring is unchanged, and all five existing public imports
   retain visibility. Only proof-only imports, two proved private helpers and the
   original proof body are added. No existing definition or statement changes.
   Verdict: pass.
2. Compiled all files through lcompile.py. The only two textual sorries are exactly
   the two named public split-off theorems reported above, both with source/proof
   docstrings and matching nodes. No definitions or private helpers contain sorry;
   no forbidden axiom, unsafe, opaque, extern or implemented_by occurs. Scratch
   copies with #print axioms check all five delivered theorems: only propext,
   Classical.choice, Quot.sound and inherited/open sorryAx occur. In particular,
   exists_frobenius_model has no sorryAx; the degree-zero helper depends on existing
   imported proper-global-section results. Verdict: pass as a decomposition,
   not as a sorry-free import closure.
3. Read the full split-off signatures and their natural-language arguments, and
   checked the Stacks sources 0A3J, 0A3P, 03P2, 02KH and 02O6. Pullback rows need
   only natural section identifications, the given Artin--Schreier formulas and
   short exactness on C'; ring pullback and constant-sheaf transport give the two
   squares. The scalar comparison uses proper coherent finiteness and the
   canonical flat-base-change map, with its actual scalar actions. Empty schemes
   for the row lemma, identity base change, degree-zero curves and the zero H^1
   model cause no failure. Neither statement asserts the other's conclusion or
   restates the original package. Fresh LeanFinder, Loogle and grep searches,
   including different vocabulary, found generic pullback/tensor/exactness tools,
   but no exact compatible package; repository comparison and flat-base-change
   statements also lack the required combined naturality. Updated new-node search
   records to these actual, relevant queries. Neither open statement has a short
   direct proof from an existing declaration. Verdict: pass.
4. Read the combining proof from its conclusion downward. It explicitly constructs
   G/G', applies the existing section-data and exactness declarations, and reduces
   the remaining geometry to the two strictly narrower statements. The proved
   phi=wp+id argument obtains semilinearity; cohomology naturality and cancellation
   obtain pure-tensor Frobenius compatibility without another hole. Degree zero
   uses the terminal-object Ext equivalence directly. All new proof dependencies
   in the original module are plain imports. Removed the unnecessary public
   SemilinearFrobenius import from the new additive-comparison module and checked
   compilation. The No longer needed section accounts for every old proof_deps
   entry removed from the main node. No globally pruned module is claimed. Read
   sk-thm-p1.json realized: the characteristic-p Artin--Schreier/coherent route and
   all unit-level steps are retained. Verdict: pass.
5. Checked that each new node's lean.statement matches its Lean signature verbatim,
   its required metadata is present, and every node's proof_deps is exactly the
   union of its proof-step uses. The original node differs only in proof,
   proof_deps and proof_origin; its mathematical statement and lean record remain
   unchanged. Its steps match the section construction, row pullback, scalar
   comparison, proved semilinearity/cancellation and degree-zero helper. New nodes
   include complete proof plans and source provenance. Verdict: pass.

Second-reading changes: restored one surplus space before the original proof
separator so its signature is byte-identical; removed the unused
SemilinearFrobenius import in AdditiveScalarBaseChange; replaced irrelevant copied
search entries in the two new nodes with the fresh relevant searches; documented
these checks. No mathematical statement, definition or proof argument changed.

The first dry run required LeanSearch separately from its combined Loogle/LeanFinder
category. Ran two fresh topic-specific LeanSearch queries and recorded the service
unavailability alongside the successful alternative searches.
