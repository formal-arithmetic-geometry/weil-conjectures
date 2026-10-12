## What changed

The statement and visibility of
`AlgebraicGeometry.Scheme.finite_normal_etale_of_depth_two_neighbourhood` are unchanged.
Its proof is now a complete Lean assembly of the original three-step argument.
A proved private helper `etale_restrict_sup` uses target locality and the
Mathlib isomorphism identifying repeated restrictions to prove etaleness on the union.
The main proof constructs that union, checks all nonclosed fibres are contained in it,
proves density on the closed fibre using smooth geometric irreducibility and the actual
point x, extends the cover, proves that L is normal integral, compares the two covers,
and transports etaleness through the resulting isomorphism.

Added two modules, each containing one strictly smaller sourced theorem:
`SmoothLocalDepthTwoEtaleExtension` extends an arbitrary finite etale cover of a
fibrewise dense open; it does not mention the original normal finite cover N.
`FiniteNormalDenseOpenComparison` compares N with an already supplied finite etale cover;
it assumes neither a smooth family nor a local base nor any depth condition.
Neither new theorem is a renamed or repackaged version of the original conclusion.
All additions and edits are under the named sandbox. No target, existing signature,
visibility, definition, or other holder's module was changed.

The primary source pages read were Stacks Project Tags 0EYB (58.26.3), 0EY6 (58.21.5),
0EYJ (58.31.8), 0EYA (58.26.2), 035I (29.54.4), and 0BQM (58.11.3).
The unit record `sk-prop-input-spreading` was read: the depth-two extension and purity
route is retained. Its realized fields are empty; no unit route was replaced.
`SmoothConnectedGenericGeometryCore` was checked against its Lean signature and node.
Its canonical generic-fibre input is a concrete Mathlib pullback, not a witness chosen
from an unproved existence theorem. Extension witnesses are eliminated inside a proof;
no definition chooses arbitrary data from an unproved existence statement.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finite_normal_etale_of_depth_two_neighbourhood`
(node `lem-sbc-finite-normal-depth-two-purity`). Its module contains no remaining sorry.
The private helper `AlgebraicGeometry.Scheme.etale_restrict_sup` is also fully proved.

Added exactly two holes, both public named theorems with proof exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_local_depth_two`,
  node `lem-sbc-smooth-local-depth-two-etale-extension`, module
  `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension`.
- `AlgebraicGeometry.Scheme.finite_normal_iso_of_dense_open_etale_comparison`,
  node `lem-sbc-finite-normal-dense-open-comparison`, module
  `Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenComparison`.

This delivery is a decomposition, not a sorry-free proof of the purity theorem:
1 original hole closed, 2 holes added, net -1 before any closure deduplication.
The complete assembly compiled through `lcompile.py` with no errors or warnings.
All three sandbox modules compiled together in dependency order.

The extension statement includes empty covers, U=L, and empty fibres. A field base
cannot meet its depth-two hypothesis, so it introduces no false depth-zero case.
It requires density in the actual scheme-theoretic closed fibre, not just density
in the total space. It drops normality and geometric connectedness only because its
explicit fibrewise density hypothesis supplies precisely what 0EYB needs.

The comparison statement includes disconnected and empty covers. Density excludes
components of N supported outside U; etaleness over U makes every remaining normal
component dominate the integral base. Components of the etale cover E also dominate.
This is essential for using their finite generic algebras. For an empty restriction,
density forces N empty and openness over the integral base forces E empty. For U=B,
the supplied isomorphism is already global. No connectedness or surjectivity of either
finite cover is asserted or assumed.

## No longer needed

Removed the direct proof imports of `Sheaf.RingTheory.SmoothNormalRing`,
`Sheaf.RingTheory.EtaleNormalRing`, and `Sheaf.RingTheory.FlatLocalDepthFormula` from
the original module. Their nodes
`lem-weil-pbc-smooth-over-normal-ring-normal`,
`lem-weil-pbc-etale-over-normal-ring-normal`, and
`lem-weil-pbc-flat-local-depth-formula` are no longer direct proof dependencies there.
They remain needed transitively: smooth normality through the already proved
`SmoothConnectedGenericGeometryCore`, etale normality in the comparison theorem,
and the flat local depth formula in the extension theorem. Therefore no entire
module or node is claimed pruned from the target closure. All original public imports
remain because the unchanged statement uses their notions. All new proof imports are
used by the final argument or are the new nodes' stated proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The original node names only ring normality and the flat local depth formula as proof
dependencies. Those signatures do not assert either the scheme-level etale extension
or the comparison of finite covers, so they cannot close steps 2 and 3 by themselves.
The two new nodes make those missing steps explicit. No mathematical error in the
original purity statement was found. The resulting route preserves all its hypotheses.
The original unbound scheme-level claims in step 1 are now proved in Lean.

The blueprint source markdown and local Stacks source tree named by repository settings
are absent on this machine. The available unit JSON contains the source text; Stacks
pages were read directly. Mathlib search used the required `msearch.py` service and
local `rg`; LeanSearch returned Internal Server Error, recorded as unavailable.
LeanFinder and grep were available and found no exact extension or comparison theorem.
Normalization search hits supply universal constructions and compatibility, but not
normal-finite-cover comparison. Whole-DAG and blueprint searches found no duplicate
statements; the existing generic full-faithfulness theorem requires both global covers
already etale and so cannot prove this comparison without circular reasoning.

## New nodes

`lem-sbc-smooth-local-depth-two-etale-extension` records the local-base specialization
of the fibrewise dense-open extension theorem 0EYB, with its 0EY6 construction and
0337 depth calculation. Its source proof is written in words in the Lean docstring
and in the node. It imports the existing flat-local-depth module. The new theorem
requires neither N nor its normality, and produces only a new extension and its
isomorphism on the supplied open.

`lem-sbc-finite-normal-dense-open-comparison` records the finite integral-closure
comparison from the original step 3. It uses the existing etale-normal-ring node
and relative-normalization node. The proof identifies generic algebras componentwise
and writes out the two inclusions into their integral closures and the overlap
uniqueness. The new theorem requires a previously given etale extension and concludes
an isomorphism, with no local-base extension or depth argument.

Both nodes carry recorded LeanSearch, LeanFinder, and grep searches matching the
sandbox searches.jsonl. Both inherit the chapter, unit, and nearest blueprint
ancestor from the original node. Its proof, proof_deps, and proof_origin now follow
the compiled assembly. No change record is necessary because no existing interface
changed. No scratch Lean module is included in the delivery.

## Second reading by E2

1. I compared the delivered purity module with the repository version. The target
statement, all existing declarations, and visibility are byte-for-byte unchanged;
only imports, the private helper proof, and the target proof changed. Verdict: pass.

2. I compiled all three sandbox modules with `lcompile.py --all`. Compilation succeeds
without errors or warnings. The only remaining `sorry`s are the two named public
split-off theorems listed above; there are no axioms, unsafe declarations, hollow
definitions, or forbidden implementation directives. Verdict: pass.

3. I checked both split-off statements against their docstrings and node files. Each
is strictly smaller than the purity target, has a complete sourced proof description,
and is needed by the target proof. I searched the library and Mathlib-facing search
tools for duplicates and found none. Verdict: pass, with the two documented holes
left intentionally as decomposition.

4. I traced the proof from the target downward. It uses the existing generic smooth
geometry core, the new fibrewise extension theorem, and the new finite-normal
comparison theorem. The union-locality helper and the density argument are proved
directly. The unit `sk-prop-input-spreading` route is retained. The three former
direct ring/depth imports are no longer needed directly and are recorded above;
their facts remain available transitively. Verdict: pass.

5. I checked the three DAG nodes against the Lean declarations, including statements,
proof dependencies, proof origins, chapter/unit, and the recorded searches. The new
nodes have matching public modules and declarations, and the original node records
the assembled route. Verdict: pass.

I changed only this second-reading report section; no Lean code, node statement, or
existing interface required repair.
