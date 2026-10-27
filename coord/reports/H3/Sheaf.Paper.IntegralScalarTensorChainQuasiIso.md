## What changed

Replaced the hole in `WeilConjectures.scalarTensorChainQuasiIso` with a proof
from one strictly finite-level lemma. The public theorem signature and public imports
are preserved. Added proof imports for the normalized finite generators, scalar
product comparison, diagonal cone homotopy, and strict Roos derived-limit API.

The proof establishes generator extensionality for scalar-extended finite tensors,
proves the generator formula for arbitrary tower transitions by induction, and
constructs a late diagonal factorization using the inverse finite-level
isomorphism. Both factorization equations are checked on the actual prescribed
generators. The diagonal cone homotopy makes every late cone transition zero
in the derived category. The existing strict-tower comparison then proves that
the specified Roos map is a quasi-isomorphism. Separately, finite freeness and
the two product coordinates prove that the additive scalar/Roos map is an
isomorphism. Composition gives precisely the original `scalarTensorChain`.

Validation: the final item module compiled without errors or warnings in
54.2 seconds through `lcompile.py`; the new finite-level module also compiled
within the 60-second limit. Delivery runs the complete packet checks.

The scalar/product and pro-zero/Roos arguments reuse the existing proved
arguments in `IntegralScalarPullbackRoosQuasiIso` as private helpers, without
importing its pullback-specific statement or dependency chain.

## Proved and sorry left

Closed the original hole in `WeilConjectures.scalarTensorChainQuasiIso`
(node `lem-pur-integral-scalar-tensor-chain-quasi-iso`). There are zero holes
left in the item module.

Added one hole: `WeilConjectures.integralScalarTensorRamifiedLevel`, in the
new module `Sheaf.Paper.IntegralScalarTensorRamifiedLevel`, node
`lem-pur-integral-scalar-tensor-ramified-level`.

This is a decomposition: one upper hole closed, one smaller hole added, net
zero holes. The remaining statement is only a normalized isomorphism between
one scalar-extended finite tensor level and one later target level. It has no
Roos complex, tower morphism, cone, homotopy, quasi-isomorphism, or good-complex
hypothesis. Its full proof in words and sources are in its docstring and node.
The original theorem's actual combination of the finite step with products,
cones, and strict derived limits is complete Lean.

## No longer needed

No existing import was removed and no existing module is withdrawn. Pruned the
following direct planned proof dependencies of the item:

- `lem-pur-finite-free-completion-exchange`
  (`Sheaf.Algebra.Homology.FiniteFreeCompletionExchange`): use the late cone
  transition criterion instead of a chosen derived completion exchange.
- `lem-pur-compact-support-roos-cofinality`
  (`Sheaf.CategoryTheory.CompactSupportRoosCofinality`): the diagonal cone
  homotopy replaces arithmetic restriction and its inverse on Roos coordinates.
- `lem-pur-kflat-total-tensor-model`
  (`Sheaf.Algebra.Homology.KFlatTotalTensorModel`): the finite balanced tensor
  argument works on arbitrary complexes, so no K-flat closure proof is needed.
- `lem-weil-l-adic-extension-integers-dvr`
  (`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`): the finite step uses the
  existing normalized ramification/quotient interface rather than reconstructing
  DVR data.

`lem-pur-integral-ambient-operation-models` and
`lem-weil-normalized-ordinary-scalar-tensor-chain` move out of the item's direct
proof dependencies into the finite-level lemma's proof plan; they are retained,
not claimed pruned. The other removed direct dependencies above can remain
transitive dependencies of retained modules or be needed by other parents.
No claim is made that their modules leave the targets' full import closure.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original arithmetic-restriction route is
valid, but its reverse-map homotopy can be avoided by factoring late cone
transitions. The existing finite-level and transition declarations suffice for
all the generator glue after the single ramified-level isomorphism.
Flatness of P,Q is unnecessary for this chain-level argument; the assigned
public signature is unchanged. Both zero factors and the empty site give zero
complexes, and an unramified coefficient extension allows the same finite
index on source and target. No shared definition or existing interface changed.

## New nodes

`lem-pur-integral-scalar-tensor-ramified-level`: at a fixed quotient level n,
ordinary scalar extension identifies the finite tensor with target level
m = e(n+1)-1 >= n. Its normalized formula involves only total pure generators.
This is the finite balanced-tensor part of the item's original first two proof
steps. Sources and dependencies are recorded explicitly. Searches found the
existing coefficient-quotient and tensor models, but no declaration assembling
this ramified tensor isomorphism. No change record is required because all
changes are confined to the item and its new lemma/node.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
