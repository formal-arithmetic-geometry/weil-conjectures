## What changed

Reduced `AlgebraicGeometry.boundary_derivation_algebraic_data` without changing its
signature or any public import. Its proof now explicitly builds the sheaf endomorphism
ring action `mu` from the local action and restriction identity, proves its ring laws,
builds the H1 action using the proved upstream additive-right-derived instance and
`ModuleCat.endRingEquiv`, and takes the additive boundary directly from the exact
composite in the statement. It proves the local-lift hypothesis and applies the
separate Leibniz identity. These constructions and their comparison equations are
complete Lean proofs; no arbitrary cohomology action or boundary is chosen.

Added `Sheaf.Paper.SquareZeroQuotientLocalAction` and
`Sheaf.Paper.SquareZeroHorseshoeBoundaryLeibniz`, with one named intermediate theorem
and one node each. The former has no resolutions or cohomology in its statement.
The latter takes a fixed sheaf action as input and asserts only the Leibniz identity
for the specified snake boundary; it asserts no existence of actions. Neither is
a restatement of the original existential package. Updated the original node's proof
and proof dependencies to match the implemented assembly. All edits are in the sandbox.

The new statements were checked against Stacks 0B8S, including the zero kernel,
empty open/empty scheme, a split extension, and a one-open cover with global lifts.
For the local action, local lifts determine the products uniquely via the monic i,
so the existential witness is characterized by its displayed equations. For Leibniz,
the identity is compatible with zero boundary and with either uniform sign convention.
No extra hypothesis is imposed on the original theorem.

Mathlib searches: LeanFinder returned quotient cotangent-module actions and algebraic
square-zero derivations, but no sheaf quotient action; for Leibniz it returned
Jacobi-Zariski boundary maps and presheaf derivation interfaces, not this connecting
identity. Loogle searches `Functor.mapAddHom` and `Derivation, Module.End` gave no
matches. Grep found the parent statements and generic local-lifting theory, not the
missing intermediate assertions. LeanSearch was attempted for both new nodes and
returned HTTP 500; this is recorded as unavailable, not an absence verdict.
Blueprint searches for `boundary derivation` and `0B8S` found no duplicate.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.boundary_derivation_algebraic_data`
(`lem-sc-boundary-derivation-square-zero-algebraic-data`). No sorry remains in the item.
This is a decomposition, not a finished proof from sorry-free dependencies:
one upper hole closed, two strictly narrower holes added, net holes closed minus added = -1.

Every hole added by this delivery:

- `AlgebraicGeometry.square_zero_quotient_local_action`
  (`lem-sc-square-zero-quotient-local-action`), in
  `Sheaf.Paper.SquareZeroQuotientLocalAction`: construction and descent of the local
  quotient action. Its entire proof is `by sorry`, with a complete construction in
  the docstring and node. The existing proved local-lifting interface is imported.
- `AlgebraicGeometry.square_zero_horseshoe_boundary_leibniz`
  (`lem-sc-square-zero-horseshoe-boundary-leibniz`), in
  `Sheaf.Paper.SquareZeroHorseshoeBoundaryLeibniz`: the Cech product computation and
  comparison with the fixed horseshoe boundary, for a supplied action. Its entire
  proof is `by sorry`, with the proof and required interfaces recorded.

The original module's construction, all ring-homomorphism laws, all three
comparison equations, and the passage from the sigma lift formula to the mu lift
formula compile. The two new modules also compile. No definitions contain holes,
and no signature, visibility, or existing module other than the item is changed.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts` and
`Sheaf.AlgebraicGeometry.CechH1MapNatural` from the item: its proof now uses the two
narrower interfaces. Their corresponding nodes
`lem-sc-boundary-cech-local-lifts` and `lem-sc-cech-h1-map-natural` are no longer direct
proof dependencies of the item, but remain planned dependencies of the new Leibniz
module. Thus no module in the target import closure is claimed pruned: pruned none.
All original public imports are retained. The blueprint unit's route is retained;
`sk-thm-curveestimate.realized` has no internal proof steps bypassed by this reduction.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan hides two substantial interfaces: quotient-action
construction and the product identity with the specified resolution boundary.
`boundary_cech_local_lifts` and `cechH1Map_natural` alone do not state either one.
This delivery exposes those steps while completing the algebraic assembly.

There is a sign mismatch to resolve in the earlier boundary comparison interfaces:
`boundary_cech_local_lifts` uses `t(x 0) - t(x 1)`, whereas
`boundary_cech_compatibility` uses `t(y 1) - t(y 0)` with the same canonical boundary
and comparison predicate. This was already flagged in the former node's Lean note.
No interface is changed here and no contradiction is used. The new Leibniz node
requires a consistent convention; reversing all three boundary representatives
preserves Leibniz. Its future proof must track this sign when comparing Cech and
horseshoe connecting maps. The identity itself is the source's assertion and does
not depend on which uniform convention is used.

LeanSearch was unavailable, as noted above. This does not prevent the other searches
or local compilation.

## New nodes

`lem-sc-square-zero-quotient-local-action` records the first paragraph of the proof
of Stacks 0B8S: construct the quotient action by local multiplication, square-zero
independence, and sheaf gluing. It uses the already proved module exactness/local
lifting interface and the existing algebra/module definitions, not the parent
boundary theorem. Its module is `Sheaf.Paper.SquareZeroQuotientLocalAction`.

`lem-sc-square-zero-horseshoe-boundary-leibniz` records the remaining Cech product
calculation for an input sheaf action and a fixed compatible resolution triple.
The lift-action hypothesis and overlap identity connect to the original Cech and
horseshoe interfaces. Its module is `Sheaf.Paper.SquareZeroHorseshoeBoundaryLeibniz`.

No change record is needed: the original public interface is unchanged and all new
imports of the original module are proof-only. There are no forced adaptations.

## Second reading by N2

1. **Interface preservation: pass.** Diffed the existing module against the repository
   and compared the complete existing theorem signature byte for byte. Only its proof,
   proof imports, and a local elaboration option differ. No definition, target statement,
   public import, visibility, or other existing module is changed. No change record or
   forced adaptation is needed.
2. **Proof and axioms: pass as a decomposition.** All three modules compile locally
   through lcompile.py (5.9, 2.2, and 10.8 seconds). A scratch copy with explicit
   `#print axioms` for all three delivered declarations compiled and reported only
   `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
   Exactly the two reported public intermediate theorems have `sorry`; there are no
   definitions with holes or forbidden declarations. The local action is uniquely
   determined by local lift multiplication and restriction: sectionwise injectivity,
   local surjectivity, and sheaf separation force equality of any two witnesses.
   The proof constructs mu, rho, and delta explicitly and does not choose arbitrary data.
3. **Split statements: pass.** Independently checked the proof of Stacks Tag 0B8S
   (https://stacks.math.columbia.edu/tag/0B8S). The local-action lemma isolates quotient
   multiplication and descent with no cohomology; the Leibniz lemma takes the action
   as input and only proves the fixed boundary identity. Neither restates the parent.
   Checked empty opens/empty scheme, zero kernel, split extensions, and a cover with
   global lifts: gluing is unique or the boundary is zero in these cases. Each has a
   source, full construction/comparison argument in its docstring, and a matching node.
   Independent LeanFinder queries used quotient actions by gluing local products and
   the connecting-map product cocycle; hits were presheaf differentials and group
   cohomology cocycle formulae, not the needed assertions. Loogle `Derivation, RingHom`
   gave single-ring derivation/lifting results, not this sheaf boundary. Local rg across
   both Lean roots and msearch grep found no replacement. Neither remaining assertion
   admits a few-minute proof from the available interfaces.
4. **Route and pruning: pass.** Read the original planned boundary local-lift and
   Cech naturality interfaces, the proved module local-lifting theorem, and the horseshoe
   delta-functor theorem. The latter quantifies over every compatible resolution triple,
   so it supports the planned comparison with the specific boundary in this statement.
   The assembly uses the proved additive right-derived instance and endRingEquiv.
   Proof-only imports are plain imports; public imports support the signatures.
   `No longer needed` lists both old proof dependencies removed from the item; their
   modules remain in the new Leibniz proof plan, so no closure pruning is claimed.
   The unit `sk-thm-curveestimate.realized` has only its statement realization and no
   internal steps, and is untouched. The pre-existing Cech sign mismatch is reported;
   it is not used as a contradiction. Uniformly reversing differences preserves Leibniz.
5. **DAG agreement: pass after repair.** Checked the three proof-dependency unions,
   existence of every cited node, source, chapter/unit, creation fields, blueprint origin,
   and Lean declarations. The original node records the actual local-action assembly
   and Leibniz application. The new nodes describe strictly smaller obligations.
   Replaced both new `lean.statement` fields with the exact multiline signatures from
   their Lean files; the old flattened Leibniz field even omitted the separating newline
   after its let-expression, so this was a real transcription fault.

Second reading changed only the two new nodes' verbatim Lean statement records and
this report. No Lean proof needed repair. One original hole closed, two holes added:
this delivery is a decomposition with net -1, not a completed sorry-free proof.
