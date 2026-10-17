## What changed

Closed the two existing inverse-existence holes by categorical assembly from component monicity
and a component retraction. The left-inverse proof cancels each monic exchange component to
obtain its opposite inverse equation, then uses `NatIso.isIso_of_isIso_app`. The right-inverse
proof uses the left inverse and `NatTrans.mono_of_mono_app` to cancel at natural transformations.

All existing declarations, signatures, definition bodies, visibility and public imports remain
unchanged. Two proof-only imports supply the component statements in new Sheaf modules. Their
equality parameter spells out the existing exchange expression and is discharged by `rfl`.
There is no duplicate exchange definition and no public equality bridge.

The interface addition is recorded in `coord/changes/exchange-component-inputs.md`.

## Proved and sorry left

Existing holes closed (2 of 2):

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_leftInverse`
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_rightInverse`

New component holes left (2):

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono`
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_section`

This is a decomposition: two holes closed and two added, net zero in the target import closure.
The item's `isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange` was already proved in
current sources; it is preserved and is not counted as a newly closed hole. The geometric
compatibility of sheaf exchange with module scalar transport, exact derived functors and the
restricted adjunctions remains open. Every remaining sorry is a whole public named theorem
with a source, natural-language proof and matching new node. No data is chosen from a sorry.

All three delivered modules compile through `lcompile.py` (2.4 s, 2.5 s, 6.7 s in the reviewed
run). Explicit `#print axioms` for both inverse theorems and the isomorphism theorem shows only
`propext`, `Classical.choice`, `Quot.sound` and the expected `sorryAx` from the two component
inputs and existing open dependencies. Separate axiom prints confirm that `ProEtale.isIso_baseChangeMap_of_isPullback` and
`ProEtale.isIso_openImmersionLowerShriekBaseChangeMap`, used as tools in the component proof
plans, use only the three permitted axioms and no `sorryAx`. The delivery tool additionally
probes every declaration.

## No longer needed

Remove `thm-sfb-dc-open-base-change-iso` from the old `proof_deps` of each inverse node: the old
plans cited the very isomorphism theorem proved from these two nodes, giving a circular plan.
The left inverse now uses the two component nodes; the right inverse uses the left-inverse and
monicity nodes. The parent theorem still uses the two inverse nodes, exactly as its unchanged
Lean proof does. No previously imported module is removed, and no library module is pruned.

The failed attempt's new duplicate `Exchange.lean`, construction node, and unused change record
were withdrawn before delivery; copies remain in sandbox scratchpad only. They never landed.

The unit `sk-def-sfb-open-base-change` still constructs the same unit--square--counit exchange
and proves its isomorphism before forming its inverse. Its `realized` arrays are empty in the
baseline, and no unit route is changed. The ordinary weakly etale sheaf base-change theorem is
used as a general already proved tool in the component proof plans, not as a replacement unit.

## Where the brief, the DAG or earlier work was wrong

The interrupted report counted the already proved isomorphism theorem as a third sorry and
claimed that proof assembly required changing the exchange definition or adding a public
bridge. The component lemmas can instead take a natural transformation equal to the existing
formula; `rfl` supplies this equality inside the item without any public interface change.

The earlier support construction duplicated the existing exchange notion and was unconnected
to the item. It is withdrawn. Earlier component node statements depended on the parent
isomorphism node; their statement dependencies now cite the exchange definition and restricted
functors, avoiding a circular dependency. Earlier inverse plans also cited the parent theorem;
those proof dependencies are replaced by the actual componentwise proof.

Independent searches used different wording: LeanFinder searched inverse image of extension
by zero for condensed module objects; Loogle found `NatTrans.mono_of_mono_app`; LeanSearch
found componentwise isomorphism criteria. `rg` found the ordinary pro-etale sheaf exchange in
`FiniteCoefficient/LowerShriek/Open/BaseChange.lean`; it does not identify the restricted
module-object mate, so it cannot close the component holes by a one-line application. The new
node search records distinguish these results from missing specialized theorems.

## New nodes

`stage3-sfb-open-base-change-component-mono` and
`stage3-sfb-open-base-change-component-section`, in chapter `sec-six-functors-basics`, unit
`sk-def-sfb-open-base-change`, with one new module per statement.

## Second reading by C3

The following is the retained record of the interrupted attempt; its provisional verdicts are
superseded by the resumed reading below.

1. **Statements:** The baseline item statements and definitions were restored byte for byte.
   Verdict: pass.
2. **Proof:** The delivered categorical proof was not retained because it cannot compile against
   the unchanged body within the stage gate. Verdict: no delivery.
3. **New statements:** The two component statements are strict geometric subclaims with matching
   nodes and docstrings. Verdict: pass.
4. **Pruning and route:** The support modules preserve the unit--square--counit route, but the
   unchanged item does not yet import them. Verdict: pass for the standalone support.
5. **DAG agreement:** The support declarations and component nodes agree; the item DAG remains
   unchanged. Verdict: pass.

### Resumed reading, 2026-10-17

1. **Statements and data: PASS.** Compared the delivered item against the current repository.
   Only two plain imports and the bodies of the two inverse theorem proofs change. Every
   original signature, definition body, visibility and public import is byte-identical. The
   two new statements explicitly assume equality to the original exchange formula; both calls
   discharge that equality by `rfl`. No arbitrary witness becomes data of a definition.
2. **Proof and axioms: PASS as decomposition.** Compiled each module in import order through
   `lcompile.py`; no delivered-source warning or error. The item has no sorry. Exactly two
   sorries remain, each the complete proof of its named public component theorem. Examined the
   cancellation orientation: beta followed by alpha is identity on the target; monicity of
   alpha gives alpha followed by beta identity on the source. Mathlib then supplies the natural
   inverse. Printed axioms for both inverse theorems and the parent: only the three permitted
   axioms plus expected `sorryAx`. No forbidden declaration or bypass is present.
3. **Split statements: PASS.** Each statement concerns a single fixed K, hence is a strict part
   of natural invertibility; one asserts monicity, the other existence of a component
   retraction, with no naturality assumed. Both retain arbitrary commutative condensed Λ and
   all original finite-type, separatedness and characteristic assumptions. Tested identity
   squares (identity exchange), the empty open (zero objects), K=0, and non-surjective open
   immersions (the cartesian condition identifies precisely the zero extension support).
   Replaced invalid gluing across an open and a closed complement with the sheaf exchange,
   coefficient-linear lift, exact-derived transport and restriction argument in each docstring.
   New nodes match the exact Lean signatures and record actual independent searches. The
   underlying abelian-sheaf theorem is a useful tool, but does not already state either
   restricted module-object comparison.
4. **Top-down route and pruning: PASS.** Used Mathlib's existing componentwise IsIso and
   monicity criteria for assembly. Kept all existing imports needed by definitions; new
   imports are plain proof-only imports. Removed the duplicate support construction and
   broke the circular inverse proof plans. Listed every old proof dependency removed above;
   no module pruning is claimed. The fixed unit's exchange-then-isomorphism-then-inverse route
   is preserved.
5. **DAG agreement: PASS.** The two existing inverse nodes now describe exactly the categorical
   proofs in the item. The parent node and its proof dependencies stay unchanged. Two new
   nodes carry source, complete proof plans, exact Lean signatures, three kinds of logged
   search, null blueprint.is, worker/item/group creation records, and the same chapter/unit.

Changes made in this resumed reading: connected the two component statements without changing
any public definition; removed the duplicate construction; proved both inverse lemmas; corrected
counts, source explanations, searches and circular node dependencies; reran compilation and
axiom checks. The outcome is explicitly a two-for-two decomposition, not net proof progress.
