## What changed

Corrected and proved AlgebraicGeometry.Scheme.Modules.dual_retraction_key in
Sheaf.AlgebraicGeometry.Modules.DualRetractionKey. Added naturality of the
internal-Hom comparison family, then used its specialization, map_id,
homObjMap_comp_homObjMap, the section equation, homObjMap_id and iso cancellation.
Removed the unused proof import Sheaf.AlgebraicGeometry.InternalHomRestrictScheme.
The scheme-sheaf abbreviations in the item are definitionally unchanged.

Adapted the sole caller, Sheaf.AlgebraicGeometry.Modules.DualRetractionOfLocalSection,
by adding the already available he argument at its final call. Its signature,
visibility, imports, and all other lines stay identical.
Change record: coord/changes/S1-dual-retraction-key-naturality.md.

## Proved and sorry left

Closed the hole in the corrected
AlgebraicGeometry.Scheme.Modules.dual_retraction_key
(blueprint: new-sbc-dual-retraction-key). No sorry remains in the item or adapted
module; no holes added or split off. The original arbitrary-family statement is
false, so this is a statement correction plus proof, not a proof of that false
statement or a claim of progress achieved solely by strengthening a hypothesis.
The genuine downstream local-section theorem keeps its exact original statement.

## No longer needed

Removed import Sheaf.AlgebraicGeometry.InternalHomRestrictScheme from the key module:
naturality is now an explicit hypothesis, not obtained by an existential there.
Its node lem-sc-internal-hom-restrict-scheme is not needed by the key proof but
remains needed by the caller to construct a natural comparison. No whole module
is asserted to leave the targets' import closure. The four existing definition
nodes remain the background of the categorical statement. No unit step is bypassed;
sk-prop-input-spreading has no realization of this auxiliary key in its realized list.
No other imports or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The prior decomposition omitted naturality from the key statement, although its
proof explicitly used it. Being pointwise isomorphic does not imply naturality.
The rank-two basis-swap counterexample is detailed in the change record. The
caller already destructures internalHom_restrict_scheme as e, he but formerly
ignored he. This delivery uses it. The cited source is
[Stacks Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP), the dualization step
of (2) to (3); the categorical compatibility is its omitted local detail.
The correction's statement_change records all DAG citers (none in the current
node dependency lists); the actual Lean caller is adapted in this delivery.

The earlier attempts were blocked by the missing published key object. On this
retry the published object is present. Both sandbox modules compile cleanly with
lcompile.py; the dry run now passes the original-caller baseline and establishes
the forced adaptation against the corrected key. No baseline artifacts were
supplied, no tool was modified, and nothing was pushed. The old temporary-baseline
check is not used as evidence. The second reader must perform a fresh reading.

Preflight uses the stage-2 statement-change schema for stage-3 corrections and
requires `statement_change.by` to be `S1 stage 2`. That field follows the required
schema; `proof_origin.by` correctly records `S1 stage 3`. The previous second
reading changed the schema field to `S1 stage 3`, which preflight rejects. This
retry restores the required value without changing the mathematical correction.

## Forced adaptations

Sheaf.AlgebraicGeometry.Modules.DualRetractionOfLocalSection is unclaimed in the
local claim snapshot. Against the corrected key, the original fails at line 45:
`hs` has the section-equation type but the new naturality hypothesis is expected.
The only edit passes `he` before `hs`. The original theorem statement and visibility
are byte-for-byte unchanged. The adapted module compiles in the delivered set. The dry run now establishes
the counterfactual against the actual published baseline and changed dependencies.
The earlier check using temporary baseline artifacts is not used as evidence.


## Second reading by S1

1. Interface comparison: PASS with the declared statement correction. Read both
   complete modules and their diffs against the repository. The key adds exactly
   the documented naturality binder; its sheaf spelling changes are definitional.
   Checked the old and new signatures in the change record and the DAG signature.
   The sole caller changes only `e hs` to `e he hs`; its signature, visibility,
   imports, and construction of the retraction are unchanged. The downstream
   tool and full source search confirm these are the only declaration users.
   No target statement or definition changes.
2. Proof check: PASS. Both sandbox modules compile cleanly via lcompile.py.
   Read the naturality specialization, the direction of contravariant composition,
   the use of hs, and every associativity and inverse-cancellation step. There
   are no sorry, axiom, unsafe, opaque, extern, or implemented_by tokens, no new
   definitions, and no data chosen from an unproved existence theorem in the
   delivered key. Independent scratch copies print the axioms of both the key
   and the downstream local-section theorem; results recorded below.
3. Split statements: PASS, none added. Independently checked the rational
   rank-two counterexample: S squared is identity and D inverse S D S is
   diag(1/2,2), so the old arbitrary-family equation is false. Naturality supplies
   precisely the missing compatibility; zero modules and empty opens cause no
   exception because all steps are categorical identities. The caller already
   supplies naturality from internalHom_restrict_scheme. Read that construction
   and verified the source's dualization step at
   https://stacks.math.columbia.edu/tag/0EKP (proof of (2) to (3)).
4. Route and pruning: PASS. Searched the library with dualMap composition,
   split-monomorphism/retraction, and internal-Hom map patterns, and ran msearch
   grep with `homObjMap.*(comp|id)`. The existing homObjMap composition and identity
   lemmas are already used directly; no replacement theorem was found. The sole
   remaining public import supplies the signature's dualMap API. The removed
   proof import is unnecessary in the key and remains in its caller. All four
   old proof_deps remain represented; no further pruning is claimed. Read the
   unit realized record: this auxiliary key realizes none of its steps, and no
   unit route changes.
5. DAG agreement: PASS. The recorded Lean statement equals the delivered
   signature byte for byte. The proof_deps equal the union of proof-step uses;
   the proof and proof_origin describe the actual naturality/composition proof.
   No new node is introduced. The statement_change and change record disclose
   the correction rather than counting a proof of the false original statement.

Second reading changes: appended this independent review and its verification
results; no Lean, node, or change-record edits were needed. The existing proof
is correct and was left intact. This delivers one corrected and proved theorem,
with zero added or split-off holes; it does not prove the false original claim.

Independent scratch axiom results: both
`AlgebraicGeometry.Scheme.Modules.dual_retraction_key` and
`AlgebraicGeometry.Scheme.Modules.isSplitMono_restrict_dualMap_of_local_section`
depend only on `propext`, `Classical.choice`, and `Quot.sound` (no sorryAx).
The fresh deliver3.py dry run passed compilation, the original-caller baseline,
the forced-adaptation counterfactual, the axiom probes, and preflight with review
class CODEX. The original caller fails against the corrected dependency and the
one-line adapted caller compiles; the diff independently confirms minimality.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Modules.DualRetractionOfLocalSection
Original against changed dependencies failed:
```
/tmp/forced-adaptation-xj8dankf/lean/Sheaf/AlgebraicGeometry/Modules/DualRetractionOfLocalSection.lean:45:36: error: Type mismatch
  hs
has type
  s ≫ (restrictFunctor U.ι).map f = 𝟙 ((restrictFunctor U.ι).obj Q)
but is expected to have type
  ∀ (a : A'✝ ⟶ A✝) (b : B✝ ⟶ B'✝),
    (restrictFunctor U.ι).map (SheafOfModules.homObjMap a b) ≫ (e A'✝ B'✝).hom =
      (e A✝ B✝).hom ≫ SheafOfModules.homObjMap ((restrictFunctor U.ι).map a) ((restrictFunctor U.ι).map b)
the following variables have been introduced by the implicit lambda feature
  A✝ : X.Modules
  A'✝ : X.Modules
  B✝ : X.Modules
  B'✝ : X.Modules
you can disable implicit lambdas using `@` or writing a lambda expression with `{}` or `[]` binder annotations.

(with the modules compiled into /tmp/forced-adaptation-xj8dankf/.lbuild) [5.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
