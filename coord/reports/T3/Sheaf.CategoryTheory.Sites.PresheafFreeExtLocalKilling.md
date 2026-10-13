## What changed

Repaired `exists_presheaf_ext_local_killing_witness` in the delivered module. The
vacuous existential proof witness and `True` marker requested by upstream review
#1428 remain removed. The resulting zero is explicitly typed as the Ext group
with source the constructed presheaf `E`, clarifying the degree and coefficient
object without changing the proposition. The proof and sole caller compile.

The witness node's `lean.statement` and `statement_change` record were updated to
match the corrected declaration.

## Proved and sorry left

No `sorry` remains in the delivered module. The following declarations are proved:

- `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness`;
- `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`;
- private helpers `epi_locally_surjective` and `exists_presheaf_cover_lift`.

No new holes were added. Relative to the current repository, holes closed: none;
holes added: none. Both public declarations and both private helpers were
already proved. This delivery has zero net hole reduction and is an interface
annotation repair, not new proof progress.

## No longer needed

No imports, nodes, or modules were pruned. The proof still uses
`Sheaf.CategoryTheory.Abelian.ExtEpiEffacement` and the public Mathlib site and
sheafification interfaces.

## Where the brief, the DAG or earlier work was wrong

The upstream padding repair was already present in the repository from the prior
landing, which caused the previous dry run to report “nothing is proved.” This
repair preserves that corrected conclusion and makes the type of its zero explicit
for the constructed `E`; the node and change record now describe the delivered
interface. No target statement is changed.

## Earlier second reading (a previous round; superseded)

Independent second reading: the witness theorem retains the original hypotheses,
constructed presheaf, local-surjectivity clause, and vanishing equation; only the
vacuous padding is removed and the zero's inferred Ext group is made explicit.
The caller compiles unchanged, and no new node or sorry is introduced.

The statement change is recorded in
`coord/changes/presheaf-ext-local-killing-witness-padding.md`.

## Earlier second reading (a previous round; superseded)

1. **Statements and interfaces.** Compared the delivered module with the
repository version. The existing declarations retain their hypotheses and
conclusions; this delivery only adds an explicit Ext type annotation to the witness conclusion's zero. Padding removal was already landed, and the caller is unchanged.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it contains no
`sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The
public declarations use only the permitted foundational axioms.
3. **Split statements.** No new split-off statements or holes were added. The
corrected witness statement is the direct vanishing assertion required by the
source and is logically equivalent to the former padded presentation.
4. **Pruning and route.** The proof uses the existing Ext epi-effacement node
and the unit's witness route. Both public imports remain needed; no imports or
proof dependencies can be pruned.
5. **DAG agreement.** The witness and caller node Lean statements match the
delivered declarations, and the recorded change identifies the sole interface
adjustment and its caller.

Changed during this second reading: added this review record only; no Lean
proof or statement changes were needed.


## Second reading by T3

1. **Interfaces:** diffed the sole delivered module against the repository.
   All proof bodies, imports and other signatures are byte for byte unchanged.
   The witness conclusion only types its zero explicitly in Ext(Z[E], F, q).
   This is the type already inferred by composition, so the proposition is
   unchanged. The change record now contains complete old and new signatures.
2. **Proof:** compiled the delivered file cleanly with lcompile.py and compiled
   an exact scratch copy with #print axioms for both public theorems and both
   private helpers. Each uses exactly propext, Classical.choice and Quot.sound.
   No sorry or forbidden declaration construct occurs. E is constructed as the
   subtype of pairs, not defined by choosing a witness of an unproved theorem.
3. **Splits and strength:** no new statements, nodes or holes are introduced.
   Read both helpers: the image subsheaf argument proves local surjectivity,
   and the explicit pullback of the generator map gives the cover lift.
   Empty P presents no obstruction; q=1 uses the same positive-degree
   effacement argument, while q=0 is correctly excluded. No restatement with
   sorry is used. The existing witness and caller are both completely proved.
4. **Route and pruning:** read ExtEpiEffacement and the two node proofs.
   Their sole non-elementary dependency is used. The Mathlib type-sheaf epi
   criterion does not directly apply to an abelian-sheaf epi; the generic
   EpiMono criterion requires extra factorization hypotheses. The existing
   small-universe image construction is valid. Both public imports supply
   signature notions; ExtEpiEffacement is correctly a plain proof import.
   No old proof dependency was dropped. sk-prop-cd.realized contains empty
   lists, and no unit step or route was bypassed or changed.
5. **DAG:** the witness proof follows epi effacement, explicit generator-pair
   construction, free extension/sheafification, and Ext associativity; the
   caller applies the witness. proof_deps and proof_origin agree with that
   route. Restored the witness node's lean.statement to the verbatim multiline
   signature. No new-node requirements apply.

Changes during this reading: corrected the report to state zero new holes
closed, made the change record signatures complete, and made the witness node
signature verbatim. No Lean proof repair was needed.
