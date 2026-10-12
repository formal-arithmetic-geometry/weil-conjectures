## What changed

Marked `CategoryTheory.exists_site_system_strictification_data` with
`STATEMENT-DISPUTED` while preserving its signature, docstring and original named
sorry. Added two fully proved modules:

- `Sheaf.CategoryTheory.SiteSystemStrictificationObstruction`: proves that an
  infinite preorder with a greatest element cannot have the asserted strict
  coefficient system over a singleton source category together with finite
  coverings and Mathlib's indexed base-change axiom.
- `Sheaf.CategoryTheory.SiteSystemStrictificationRefuted`: proves the negation
  of the complete original universally quantified signature at universe zero.
  It constructs and verifies every input hypothesis, assumes the original
  conclusion, and applies the obstruction. It does not import the original
  sorry or derive the refutation from any unproved statement.

All three delivered modules compile cleanly through `lcompile.py --all`.
The original statement has not been weakened or replaced. No definitions or
interfaces of existing modules changed; no forced adaptations are necessary.
The source's intended strictification may be valid for a weaker site interface,
but that is a statement correction for a subsequent item, not a silent repair
in this delivery.

## Proved and sorry left

Original holes closed: **0 of 1**. New holes added: **0**. This delivery records a
proved refutation, not a proof or decomposition of the false statement.

The only sorry left is
`CategoryTheory.exists_site_system_strictification_data`, node
`lem-weil-pbc-site-system-strictification-data`, marked disputed.

New fully proved declarations, with no sorry dependencies:

- `CategoryTheory.site_system_strictification_obstruction`, node
  `lem-weil-pbc-site-system-strictification-obstruction`.
- `CategoryTheory.site_system_strictification_data_refuted`, node
  `lem-weil-pbc-site-system-strictification-refuted`.

Their private helper proofs are complete. The earlier sandbox's holed
`strictification_data_from_plan` and its misleading core-node copy were removed.

## No longer needed

No existing library module or DAG node is claimed pruned: there is no valid proof
route for this disputed signature. The original module's imports are retained. In the new refutation module, the
unused `Mathlib.Order.Filter.AtTopBot.Finite` import was removed during second
reading; `Mathlib.CategoryTheory.CodiscreteCategory` is now a plain proof-only
import.
The earlier sandbox-only `strictification_data_from_plan` and
`lem-weil-pbc-site-system-strictification-core.json` were discarded; they had
never been valid dependencies or library declarations.

## Where the brief, the DAG or earlier work was wrong

**STATEMENT-DISPUTED:** the original signature is false, not merely difficult.
`site_system_strictification_data_refuted` is a Lean proof of its full negation
at universes zero. The counterexample is:

- `I = WithTop Nat`, an infinite directed nonempty preorder with greatest element.
- Every `C i` is `Codiscrete PUnit`, a singleton category with a singleton hom
  type. Every `P i` is the top precoverage. All presieves have finite uncurry,
  and the required isomorphism, composition, base-change and pullback axioms hold.
- Every transition `U i j h` is the identity. Equality comparisons give gamma
  with both HEq normalizations and the cocycle. Cover preservation and all
  pullback preservation hypotheses hold. Identity sheaf pullbacks preserve
  finite limits; their adjunction and comparison to the abstract left adjoint
  prove finite-colimit preservation.
- `D = Codiscrete I`, and `v i` is constant at the actual object `i`.
  The unique natural isomorphisms give delta and satisfy normalization and
  coherence. These are actual constructed functors and comparisons.

Suppose the asserted `F, Q, e, v'` exist. At the top index define
`Y i = F(i ≤ top).obj (e i).obj point`. The two strict coefficient equalities
force `(v' top).obj (Y i)` to have label `i`, so `Y` is injective. Essential
surjectivity of `e top` makes every `Y i` isomorphic to `(e top).obj point`.
The identity covering of that object may be indexed by `I`, repeating the
same arrow. For each index choose the pullback of the identity along itself
whose two projections are the corresponding isomorphism from `Y i`.
Mathlib's `Precoverage.IsStableUnderBaseChange` makes the resulting presieve
covering. Its uncurry contains the injective image of `I`, contradicting the
original finiteness clause. The formal obstruction needs only HasIsos and
indexed base change, not any continuity or transition-covering assertion.

This isolates the error in the DAG's step 2: imposing finiteness on the
pair-category coverings is incompatible with the specified indexed axiom.
`Mathlib/CategoryTheory/Sites/Precoverage.lean`, lines 92–98, explicitly says
this axiom is stronger than the corresponding `Pretopology` requirement,
because arbitrary pullback objects need not equal the chosen pullbacks.
`Mathlib/CategoryTheory/Sites/Finite.lean` consequently gives the finite
precoverage HasIsos, but supplies a finite *pretopology*, not an indexed
IsStableUnderBaseChange instance for arbitrary categories. Restricting only
the proposed transport lemma to finite presieves cannot fix the target.

The earlier sandbox attempt was also invalid: it moved the complete assertion
into `strictification_data_from_plan` with an irrelevant `True` hypothesis,
and its report did not describe its actual code. This delivery removes that
relabeling and the worker-written pending second-reading section.

Searches used LeanFinder, Loogle and grep. LeanFinder returned the finite
precoverage/pretopology APIs; Loogle returned the indexed base-change lemma;
grep found no existing obstruction or refutation. LeanSearch reported an
Internal Server Error and is recorded unavailable. The blueprint search found
no strictification node, and the ancestor tool returned no blueprint ancestor.
No unit realization is bypassed: this is a formal counterexample to an
auxiliary statement, not a replacement route for the unit's proof.

## New nodes

`lem-weil-pbc-site-system-strictification-obstruction` is the proved general
obstruction, in `Sheaf.CategoryTheory.SiteSystemStrictificationObstruction`.
Its proof constructs the indexed covering explicitly and uses the coefficient
labels to prove an injection into its uncurry. Small-case checks: its infinite
index assumption excludes a finite family, and its singleton source assumption
is essential to the isomorphism argument. It uses exactly the indexed
base-change axiom appearing in the original statement.

`lem-weil-pbc-site-system-strictification-refuted` is the proved negation of
the original interface at universe zero, in
`Sheaf.CategoryTheory.SiteSystemStrictificationRefuted`. Its proof verifies all
original input clauses before invoking the obstruction. Thus the example does
not rely on an omitted or inconsistent hypothesis. The original statement and
all existing users remain unchanged. There are no change records because no
existing signature or definition changed.

## Second reading by N2

1. **Visible interfaces — pass.** Diffed the existing module against the repository:
   only the five-line STATEMENT-DISPUTED comment was added. Every existing
   declaration signature, body, docstring and import is otherwise byte-for-byte
   unchanged. There are no changed definitions, targets or forced adaptations.
   A scratch Lean example applied the new refutation directly to
   `exists_site_system_strictification_data.{0, 0, 0}`; it compiled, confirming
   the negated proposition matches the actual original elaborated signature.
2. **Proof and trust — pass.** Compiled all three modules in import order using
   lcompile.py, both before and after the import corrections. Scratch #print
   axioms checks show exactly propext, Classical.choice and Quot.sound for both
   new public theorems. Only the unchanged original theorem has sorryAx. Read
   every helper, instance and constructed witness: no hollow definition, new
   sorry, prohibited declaration or choice from an unproved existence theorem.
   The singleton category, functors and comparisons are concrete constructions;
   the only object preimages used come from proved equivalence instances.
3. **New statements — pass.** No holed statements were split off. Both new
   theorems are fully proved. Checked the singleton input satisfies finiteness,
   all four site axioms, gamma/delta normalizations and cocycles, continuity,
   and both sheaf exactness hypotheses. The infinite-index requirement excludes
   finite counterexamples, the point rules out an empty source, and the greatest
   index is what puts the injective family in one fibre. Read Mathlib's indexed
   base-change axiom and finite-pretopology implementation. Independent Loogle
   search `CategoryTheory.Precoverage, Finite`, LeanFinder search for finiteness
   of isomorphism classes forced by indexed pullback stability, and rg searches
   for finite/isomorphism families and strictification obstructions found no
   existing replacement result. The obstruction is strictly smaller than the
   interface and the refutation verifies the complete interface's hypotheses.
4. **Route and pruning — pass with import repairs.** The original false assertion
   remains disputed and unproved, with no claimed proof or net hole reduction.
   Its dependencies are retained because no new proof replaces its route.
   The new proofs use Mathlib directly, plus the obstruction in the refutation;
   no original sorry is imported by either. Checked sk-thm-p1's realized statement
   and steps: this auxiliary counterexample bypasses none and changes none.
   Corrected CodiscreteCategory to a proof-only import in the refutation and
   removed its unused Order.Filter.AtTopBot.Finite import. Other public imports
   supply notation or types used in the statements; pullback proof imports are
   private. No library module or node is claimed pruned.
5. **DAG agreement — pass.** Read both new node files alongside the proofs.
   Their statements, verbatim Lean signatures, proof steps and dependency unions
   agree; source, searches, provenance, creation, blueprint, chapter, unit and
   Lean records are present. The original node retains its plan, since its
   assertion was not proved or modified. The report identifies exactly which
   step of that plan is false and reports the remaining original hole by name.

Second reading changed only the new refutation module's import visibility and
removed one unused import; no proof, statement, definition or node was rewritten.
Added this independent review and the scratch axiom/signature checks. Original
holes closed: 0 of 1; new holes added: 0; proved counterexample declarations: 2.
