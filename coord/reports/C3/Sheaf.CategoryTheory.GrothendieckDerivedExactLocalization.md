## What changed

Repaired `CategoryTheory.grothendieckDerived_exact_localization` from the false
arbitrary-source assertion to the concrete exact abelian module-localization
interface. The statement change and forced parent adaptation are recorded in
`coord/changes/grothendieckDerived_exact_localization.md`. No definition changes.
The parent `grothendieckDerived_compact_localization_model` retains its signature
byte for byte. Its proof uses the new common Gabriel–Popescu presentation and
composes the resulting derived adjunction with the supplied exact equivalence.

## Proved and sorry left

The corrected `CategoryTheory.grothendieckDerived_exact_localization` has a complete
proof, with axioms only `propext`, `Classical.choice`, and `Quot.sound`. This repairs
a false statement; it does not prove the former arbitrary-source statement.
`CategoryTheory.grothendieckDerived_compact_localization_model` has a complete proof
body but still depends on the new presentation theorem and hence on `sorryAx`.

One new hole is added:
`CategoryTheory.grothendieckDerived_gabriel_popescu_presentation`, node
`lem-c3-grothendieck-derived-gabriel-popescu-presentation`, in
`Sheaf.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation`.
It contains the abelian presentation, compact generation and universe transport,
excluding the derived adjunction and counit. Its docstring gives the construction
and the size-extension argument. No other delivered declaration contains `sorry`.
The former false hole is replaced with a proved corrected statement and one true
lower construction hole. This is a repair/decomposition, not positive net hole
closure. No existing true holed statement is closed by this delivery.

## No longer needed

Removed proof import `Sheaf.CategoryTheory.GrothendieckDerivedCompactSource` from
the adapted parent; its node `lem-g2-grothendieck-derived-compact-source` is no
longer used by that proof. The baseline parent DAG omitted this Lean dependency. It does not relate its existential source to A and
in fact constructs the zero category. It cannot supply the common source required
by the repaired localization argument. No unit statement or realized step is
removed. The exact-localization node originally has no proof dependencies to prune. The
parent's old direct dependency `def-pc-compactly-generated` remains required through
the presentation and statement imports; it is not claimed as a pruned node.

The returned obstruction's proof-only imports are not in the repository baseline;
they are not claimed as baseline pruning. The new presentation imports the
triangulated-functor interface rather than the unnecessary derived exact-functor
construction. Remaining public imports supply statement vocabulary; new imports
needed only for proofs are plain imports. Global module pruning is for the ledger
to determine; this delivery removes the compact-source edge only.

## Where the brief, the DAG or earlier work was wrong

The old exact-localization theorem is false for the zero triangulated source and
a nonzero Grothendieck abelian target. Invertibility of the counit would make the
right adjoint faithful, forcing every target Hom set to be a subsingleton. The
fully faithful degree-zero embedding would then force identity equal to zero on
every object of A. The returned obstruction identifies this error correctly.

The first worker's report omitted the new holed presentation module and incorrectly
said there were no new nodes. The second reading corrects that accounting.

## New nodes

`lem-c3-grothendieck-derived-gabriel-popescu-presentation` states the common abelian
module presentation, compact generation, and exact universe-lifting equivalence.
This is the construction portion of the parent's argument, strictly below its
localization conclusion. Sources: Stacks Tags 0F5V, 0F5X, and Baer's criterion
05NU; the universe extension is the agent-written argument detailed in the
docstring. Searches found the small-universe abelian Gabriel–Popescu API but no
complete match for the size-extended presentation with compact derived source.
LeanSearch was unavailable; LeanFinder, Loogle and local source search were used.
Change record: `coord/changes/grothendieckDerived_exact_localization.md`.

## Forced adaptations

`Sheaf.CategoryTheory.GrothendieckDerivedCompactLocalizationModel` (unclaimed)
is adapted only in proof imports and body. Its original application supplies B
where the repaired theorem expects F : ModuleCat S ⥤ A. The presentation theorem
supplies a common ring, abelian adjunction and equivalent compact source; the
parent composes the specific derived adjunction with that equivalence and checks
the composite counit pointwise. No signature or visibility changes. The delivery
tool checks the original against baseline and changed dependencies separately.

## Second reading by C3

1. Compared each existing delivered module with the repository using `diff`.
   The exact-localization signature changes only as explicitly recorded with its
   node's `statement_change`; the parent signature is byte-for-byte identical.
   The new presentation is a declared new module/node. No target or definition
   changes, and the parent interface preserves all downstream statements.
2. Compiled all three modules in import order through `lcompile.py`, without errors
   or warnings after repair. Scanned for forbidden declarations and hollow data.
   Explicit axiom probes show only the three standard axioms for the corrected
   item; the parent and presentation additionally use `sorryAx`, exactly from the
   named presentation hole. There are no definitions choosing arbitrary witnesses
   from that hole: its existential is eliminated only in a proposition proof.
3. Read the split-off statement, docstring and node together. It excludes derived
   localization and has a real free-presentation construction in its proof plan.
   Checked the zero category, the ordinary module category with identity
   presentation, and equal versus larger module universes. The large-coproduct
   hypothesis supplies coproducts in A via the standard t-structure; Baer's
   criterion extends injectivity because ideals of the ring remain w-small.
   Checked Stacks 0F5V, 0F5X and 05NU directly. Independent LeanFinder query on the
   ring as compact generator and Loogle query on the tensor/coyoneda adjunction,
   plus source search for compact generators and Gabriel–Popescu, found no complete
   match. The existing compact-source theorem only constructs the zero category.
   This substantial construction cannot be closed in a few minutes with available
   declarations; no restatement of the derived-localization conclusion was added.
4. The item follows the shortest available route via the source library's proved
   derived adjunction, K-injective preservation, and full-faithfulness instances.
   Public imports support signatures; proof-only imports are private. The unused
   compact-source dependency is listed above. The unit `sk-prop-sf-cbc` has empty
   `realized.statement` and `realized.steps`, and neither is changed; no unit or
   chapter route is bypassed by the below-unit construction repair.
5. Checked both existing node updates against the proofs and the new node against
   its Lean signature. Parent dependencies are exactly the presentation and exact
   localization; the item uses upstream/Mathlib APIs and has no Sheaf proof-node
   dependencies. New-node creation, source, search, blueprint ancestry, chapter,
   unit and Lean records are present. Replaced its top-level Lean-only statement
   with a self-contained mathematical statement; its `lean.statement` stays
   verbatim. Added the missing recorded LeanSearch attempt and ancestry `via`.

Second reading changed four `letI` bindings to `let` to remove compiler warnings,
replaced the new presentation's unnecessarily broad exact-functor import with the
triangulated-functor interface, repaired report hole/pruning/new-node accounting,
and completed the new node's statement/search/ancestry metadata. The proved
argument and corrected signatures were otherwise retained.

## Statement corrected

The exact-localization node's baseline has zero DAG citers (the baseline parent
node omitted the dependency despite its Lean application). The change record
therefore has an empty schema-compliant `citers` list. Its actual Lean user, the
compact-localization parent, is adapted and its DAG proof dependencies repaired
in this delivery. The second reading also repaired the invalid statement-change
record to the required date/by/old_statement/what/source/citers/old_proof schema.

## Forced adaptations

### Sheaf.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
Original against changed dependencies failed:
```
/tmp/forced-adaptation-gqtq3558/lean/Sheaf/CategoryTheory/GrothendieckDerivedCompactLocalizationModel.lean:97:68: error: Application type mismatch: The argument
  B
has type
  Type (max uA vA ((max w vH) + 1))
of sort
  Type ((max uA vA ((max w vH) + 1)) + 1)
but is expected to have type
  ModuleCat ?m.208 ⥤ A
of sort
  Type (max (max vH w) vA (max (max (vH + 1) (w + 1)) w) uA)
in the application
  grothendieckDerived_exact_localization B
/tmp/forced-adaptation-gqtq3558/lean/Sheaf/CategoryTheory/GrothendieckDerivedCompactLocalizationModel.lean:96:9: error: Tactic `rcases` failed: `x✝ : ?m.216` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-gqtq3558/.lbuild) [2.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
