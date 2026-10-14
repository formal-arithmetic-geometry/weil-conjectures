## What changed

Repaired X-7c2e9 (head 7c2e9037b), A3/mechanical (d): claimed
Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAux
on the project server as an additional interface-change module, held by B2.
Retained the mathematically justified retirement. The forced-adaptation entries
now give full module names and the change record records the actual Aux holder.

Repaired X-472ac (head 472ace8c7), E2 review point 4, by its exact retirement.
EtaleResidueTriplesPrimeLocalizationComponentExtensionAux removes its entire false
etaleResidueTriples_primeLocalization_component_extension_aux theorem and docstring.
The empty module retains its public imports and namespace scaffold and inserts
set_option linter.privateModule false after its imports. Its node has lean: null
and records the finite-field product counterexample and retirement.

EtaleResidueTriplesPrimeLocalizationComponentExtensionExists removes the Aux proof
import and replaces the entire application-based proof with sorry, preserving its
signature, visibility and docstring. Its already-present sandbox adaptation was
verified against the repository original and its proof metadata updated.
The prior retirement of the false factorization theorem and the checked private
certificates in the item's module are retained; that node now records the additional
Aux retirement. Change record: coord/changes/retire-false-component-extension-factorization.md.

## Proved and sorry left

Proved 0 of the item's original 1 sorry. Retired (not proved):
AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_factorization
and AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_aux.
Split off: 0. The only sorry left in delivered Lean files is the restored existing
AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_exists,
node new-lem-sbc-etale-triples-prime-localization-component-extension-exists.
Relative to the repository baseline, the one false factorization hole is retired
and one caller hole is restored; Aux previously had an application proof, not a
separate sorry. The net hole reduction is zero. This is correction/retirement,
not positive proof progress or decomposition.
No sorry remains in either retired module.

The retained private residuePointingCocone, factorization_counterexample and
factorization_statement_refuted remain fully proved; the cocone data is explicitly
constructed. No hollow definition, arbitrary unproved-existence witness or new node
is introduced. The reviewer-supplied finite_field_etale_product_obstruction is
validated separately in scratchpad and has only the standard allowed axioms.

## No longer needed

Removed Aux proof imports:
Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel and
Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxFactorization.
Removed Exists proof import:
Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAux.
Retired nodes new-lem-sbc-etale-triples-prime-localization-component-extension-aux-factorization
and new-lem-sbc-etale-triples-prime-localization-component-extension-aux have lean: null.
Their corresponding modules are no longer imported anywhere in the library after
this delivery. Removed Aux proof dependencies aux-model and aux-factorization, and
Exists proof dependency aux (all with the new-lem-sbc-etale-triples-prime-localization-
component-extension- prefix). AuxModel is not claimed globally pruned.
The item's imports remain required by its checked private certificates.
Unit sk-prop-input-spreading has empty realized entries and is unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the existential Aux statement is false too. Restoring it as a
sorry did not repair review point 4. Over F₂, for every proposed model C, the product
C × C supplies a compatible global pointed triple. Its two projection families embed
H ⊕ H into Hom(C × C,F₂), where H = Hom(C,F₂) is finite and nonempty. Any proposed
cancellation map would inject H ⊕ H into H, contradicting cardinality. This is stronger
than the earlier counterexample fixing the arbitrary model to the identity triple.
The false Aux statement is now retired, rather than retained as an unresolved caller.
The unchanged Exists statement remains the outstanding obligation; the false Aux route
cannot prove it. Common refinements depending on the compatible map remain its proof plan.

The full declaration-user audit finds Factorization and Aux for the first retirement,
and Aux and Exists for the second. These three affected modules are all listed in the
change record. The 159 transitive downstream modules of Aux require no adaptation since
Exists keeps its interface. No new nodes or unit-route changes.
The previous second reading assessed a version returned by X-472ac; its stale verdict
is removed so it cannot be mistaken for review of this repair.

## Forced adaptations

Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAux (B2) originally fails against the retired
factorization declaration: line 60:4 reports unknown identifier
etaleResidueTriples_primeLocalization_component_extension_factorization; line 59:9
reports the resulting rcases failure. Reviewer X-472ac explicitly requires retirement
of Aux's entire docstring and false theorem, rather than restoration as a proof hole.
The adapted empty module compiles. Its public imports are unchanged; only obsolete
proof imports are removed, the theorem/docstring deleted, and the privateModule linter
setting added after the imports.

Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionExists (unclaimed in the local claims snapshot) originally fails against the retired
Aux declaration: line 73:4 reports unknown identifier
etaleResidueTriples_primeLocalization_component_extension_aux, followed by the dependent
obtain failure. Original import line 5 is removed and proof lines 72–87 are replaced by
sorry. These lines used the retired declaration; all signature and docstring text is
byte-for-byte preserved. The adapted module compiles with the delivered dependencies.
Aux is held as an additional interface-change module, not an unheld forced adaptation.
The dry run supplies fresh counterfactual compiler evidence for the unheld Exists module.

## Earlier second reading (a previous round; superseded)

1. Compared all three delivered modules against the read-only repository with
   unified diffs. Exists keeps its signature, visibility and docstring byte for
   byte. The two deliberate declaration retirements are recorded with their exact
   old signatures in coord/changes/retire-false-component-extension-factorization.md.
   No definition or target statement changes. Verdict: pass as a documented
   interface repair, not a proof-only delivery.
2. Compiled the complete three-module set using lcompile.py. Independently read
   the explicit pointing cocone and product counterexample; scratch-copy axiom
   probes show only propext, Classical.choice and Quot.sound for all three private
   declarations. The sole delivered sorry is the named existing Exists theorem,
   with its source, complete proposed argument and existing node. No prohibited
   declarations, hollow data or arbitrary unproved-existence choices. The finite
   field product obstruction also compiles with only the three standard axioms.
   Verdict: pass; retirement is not a proof of the original false statement.
3. No statements are split off and no new nodes are introduced. Checked the
   stronger Aux counterexample independently: over F₂ an étale algebra C is
   finite, Hom(C,F₂) is nonempty by its pointing, and the two coordinate
   projections embed two copies of this finite set into Hom(C×C,F₂). Any
   asserted cancellation map would inject these two copies into one. C cannot
   be the zero ring because it maps to F₂. The identity local triple is obtained
   via localization at (0) of the field. Verdict: both retirements are justified.
4. Searched declaration uses and direct imports over both Lean roots. Aux is
   the only caller of Factorization; Exists is the only caller of Aux. All
   affected modules are delivered together. The obsolete proof imports and
   dependency edges are listed in No longer needed; AuxModel is not claimed
   globally pruned. Read sk-prop-input-spreading.json: its realized lists are
   unchanged and no unit step is replaced. The surviving Exists obligation
   retains the common-refinement route; an invalid uniform cancellation route
   cannot shorten it. Verdict: pass.
5. Compared the three node records with their repository versions and Lean:
   retired nodes have lean null, proof_deps empty, and explicit counterexample
   proof/proof_origin; Exists has its unchanged Lean statement and records its
   unresolved proof without the false Aux dependency. No extra node fields or
   unit records are changed. Verdict: pass.

Second-reading changes: corrected the hole accounting (one original factorization
hole retired, one existing caller hole restored; Aux was not a second original
hole). No delivered Lean changes were necessary. Refreshed scratch axiom probes
and compiled the finite-field obstruction in module syntax.

## Second reading by B2

1. Compared each delivered Lean module with the repository version. The surviving
Exists declaration keeps its signature, visibility, and docstring byte for byte.
The factorization and Aux declarations are deliberately retired and their exact old
signatures are recorded in the change record. Verdict: pass, with documented
interface retirements and the required forced adaptation.

2. Compiled the three delivered modules with `lcompile.py --all`; compilation is
clean. Independently compiled the finite-field product obstruction and axiom probes.
The private certificates use only `propext`, `Classical.choice`, and `Quot.sound`;
the restored Exists hole is the sole delivered `sorry`, and is named in its node.
No hollow definition or prohibited declaration occurs. Verdict: pass.

3. Checked the two counterexamples on the explicit product algebra. The coordinate
maps agree after the diagonal while differing on `(1, 0)`, refuting factorization.
For the existential Aux claim, the finite-field product argument gives the same
obstruction by cardinality. Both retired statements are therefore false; no split-off
statement is introduced. Verdict: pass.

4. Audited imports and declaration users. The obsolete AuxModel and factorization
proof imports are removed, and the Exists proof no longer depends on retired Aux.
The unit record `sk-prop-input-spreading` and its realized route are unchanged.
The change record lists every affected module and the forced compiler failures.
Verdict: pass.

5. Compared all changed node records with the Lean files. Retired nodes have
`lean: null`, empty proof dependencies, and explicit counterexample proof origins;
Exists records its unchanged statement, restored hole, and removed false dependency.
The report and change record document the statement disputes and hole accounting.
Verdict: pass.

Second-reading changes: added this review section and independently refreshed the
compilation and axiom checks. No Lean proof or statement changes were needed.
