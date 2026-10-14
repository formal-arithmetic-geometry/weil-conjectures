## What changed

Repaired E2 by adding M : Submonoid c.B and an IsLocalization M t.B hypothesis
for the algebra structure induced by i.hom to
`etaleResidueTriples_primeLocalization_component_extension_epi`.
The corrected theorem is proved directly by Mathlib `IsLocalization.epi`.
Removed the previous delivery's counterexample helpers from the delivered module;
the checked counterexample remains in scratchpad for reference. Updated its node,
statement_change and sole citer. The caller's exact signature and visibility stay
unchanged; its invalid proof is replaced by a documented descent sorry.
No Challenge target or definition changes.

## Proved and sorry left

The corrected `etaleResidueTriples_primeLocalization_component_extension_epi`
has no sorry (1 corrected theorem proved). This does not prove the old false claim.
Closed its old hole by correcting its statement, as explicitly requested in E2.
Restored one hole in the existing
`etaleResidueTriples_primeLocalization_component_extension_unique_aux`, node
`new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux`.
This is the full affine descent obligation, not a new statement or renamed copy
of the epi assertion. It is true by descent retaining the localization model,
as explained in its docstring and node. No new nodes, no split-off statements.
Hole accounting: one corrected hole removed and one caller hole restored;
net zero, not a proof of the original assertion or positive net progress.

## No longer needed

Removed both proof imports from the forced caller:
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAuxCompatible`
and `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAuxEpi`.
The corresponding aux-compatible and aux-epi node dependency edges are removed
from the aux node. Its eventual descent proof must retain localization data;
compatibility alone is insufficient. These two imports are not needed by its
restored whole-proof obligation. No global reachability claim is made.
The previous attempted delivery's `Mathlib.RingTheory.Etale.Pi` proof import and
private counterexample helpers are no longer needed to prove the corrected claim.
Original public imports remain required by its statement; the only new proof
import is `Mathlib.Algebra.Category.Ring.Instances`.

## Where the brief, the DAG or earlier work was wrong

E2 was correct: arbitrary compatible maps need not be localization maps.
The diagonal F → F × F and its first-coordinate pointing satisfy the original
compatibility equations, but the two projections distinguish it from an epi.
The old caller selected an arbitrary compatible model and applied the false
universal statement. Its statement (existence of a particular epic descended
model) remains true, but its proof must construct the localization model.
The corrected localization hypothesis excludes this counterexample. Identity
localizations and canonical localizations satisfy the new hypothesis, and the
proof works for every submonoid, including degenerate localizations. The unit's
realized entries are empty, and no unit or chapter statement or route changes.

## Statement corrected

The old and new exact signatures and all 160 transitive users are in
`coord/changes/etaleResidueTriples_primeLocalization_component_extension_epi.md`.
The sole citing node is
`new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux`:
its former application no longer holds; its unchanged existence statement is
restored as an explicit geometric descent obligation. Its node now records the
complete localization-preserving proof plan instead of the invalid application.
Source: Stacks 00CR, 01ZM, 07RP, 01Z6, 04GW and Mathlib IsLocalization.epi.

## Forced adaptations

`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAux`
is unclaimed. The original caller compiled against the changed epi module fails
at its former line 43 with `Application type mismatch`: the application has type
`∀ (M : Submonoid c.B), IsLocalization M t.B → Epi i`, expected `Epi i`.
Changed the invalid proof body to `by sorry`, completed its required natural-language
proof documentation, and removed its two now unused proof imports. Every existing
signature and visibility remains identical. This restores an honest existing
obligation instead of deriving a localization property from mere compatibility.
The independent reader can repeat the counterfactual with the original caller
in scratchpad/original-caller. No other consumer uses the changed theorem directly.

## Second reading by G3

1. Compared both delivered modules with the repository using diff. The only
existing signature change is the explicitly recorded E2 correction of
`etaleResidueTriples_primeLocalization_component_extension_epi`, including its
unused binder renamings. The forced caller's signature and visibility are byte
for byte unchanged. No definition or Challenge target changes. Checked the
change record against the exact old and new signatures and reran downstream.py:
160 transitive users, with just the existing aux caller using the theorem.
Verdict: the interface change is declared and its sole caller is adapted.

2. Compiled the complete delivered set through lcompile.py without errors or
warnings. Scratch copies with #print axioms show exactly propext,
Classical.choice and Quot.sound for the corrected epi theorem; the restored aux
obligation additionally uses sorryAx. No forbidden declarations or data holes.
Independently recompiled the original caller against the delivered dependency:
it fails at line 43 because the new localization arguments are missing. The
adapted caller compiles. The scratch counterexample also compiles, and its
compatible_non_epi theorem uses only the three permitted axioms. Verdict: the
corrected theorem is proved, and the one reported existing descent hole is honest.

3. There are no new declarations, new nodes, or split-off statements. The restored
aux theorem is true: affine finite-presentation descent, eventual etaleness,
and eventual affineness give a model over R_s whose base change is the specified
local algebra, not an arbitrary compatible algebra. The restricted map to K
supplies its prime and residue-field pointing. Checked the cited descent facts
at [01ZM](https://stacks.math.columbia.edu/tag/01ZM),
[07RP](https://stacks.math.columbia.edu/tag/07RP), and
[01Z6](https://stacks.math.columbia.edu/tag/01Z6).
For the corrected epi statement, identity localizations and submonoids containing
zero obey the general localization theorem; no nontriviality assumption is needed.
The diagonal counterexample to the old statement is excluded by hlocal.
Verdict: the repair does not disguise a restatement as a decomposition.

4. Read Mathlib.Algebra.Category.Ring.Instances.IsLocalization.epi and its
ringHom_ext proof. This is already the shortest direct route for the corrected
claim; the induced algebraMap is definitionally i. Repeated Mathlib search with
`epi_iff|IsLocalization.epi|ringHom_ext` and searched the upstream and Sheaf
descent declarations: no immediate proof of the whole restored aux obligation.
The proof-only import is plain import; the public imports serve the signatures.
The old epi node has no proof_deps. The old aux node's two proof_deps are both
listed under No longer needed and removed with their unused imports. The unit
sk-prop-input-spreading has empty realized lists, preserved by this delivery.
Verdict: imports and dependency pruning agree with the actual repair; no unit
route is bypassed and no whole-library reachability claim is made.

5. Compared both node records with the Lean signatures, proof bodies and source
plans. The epi statement and lean.statement both include the induced-algebra
localization hypothesis; statement_change preserves the exact old statement
and names the sole citer. The aux statement is unchanged, with its failed
compatibility-only proof replaced by the complete localization-preserving
natural-language descent plan. proof_deps and proof_origin match both modules.
Verdict: DAG and Lean agree. The old mathlib_searches fields are historical;
current successful searches are in searches.jsonl and the proof_origin correctly
names the Mathlib theorem actually used.

Second-reading changes: appended this independent review and recorded a fresh
Mathlib search; no delivered Lean or node edits were necessary. The corrected
item has one theorem proved out of one, with no split-offs; its forced caller
has one restored hole. This is a statement repair with net zero holes closed,
not a proof of the original false universal assertion.

## Forced adaptations

### Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAux
Original against changed dependencies failed:
```
/tmp/forced-adaptation-bnsjatz_/lean/Sheaf/RingTheory/EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAux.lean:43:4: error: Application type mismatch: The argument
  etaleResidueTriples_primeLocalization_component_extension_epi R p K χ q ψ hψ hK t c i hα hφ
has type
  ∀ (M : Submonoid ↑c.B), IsLocalization M ↑t.B → Epi i
but is expected to have type
  Epi i
in the application
  ⟨hφ, etaleResidueTriples_primeLocalization_component_extension_epi R p K χ q ψ hψ hK t c i hα hφ⟩

(with the modules compiled into /tmp/forced-adaptation-bnsjatz_/.lbuild) [2.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
