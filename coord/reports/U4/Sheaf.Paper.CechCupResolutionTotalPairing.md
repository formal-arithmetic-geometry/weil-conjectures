## What changed

Restored Sheaf.Paper.CechCupResolutionTotalPairing and its exact assigned signature
from the resolved repair record, since the dispatched module and node are absent
from the baseline. Restored the strictly smaller beta-axis obligation in
Sheaf.Paper.CechCupResolutionBetaClassPairing. The main proof constructs a concrete
bilinear map by precomposing the characterized sheaf cup with the two inverse
comparison isomorphisms and postcomposing with the target comparison isomorphism.
The alpha equation is proved using alpha_class and IsModuleCupProduct; the beta
equation follows by applying the separately named obligation and cancelling the
target isomorphism. No arbitrary total pairing is selected and no definition uses sorry.
The public imports supply the unchanged signatures; the beta module is a proof import.

## Proved and sorry left

The restored upper hole cupCechResolution_total_pairing has a complete reduction in Lean;
its module has no sorry. One lower hole remains: cupCechResolution_beta_class_pairing
(lem-sc-cech-cup-resolution-beta-class-pairing). This is a decomposition, not a
sorry-free proof: only the beta-axis compatibility calculation remains, whereas
bilinear-map construction and the alpha-axis equation are proved.
The baseline has neither module, so this restores an assigned item and adds one
tracked hole rather than claiming a net reduction against the current baseline.
Relative to the withdrawn repair source, the total-pairing body was already discharged
and the beta hole was already present: this delivery restores that decomposition.
Relative to the current absent-module baseline, holes closed: none; holes added:
cupCechResolution_beta_class_pairing. Neither declaration is axiom-free, and no
net sorry reduction is claimed. Both modules compile cleanly through lcompile.py. Degree zero has sign one on both
axes; empty or zero inputs satisfy the formulas by bilinearity. No cover hypothesis
is inferred or added: the input comparison data supplies the required isomorphisms.

## No longer needed

None. Both statement imports and the beta proof import are needed. No blueprint
unit statement or realized step is bypassed. No existing module is proposed for pruning.

## Where the brief, the DAG or earlier work was wrong

The brief assumes the item is present and contains sorry, but neither its source
nor its node is in the baseline. The resolved repair note retains the withdrawn
source and signatures. Its old import collision no longer occurs with the current
published build. No dependency adaptations were necessary.
Mathlib searches: LeanFinder returned eight unrelated hits; Loogle and upstream
grep returned zero hits. LeanSearch returned Internal Server Error and is recorded
as unavailable. The existing representatives/pullback compatibility results require
covering and quasicoherence hypotheses unavailable here, and the latter depends
on the former, so neither provides a shorter route.
Read Stacks Tags 0FKV and 07MB: the signed cochain construction is the source for
the beta obligation. The source's covering condition establishes alpha invertibility;
here invertibility is supplied explicitly by the comparison data. The direct
sectionwise beta calculation does not require a cover.

## New nodes

lem-sc-cech-cup-resolution-total-pairing restores the assigned theorem and unchanged
signature from the repair history; its proof records the transport construction and
the two separate axis arguments.

lem-sc-cech-cup-resolution-beta-class-pairing isolates only the beta-axis identity
for a characterized sheaf cup, without asserting existence of a total pairing or
its alpha identity. Its docstring and node detail signed Alexander--Whitney descent,
alpha surjectivity, augmentation compatibility and inverse-iso cancellation.
Searches were rerun; blueprint search for Cech cup found no matching blueprint node.
The unit remains sk-prop-av-cube. Change record:
coord/changes/CechCupResolutionTotalPairing-restoration.md.

## Second reading by U4

1. Interfaces: compared each delivered module with the repository baseline (both
   absent, hence additions against /dev/null), then extracted the withdrawn Lean
   files from coord/repair-notes/Sheaf.Paper.CechCupResolutionTotalPairing.json.
   Both theorem signatures are byte-for-byte equal to those withdrawn signatures.
   No existing declaration, definition, or target statement changes. The restoration
   change record now includes both old and new signatures verbatim. Verdict: pass.
2. Proof: compiled both files in dependency order with lcompile.py --all, without
   errors or warnings. Scratch copies with #print axioms for both declarations
   returned exactly propext, Classical.choice, Quot.sound, sorryAx. The sole textual
   sorry is the named beta theorem; no definitions or prohibited declarations occur
   in either delivered file. The local t is built by bilinear composition. Choosing
   cup uses an ExistsUnique characterization, so it determines the map and does not
   choose unconstrained data. Verdict: valid reduction, not an axiom-free proof.
3. Split: checked beta against CupResolutionPairing.restriction, leibniz and
   augmentation_pair and against alpha_f, beta_f, alpha_quasiIso and alpha_class in
   CupCechResolutionComparison. On summands of bidegrees (r,i), (s,j), the product
   sign is (-1)^(i*s) for the library's resolution-first total convention. It gives
   dP(x,y)=P(dx,y)+(-1)^(r+i)P(x,dy); hence boundaries descend. Both axis signs
   equal one. Alpha surjectivity lifts total homology classes to global cycles;
   leibniz supplies the target paired cycle needed by hcup. Beta_f and
   augmentation_pair then yield precisely the remaining equation after C.iso.inv.
   Degree-zero inputs reduce to ordinary tensor of sections; a zero input gives
   zero; an empty index set gives zero Cech cochains in every nonnegative degree.
   No covering or quasicoherence assumption is used: alpha quasi-isomorphisms are
   supplied. Read Stacks 07MB in its surrounding section 20.25 and the final diagram
   of 0FKV. The source uses a cover to establish comparison isomorphisms, while the
   sectionwise product and the explicitly supplied comparisons suffice here.
   Repeated searches with new queries: LeanFinder 'Alexander Whitney product total
   complex augmentation resolution homology' gave unrelated Dold--Kan and
   representation-resolution results; Loogle '"homologyMap", "total"' and upstream
   grep 'AlexanderWhitney|augmentation.*pair|total.*pairing' gave zero hits. Local
   searches locate representatives, Godement pairings and augmentation lemmas, but
   none proves the arbitrary-U beta identity; representatives additionally assumes
   a cover and quasicoherence. Beta retains only one compatibility square, whereas
   the main body constructs the bilinear map and proves its alpha square. Its named
   hole, source, proof docstring and node agree. Verdict: true, needed decomposition;
   closing beta is a substantial total-complex construction, not a quick repair.
4. Route and pruning: followed the main body downward. exists_unique_moduleCupProduct
   supplies cup and its characterization, alpha_class proves the alpha square, and
   beta_class_pairing supplies the beta square; iso cancellation has the correct
   direction on both axes. Both public imports appear in the signatures; the beta
   import is private to the proof. The withdrawn node's proof_deps are the same
   three nodes used now, so none is omitted from No longer needed. The unit
   sk-prop-av-cube has empty realized statement/step arrays in the baseline; this
   delivery leaves them and the general-cube route unchanged. Verdict: pass.
5. DAG: checked each Lean signature against lean.statement and each proof step
   against the declarations it uses. The main node records transport, alpha
   characterization and beta cancellation; the beta node records the remaining
   cochain calculation. New-node source, search, origin, created, blueprint, chapter,
   unit and lean fields are present. Added def-sc-module-cohomology-cup-product to
   the main stmt_deps because its prose explicitly cites that notion; proof_deps
   already contained it. Verdict: pass after that metadata repair.

Second reading changed only the main node's missing statement dependency, the
restoration record's verbatim signatures, and this report's baseline/hole accounting
and independent review. No Lean proof or signature needed repair.
