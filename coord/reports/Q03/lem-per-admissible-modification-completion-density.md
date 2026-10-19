## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-admissible-modification-completion-density.json: item split in six steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- citations.json: one entry for each node used by each proof step, quoting its statement verbatim.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the blueprint id, admissible-modification/completion phrases, and completion/henselization in Blowup found no declaration stating this item. I also checked the read-only master reference. No compiler or Lean-writing tool was used.

## WANTED

None. The ILO source and Stacks algebra/constructions sources are available locally.

## What changed

The item was statement-only, and the sandbox contained dispatch markers only: there was no interrupted delivery or previous split to invalidate. I kept every mathematical hypothesis and conclusion. I added references to the existing fibre-product, geometric-point, colimit and blowup-comparison notions, specifying which canonical map is meant. No STATEMENT-DISPUTED mathematical correction was needed.

The key reusable input already exists: lem-per-admissible-modification-system states the Rees-power congruences for every m and every degree, as well as the filtered preorder and corresponding domination order. I did not create a second lemma for the infinitesimal fibre clause. The generic quotient theorem already exists as lem-trf-closed-immersion-strict-localization-cartesian; it explicitly retains nilpotents and needs no Noetherian hypothesis. I did not create another strict-henselization quotient node.

Whole-DAG and blueprint searches included admissible blowups and completions, infinitesimal closed fibres, strict henselization quotient, Rees powers, and tag 05WS. The blueprint searches found no node stating the whole item; same_as stays empty. I read the unit and chapter records, the current unit proof, and the current ancestor lem-per-artin-gabber-affine-curve Step 3. This item remains the existing descendant completion-congruence input to that step, not a replacement for the unit's Fourier route.

The item's inherited Mathlib searches are retained verbatim. The additional searches were made only through msearch.py and are in searches.jsonl: two semantic phrasings with LeanFinder, LeanSearch, Loogle with AdicCompletion/IsEtale, and a literal grep for blowup/completion and strict-henselization quotients. The returned declarations concern ordinary adic completion, formal smoothness, HenselianRing, perfectoid untilts and Weierstrass preparation; none states the geometric comparison. The Loogle and grep searches returned no hits. Both semantic services answered. No search is recorded as run without a log entry.

## Unfinished

Nothing in this one-level split. Its pre-existing unsplit dependencies remain their own items. No new statement-only obligation is created.

## Review by Q03

I read ILO Expose XX 4.4, printed pp.373–374, including the final Note, and the proof of XX 2.4.4 on printed p.365. The final Note identifies the Rees algebras modulo every power of I; 2.4.4 discusses corresponding strict henselizations and their common exceptional-ideal completion. I checked Stacks algebra.tex Tag 05GG (lemma-hathat-finitely-generated), Tag 05WS (lemma-quotient-strict-henselization) and constructions.tex Tag 01O3 (lemma-relative-proj-base-change), and opened the statement of every node cited in the split. There are no new nodes with separate sources to audit.

Step 1 uses the completion-mod-power node for the actual base map A/I^n -> A'/I^nA', the Rees definition for its graded pieces, and the system node for every J^d/I^nJ^d. The latter really states all m and d, not merely the reduced or first closed fibre. Multiplicativity follows from coefficientwise ring multiplication; finite direct sums suffice, so no interchange with an infinite product occurs.

Step 2 uses the affine blowup and relative-Proj definitions to match the models, the arbitrary-base-change node for both nonflat quotient maps, and the graded-equivalence clause of relative-Proj functoriality for the isomorphism. I checked that the latter's flatness clause is not being used for a nonflat map. The strict-transform comparison node supplies the canonical comparison and its standard-chart formula. Coefficient fractions show that the isomorphism obtained is the reduction of this map. This does not assert that arbitrary base change of blowups is an isomorphism.

Step 3 checks the compatibility that is essential for taking colimits. The system node gives corresponding domination arrows. The open-restriction lemma says they are the identity over U, so the two composites agree over U'. I corrected an initial shortcut here: I do not reapply the henselian-pair system lemma to the completed ring without proving its henselianity. Instead the principalization theorem gives a nonzerodivisor chart equation for the exceptional divisor, and R -> R[1/t] is injective by cancellation. This proves schematic density over A' directly. Finite generation of K extends to KA', and V(KA')=V(IA') follows by inverse image of supports. Properness of Y_J comes from finite generation of J; proper implies separated by the definition node; the schematic-density extension lemma then equates the two X-morphisms. Neither reducedness nor flatness is assumed.

Step 4 uses the geometric closed-immersion quotient statement, not the weaker algebraic quotient node that chooses an unspecified action. It identifies the structural quotient maps D_J -> D_J/I^nD_J and E_J -> E_J/I^nE_J. The chosen points lie over V(I), so the ideal is contained in the relevant maximal ideals. Both points use the same separable residue-field closure, so the fibre isomorphism induces the identity identification there. Functoriality clause (3) gives uniqueness of the local ring map with its specified scheme structural map and residue embedding. Applied to both composites in Step 3, it proves the transition-map equality, not an unverified assertion of naturality.

Step 5 checks smallness and filteredness before using the elementwise filtered-ring-colimit node: the finitely generated ideals of the set A form a set, and the system lemma supplies filteredness. The colimit definition produces u from the compatible maps. I wrote both surjectivity modulo I^n and injectivity out in representatives. In particular, injectivity does not assume that stage maps or u itself are injective: only a finite ideal-membership expression is moved to a common stage, and the elementwise equality criterion then moves the equality to a further stage. The stagewise quotient isomorphism proves the required membership there. Step 6 is the elementary extension-and-power identity, including the equality IC=(u(phi)); phi need not be a nonzerodivisor for this clause.

I tested n=1, the identity case A already complete, the principal ideal case, nilpotent I (where the full-support blowups are empty, so the geometric-point assertion has no instance), the zero ring, and I=0 (again no geometric point on the blowup of the nilpotent full-support centre). The infinitesimal-fibre assertion still holds in these empty cases. No Noetherian, flatness, excellence, reducedness or pre-existing density of U in X was silently introduced. All six steps are below 2000 characters. No hidden comparison lemma remains in a long step, no clause has been moved to a new node, and the proof-dependency union matches the uses. Generic off-unit inputs are declared in split_report.tool_uses for the maintainer's judgment; the closed-immersion strict-localization input has no trace-formula content. I checked dependency closures before using the existing tools and found no path back to the item.
