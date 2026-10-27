# Stage-1 report: lem-trf-sharp-section-basic-chart-data

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-sharp-section-basic-chart-data.json`: statement, split into seven explicit proof steps; Mathlib verdict no full match. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the seven step citations.
- `searches.jsonl`: actual searches recorded by msearch.py, retained unchanged.
- `report.md`: this report.

## Attachments

None. Searched the whole project `lean/WeilConjectures/` for the blueprint id and for sharp monoid / monoid-spectrum / basic-chart terminology. No project declaration states the item. Ringed-space results do not supply an attachment.

## WANTED

None. Read the available ILO PDF directly with pdftotext, PDF pages 104--105, printed pp.98--99.

## Corrections and scope

The imported node had a statement only, not a proof. The statement and its two statement dependencies remain unchanged. The proof expands ILO VIII 3.1.8(i)--(ii), whose proof leaves the sheaf construction as straightforward, using the monoid conventions of 3.1.1--3.1.3. Its omitted details are supplied here rather than hidden in a fresh node. In particular the extension is defined on representatives and its well-definedness uses integrality of P, not cancellativity of the target sheaf.

Read the chapter, unit and current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`. The ancestor's current contracting-correspondence route no longer uses this historical alteration branch. This assigned item is a valid supporting monoid lemma in the live DAG and is handled without changing the chapter, unit or ancestor. The recorded ancestry remains historical. No SGA source is used.

## Searches and reuse

Searched DAG and the whole imported blueprint by `sharp`, `sharp stalks`, `monoid` and `localization`; inspected the sharp definition, affine-fan section lemma, parent universal-property lemma and principal-open-face lemma. No new node was needed. The principal-open-face lemma is unnecessary here because restriction compatibility follows directly on numerator classes using the existing canonical localization restrictions.

Ran msearch.py for the item with LeanFinder (two phrasings), Loogle (`"MonoidSpectrum"`), grep (`MonoidSpectrum|KatoFan|sharp.*stalk|sharpening`) and LeanSearch. Loogle and grep returned no hits. Both LeanFinder answers concern locally ringed spaces and ring structure sheaves. LeanSearch returned ring/module statements and `Submonoid.LocalizationMap.lift`; the latter covers a localization extension component, not this full geometric assertion. No hit gives the entire node or a one-line specialization. The prior 2026-10-22 searches in the live item are retained alongside these actual new searches.

## Not duplicates

No new nodes; there are no new/existing pairs requiring distinction.

## Review by O4

I read ILO VIII 3.1.1--3.1.8 at printed pp.98--99 and the full statements of both cited nodes. I checked the construction against the imported statement clause by clause. The six elementary steps are explicit uses of germ equality, the sheaf axiom and monoid definitions, rather than citations to unstated theorems. No standalone lemma has been moved into a new node or used without its argument.

Step 1 uses `def-trf-fine-fan-blowup`, which defines sheaves of monoids on opens and germs as equality after shrinking. A unit section has zero germs because every stalk is sharp. Shrinking gives a cover where that section is zero, and sheaf uniqueness makes it zero. The empty-open case uses the empty cover.

Step 2 uses that definition's exact prime-ideal convention, including the empty prime. I verified both the ideal property and additive closure of the complement. The only algebraic inference is that two elements summing to zero are inverses; a sharp monoid therefore has each summand zero. No integral or local hypothesis is imposed on A.

Step 3 again uses the germ definition: the zero-germ locus is a union of neighborhoods of actual vanishing. This proves openness and section vanishing before continuity is claimed. The same definition explicitly supplies the topology basis D(a), so the inverse-image formula proves continuity for the whole topology.

Step 4 uses the definition's integrality of a fine monoid and its concrete localization in P^gp. Equality p-na=q-ma implies p+ma=q+na in P, since P embeds in its completion. Applying g kills both copies of a. No cancellation is performed in A(V_a). The additive and identity equations prove that the representative formula is a homomorphism; its uniqueness follows by applying an extension to a+(-a)=0.

Step 5 uses exactly the definition of sharpening as identifying elements differing by a unit. Images of units are units, and Step 1 proves these images zero. This establishes descent directly; there is no unstated general quotient theorem.

Step 6 is the only non-elementary input: `lem-trf-affine-fan-localization-sections` explicitly identifies sections on D(a) with P_a/P_a^times and states that the restriction maps are induced by localization. I use only that statement, not its proof. Its hypothesis is fine P, provided by the item. Numerators are preserved; the negative of a is a unit already in P_a, so its class and every restricted class are zero. Equality of the two maps follows on every representative, establishing the precise restriction square for arbitrary basic-open inclusions, without substituting ring localizations.

Step 7 uses only the prime-ideal definition and Step 6. The ideal property gives both directions of D(a) intersect D(b)=D(a+b). Both overlap squares end in theta_(a+b), which is the required agreement after the canonical restriction identifications.

I checked all B--E return categories: source places are exact; no new unsplit statements carry proofs; statement dependencies are actually used; no Mathlib results are claimed without their hypotheses; all citations quote statement text verbatim; the proof dependency union is exact; there is no new edge to the parent or to a descendant using this item. Each step has fewer than 700 characters, so none hides a long lemma.

Small cases checked: T empty (every section monoid is singleton), V empty, P={0}, a=0 (V_0=T), and phi zero (each prime is the permitted empty ideal). For the one-point sheaf with stalk the sharp noncancellative monoid {0,e}, e+e=e, the map N to {0,e} sending 1 to e has V_1 empty and V_0 the point. The formulas and prime property still hold, confirming that no cancellation or integrality of A was tacitly used. For N^2 mapping (r,s) to r in the constant sharp monoid N on a point, the zero face is the second coordinate axis; both full and empty basic inverse images and their restrictions behave as stated.

No statement dispute was found, and no source error is asserted. All proof steps preserve the full given hypotheses and conclusions.

## Unfinished work

None in this one-level split. The two reused nodes retain their own independent proof obligations.
