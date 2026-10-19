# Worker report: lem-trf-scheme-frobenius-finite-radicial

Files written:

- `dag/nodes/sec-six-functors/lem-trf-scheme-frobenius-finite-radicial.json`: item, split into three proof steps; statement unchanged.
- `dag/nodes/sec-six-functors/lem-trf-relative-frobenius-finite.json`: new statement-only node, unsplit; no Mathlib match for finiteness of the n-fold relative Frobenius of a locally finite type morphism in prime characteristic.
- `dag/nodes/sec-six-functors/lem-trf-finite-radicial-basechange.json`: new Mathlib leaf; four instances give stability of finite and universally injective scheme morphisms under base change and composition.
- `citations.json`: verbatim current statements for every citation of every proof step.

Attachments: none. I read `WeilConjectures/AlgebraicGeometry/Morphisms/Frobenius.lean` (234–246), and the relative-Frobenius declarations in `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Frobenius.lean` (516–556). The retained candidates for the item require an explicit `IsFrobenius` witness on the model map. I retain the earlier decision to split rather than claim an exact attachment under the item's written hypotheses. The latter declarations concern relative Frobenius of an additional morphism, with finiteness hypotheses or explicit witnesses; they do not state the new lemma over an arbitrary characteristic-p base.

WANTED: none.

What was wrong: the earlier report described a removed node and claimed that its replacement gave radiciality, whereas the current replacement states only finiteness. The proof did not write out the iteration identification used for radiciality, and three proof-only dependencies had been inserted in `stmt_deps`. I repaired these, corrected the new nodes’ ancestry `via` lists to include their non-blueprint parent item, made the prime hypothesis explicit in the new lemma (as its cited definitions already require), corrected misleading search verdicts, and regenerated citations from current statements. The item statement and all imported blueprint metadata were retained. Earlier searches and results in `searches.jsonl` were read and reused; the new second phrasing for the finiteness lemma and its Loogle query are logged by msearch and recorded verbatim.

What could not be finished: no mathematical obstruction remains. The new general finiteness lemma is intentionally unsplit, to be taken up as its own stage-1 item. No Lean was written or compiled. Delivery is reserved for the independent second reader.

## Review by Q90

I read Stacks `varieties.tex`, Tag 0CCB (`lemma-relative-frobenius`), Tag 0CCD (`lemma-relative-frobenius-finite`), and Tag 0CCG (`remark-n-fold-relative-frobenius`), including their surrounding definitions and proofs; the tag-to-label correspondence was checked in `tags/tags`. The new finiteness statement assumes exactly a prime p, a characteristic-p base and a locally finite type structure map; the integer n is at least one. Tag 0CCD supplies the one-step assertion, and 0CCG supplies the iteration and its factorization into base changes. No separatedness, quasi-compactness, perfection, reducedness or noetherian hypothesis is required. The item is the scalar-extended q-power map of the current main-20261015 `def-trf-scheme-frobenius` (order 2415), not the relative Frobenius of an arbitrary morphism between separated models. I read the chapter and unit records; this auxiliary node realizes its fixed blueprint ancestor's finiteness/radiciality clause and does not alter either record or any target.

Step 1 uses the definition of finite type to obtain locally finite type, the geometric-fiber Frobenius definition to identify the characteristic-p model, and the new finiteness statement with n=a. Their complete statements were read; each supplies the claim used. The datum has p prime and a>=1, so the new lemma applies even when the scheme is empty or nonreduced.

Step 2 uses the existing one-step relative-Frobenius statement, which explicitly gives a universal homeomorphism without finite-type assumptions. It applies to every twist Y_i over Spec(k_0). I added the universal-homeomorphism and radicial definitions: a homeomorphism after every base change is injective after every base change, and the latter definition states the equivalence with radiciality. The fibre-product definition gives the canonical association of twists and uniqueness from the two projections. The absolute-Frobenius definition gives naturality on structure sheaves by preservation of pth powers. Induction now checks both projections of the composite of one-step maps; it is the a-fold relative Frobenius, rather than an unidentified iterate. The Mathlib leaf supplies composition stability. Finally the finite-field power lemma states c^q=c and the geometric-fiber and absolute-Frobenius definitions identify the map under F_S^a=id with Phi_0. These are explicit arguments from the cited statements, not appeals to the proof of a cited node.

Step 3 uses the geometric-fiber definition and `def-pc-base-change`, whose statement explicitly defines the base change of a morphism as h times the identity. The Mathlib leaf then applies to Phi_0 along k_0 to k. This obtains both desired conclusions for exactly the scalar-extended map in the statement.

I also checked the scalar-stability source in `morphisms.tex`: Tag 01WL (`lemma-base-change-finite`), Tag 0472 (`lemma-base-change-universally-injective`), and the composition statements Tags 01WK and 02V1. The earlier step incorrectly named 01WH, which defines finite/integral morphisms; I corrected it to the stability tags.

For the Mathlib leaf I read `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean` lines 55–62 (composition and base-change instances) and `Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean` lines 88–94 (the corresponding two instances). Each clause is a single instance, and radicial versus universally injective is the equivalence explicitly stated in the existing definition node. The source names and line numbers are recorded in the leaf. I retained the failed grep attempts with their supplied extra Mathlib/ directory prefix, as well as the successful corrected grep results, and corrected the exact-name Loogle match verdict. This is a leaf, so it has no proof.

For B1–B9 and D1–D4 I checked the new files themselves: both are self-contained statements with definition dependencies, neither contains a hidden proof, and the general relative-Frobenius lemma is a geometric input before the finite-field specialization and scalar extension. It is not a renamed clause of the item. The scalar-stability statement is a Mathlib leaf. Neither depends on this item. DAG searches by the tags, relative Frobenius, finite/radicial stability, and the Mathlib names, plus whole-blueprint searches (`relative Frobenius`, `Frobenius finite`, `0CCD`, `universally injective`), found no equivalent existing node. In particular `i-relative-frob` is downstream of the item through its definitions and cannot be cited without a cycle; it also has separated-model hypotheses.

Small cases checked: for X=Spec(F_p[t]) over F_p, the n-fold map is finite with spanning monomials of exponents less than p^n; for F_p[epsilon]/epsilon^2 the map kills epsilon, but remains finite and universally injective, so reducedness is unnecessary. The empty scheme satisfies the statement; n=1 is precisely 0CCD. For a nonperfect characteristic-p field base, the twist must be retained, as in the new statement; it is identified with X_0 only after the finite-field calculation in the item. Nonseparated models such as the doubled-origin affine line remain covered by the general Stacks results. For the stability leaf, identities, empty schemes, arbitrary nonflat base change and two successive morphisms all lie within the four unconditional Mathlib instances.

No SGA source was used. Every non-elementary input in the three steps is a cited node, and every citation is backed by a verbatim quote in citations.json. No live file, launcher, Lean source, compiler or build tool was changed or run.

## Not duplicates

lem-trf-relative-frobenius-finite vs lem-trf-relative-frobenius-universal-homeomorphism: the existing node gives integrality and universal-homeomorphism for a one-step relative Frobenius with no finite-type assumption; the new node gives finiteness under locally finite type for any positive iterate.

lem-trf-relative-frobenius-finite vs lem-trf-scheme-frobenius-finite-radicial: the new node treats an arbitrary characteristic-p base and the Frobenius-twisted target, and gives only finiteness; the item specializes to a finite field, identifies the model endomorphism, proves radiciality, and extends scalars to its algebraic closure.

lem-trf-relative-frobenius-finite vs i-relative-frob: the existing node concerns a morphism between geometric scalar extensions of separated finite-type finite-field models, with a twist by the scalar-extended q-power map; it depends on this item and cannot supply the arbitrary-base relative p-power finiteness input.

lem-trf-finite-radicial-basechange vs lem-weil-pbc-finite-morphism-permanence: the existing node gives finite base change, affineness over an affine target and properness of a composite with a proper map; the new Mathlib leaf also gives composition of finite maps and stability of universal injectivity under base change and composition, which the existing node does not state.

## Second reading by Q90

- Item statement: reread against `varieties.tex` Tags 0CCB, 0CCD and 0CCG and the current `def-trf-scheme-frobenius` blueprint update; the finite-field datum, finite-type hypothesis, scalar-extended affine map, finite/radicial conclusions, and absence of separatedness or reducedness all agree, including the empty and nonreduced cases. Verdict: pass.
- Step 1: checked the structure map, finite type implying locally finite type, characteristic- $p$ inheritance, and the application of the relative-Frobenius finiteness statement with $n=a$ against Tags 0CCD/0CCG and all three cited node statements. Verdict: pass.
- Step 2: checked the fibre-product identifications $Y_i^{(p/S)}\cong Y_{i+1}$, both projection equations in the induction, the use of universal-homeomorphism to universal-injectivity/radiciality, composition stability, and $F_{k_0}^a=\operatorname{id}$ against Tags 0CCB/0CCG and each cited definition/lemma. Verdict: pass.
- Step 3: checked that the displayed morphism is exactly the base change of the model map and that the Mathlib stability instances apply to both properties, against the geometric-fibre/base-change definitions and the cited Mathlib source lines. Verdict: pass.
- `lem-trf-relative-frobenius-finite`: reread as a statement-only node against Tags 0CCD and 0CCG; hypotheses and the $n\geq1$ edge case are exact, and the field, empty scheme, and nonreduced examples satisfy it. Blueprint ancestry, definition dependencies, source place, and recorded failed searches are present. Verdict: pass.
- `lem-trf-finite-radicial-basechange`: reread the statement and Mathlib lines 55–62 and 88–94; the four named instances give precisely finite/universally-injective base-change and composition, with radiciality supplied by the cited Stacks equivalence. The identity, empty, and arbitrary-base-change cases cause no exception. Verdict: pass.

Changes made during this second reading:

- Added three independently phrased msearch records (LeanFinder, Loogle, and grep) for the Mathlib stability leaf; the results corroborate the recorded declarations and do not change its status.
- No node statements, proof steps, dependencies, or citation quotes required repair after the source, DAG-duplicate, blueprint, and edge-case checks.

## Dry-run repair

The first required `deliver.py --no-push` reached server preflight and returned two formatting diagnostics for the Mathlib leaf: its combined citation brackets were not recognized as node references, and `mathlib_match.line` was missing even though the file strings contained the verified lines. I separated the two definition citations, supplied line 60 and spelled out all four declarations and their source lines in `how`, then refreshed the affected verbatim quotes. No mathematical statement changed in this repair.
