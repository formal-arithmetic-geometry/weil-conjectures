## Files written

- `dag/nodes/sec-smooth-purity/def-sf-pf.json`: definition, split using the existing three constituent definitions; no exact Mathlib match.
- `citations.json`: empty list, because a definition has no proof steps.
- `searches.jsonl`: actual search-command log.

No new nodes or Mathlib leaves. No unit file changed: this item covers the projection clause of `sk-def-sf-exchanges`, not the unit's two exchange transformations, so it is not the node that states the whole unit.

## Attachments

None for the whole item. Searches for `def-sf-pf`, its blueprint tag, and the dual/projection terminology under the read-only `WeilConjectures/` sources found partial interfaces only. I read `AlgebraicGeometry.Etale.dualizingComplex` and `AlgebraicGeometry.Etale.verdierDual` (`SixFunctors/Etale/Derived/Dualizing.lean:84,89`), `AlgebraicGeometry.Etale.DerivedCategory.coefficientDual` (`SixFunctors/Etale/Derived/Perfect/Dual.lean:69`), and `AlgebraicGeometry.Etale.projectionMapOfCompactification` (`SixFunctors/Etale/Derived/LowerShriekProjection.lean:122`). The pro-etale analogues in `SixFunctors/ProEtale/Derived/Duality.lean:73,96,102` also define the two duals and the dualizing object. These are operations for a coefficient category with explicit structural assumptions; they do not give the complete four-stage coefficient formalism, its identification with this datum, and all clauses of this item. No partial declaration is being offered as an attachment. Upstream master was read only as reference, never as proof evidence.

## Wanted sources

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-exchanges/def-sf-pf.md`, complete definition, for def-sf-pf.

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-exchanges/_section.md`, complete unit, for def-sf-pf.

The shared repository has no `literature/blueprint/` directory, and the two read-only source trees have empty blueprint directories. I read the verbatim imported statement/source record in the item and the imported unit and chapter records instead. I do not claim to have opened the missing originals. There is no proof written from an unavailable source: this is a definition, with `proof` empty and `proof_origin` null.

## Statement corrected

STATEMENT-DISPUTED: the imported projection display uses an undeclared $L$ and does not state the projection-variable domains. Type check: $Rf_!K$ lies on $Y$, so tensoring it with $L$ requires $L$ on $Y$; $Lf^*L$ must then lie on $X$. I made these domains explicit as $K\in D^b_c(X,\Lambda)$, $L\in D^b_{ctf}(Y,\Lambda)$, exactly as both the imported unit statement and `def-exchange-projection` state. The earlier dual formulas still have their original $K\in D^b_{ctf}(X,\Lambda)$ domain. No isomorphism claim or coefficient range has been weakened. I also wrote $Ra_X^!\Lambda_s$, identifying the base coefficient unit, instead of the abbreviated $Ra_X^!\Lambda$.

The imported dependency `def-weil-derived-pullback-tensor-hom` was implicit in the text; I now cite it explicitly. The six concrete projection-formula verification nodes remain forward references. Their theorem statements are not assumed or discharged here: the item merely identifies the datum's already stated axiom (A3).

## What remains

Nothing remains for this one-level definitional split. The original blueprint source files remain wanted. A fresh second reader must review and deliver; this worker only runs the required dry run.

## Not duplicates

No new-node pairs arise. Whole-DAG and whole-blueprint searches used `Verdier`, `dualizing complex`, `coefficient dual`, and `projection transformation`. I opened `def-pod-coefficient-dual-on-x`, which defines one dual and its evaluation in the narrower Poincare setting; `def-trf-dualizing-complex`, which defines the finite-coefficient dualizing object, Verdier dual and evaluation under exceptional admissibility; and `def-exchange-projection`, which supplies the projection map together with exchange maps. None is equivalent to the entire composite item, so `blueprint.same_as` is `[]`. Reusing the existing constituent definitions avoids creating a node for any of these clauses.

## Review by Q28

I checked the imported item against the imported unit `sk-def-sf-exchanges` and chapter `sec-smooth-purity`, and opened the full statements of all three statement dependencies. No new node needs a source or proof review. The unavailable original files are identified above rather than represented as read.

`def-sf-datum` actually supplies the global finite-field and four coefficient stages, the finite-Tor categories, the six operations and internal Hom, and axiom (A3). Its statement lists these data itself; its back-reference to this item is an existing pointer, so retaining this dependency does not add a reverse edge. `def-weil-derived-pullback-tensor-hom` actually defines derived pullback, tensor and internal Hom at finite, integral, rational and algebraically closed stages, including completed integral operations and common-stage operations; I did not identify these categories with the discrete-field etale category. These two statements provide every ingredient in the two dual formulas. `def-exchange-projection` actually displays the same arrow with $K$ on $X$ and $L$ on $Y$, and the exact domains used in the corrected text. I use its statement, not a construction hidden in its proof.

There are no proof steps or step citations: B1 and C1-C4 therefore call for no invented argument or quotations, and `citations.json` is correctly empty. The split is the naming of notions prescribed for definitions by stage 1 section 3(2), not a proof reduced to restated clauses (D1-D3). No induction, omitted proof detail, compatibility theorem, or new off-unit proof tool is hidden (D4-D5, C7-C8). Statement dependencies are unchanged, so no new cycle is introduced (C6).

For B2-B4 and E1/E4, I checked the source and target of every displayed expression: $a_X:X\to s$, $\Lambda_s$ on the base, $\omega_X$ and $\Lambda_X$ on $X$, and $Rf_!K\otimes^L L$ on $Y$. All schemes and morphisms retain the separated finite-type hypotheses of the datum/unit. For B5-B8 there is no new Stacks-sourced assertion or claimed Mathlib leaf. Both semantic phrasings, both Loogle queries and both grep patterns are recorded verbatim from real msearch runs; LeanSearch returned HTTP 500 and is recorded as unavailable. I read the returned abstract/underived internal-Hom interfaces and did not mistake them for this geometric definition. For B9-B10, the blueprint searches and partial Lean coverage are recorded above.

For E2-E3/E5-E7, the small-case checks are type checks rather than unproved isomorphism claims: $K=0$ and $L=0$ still give meaningful expressions, $X=s$ and $f=\mathrm{id}$ introduce no new domain restriction, and empty $X$ is not excluded. No theorem about these cases is asserted as a proof step. The important correction was the missing domain of $L$; no false source assertion was reproduced. The projections' concrete verification and coherence remain the six existing forward pointers. The original `import_flags`, blueprint import metadata, audit data and pointers are preserved.

Validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q28 def-sf-pf --no-push` printed OK with preflight passed. After correcting one source-declaration line reference in this report, the same dry run was repeated on the final sandbox. Nothing was pushed.

## Second reading by Q28

Independent second reader, 2026-10-16. I read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the stage-1 definition rule, the original imported item, its unit and chapter, and the current statements of all three dependencies. The originals named by the source fields are absent: the repository has no literature/blueprint directory and both read-only upstream blueprint directories contain no files. This item has no Stacks tag and introduces no Stacks-sourced lemma; the available source evidence is the verbatim imported node/unit, not an opened original or a substitute Stacks reference.

Checks, by clause and dependency:

- Dualizing-complex clause: compared with the imported item, def-sf-datum and the exceptional inverse-image formula; PASS, with the already explicit base unit Lambda_s retained.
- Verdier-dual clause: compared with the imported item and the internal-Hom operation in def-weil-derived-pullback-tensor-hom; PASS, the input remains D^b_ctf(X,Lambda).
- Coefficient-dual clause: compared with the imported item and the same internal-Hom definition; PASS, Lambda_X is the coefficient unit and no biduality or perfection theorem is asserted.
- Projection clause: compared with sk-def-sf-exchanges and the complete current def-exchange-projection, especially its chosen-compactification and final coefficient-domain paragraphs; FIX, retain the displayed arrow and variable domains while making the construction's comparison prerequisites explicit.
- Axiom/verification clause: compared with the quantifier preceding (A1)–(A6) in def-sf-datum; FIX, A3 is quantified over finite-Tor inputs, rather than the entire larger finite-coefficient domain of the concrete map. The six verification nodes remain pointers, not premises or proofs.
- Statement dependency def-sf-datum: checked its statement, not its forward pointer to this item; PASS for the field/coefficient datum, finite-Tor categories, supplied operations and A3 on its own domain.
- Statement dependency def-weil-derived-pullback-tensor-hom: checked all four coefficient paragraphs; PASS for the displayed operations, with integral completion and common-stage interpretations preserved.
- Statement dependency def-exchange-projection: checked the actual counit/tensor composite and all supplied higher-coefficient comparisons; FIX to the item's description, because the current constituent does not assert an unconditional compactification-independent map on every higher-coefficient domain.
- Proof steps: NONE (the proof array is empty); PASS under stage 1 section 3(2), which splits definitions by naming their constituent notions. There are no elementary labels or hidden proof-step citations to audit, and citations.json remains the true empty list.
- New nodes: NONE; PASS, there is no smaller assertion to remove, duplicate, or relabel as a Mathlib leaf.

STATEMENT-DISPUTED: the first worker's sentence identifying A3 with invertibility on the preceding whole domain was broader than the axiom as actually stated. The logical domain check is visible already on the point X=Y=Spec(k): for n=2 and E=Q_ell, the complex K=Z/ell in degree zero is bounded constructible over A=Z/ell^2 but is not of finite Tor amplitude. Its periodic free resolution has differential multiplication by ell, so tensoring with Z/ell gives nonzero Tor in every positive degree. With L=A the concrete projection map is meaningful (and the identity case is invertible), but K is not an admissible input to A3's finite-Tor quantifier. I therefore state the exact finite-Tor scope of A3 separately from the larger finite-level domain whose concrete verification is still pointed to. This corrects the earlier review's implicit domain attribution; it does not withdraw the concrete finite-coefficient projection formula.

The constituent definition now explicitly keeps a compactification superscript until comparisons intertwining its composites are supplied. I made that requirement visible here, including the completed integral and rational/common-stage interpretations. I added no theorem of independence, preservation, or coefficient compatibility. On K=0, L=0, empty X, X=Spec(k), and f=id, the formulas remain well typed. For n=1 the coefficient ring is a field; n=0 is excluded already by the datum, and no assertion has been silently extended to it.

I independently repeated whole-blueprint searches for coefficient dual and projection transformation, read def-pod-coefficient-dual-on-x and def-trf-dualizing-complex, and confirmed that neither states the complete item. Fresh Mathlib queries used the more general vocabulary of monoidal units, closed internal Hom and exceptional pullback. LeanFinder returned over-category adjunctions and underived Scheme.Modules pullback; Loogle returned abstract closed-monoidal currying identities; grep returned ten unrelated occurrences of dualizing. I read Mathlib's ihom definition (CategoryTheory/Monoidal/Closed/Basic.lean:76) and the Cat.opFunctor context (CategoryTheory/Category/Cat/Op.lean:12–30). They presuppose or define different structures. Actual queries/results were appended to searches.jsonl and recorded in the item. No new leaf or exact attachment results.

I also reread the partial upstream declarations cited in the first report: Etale.dualizingComplex, Etale.verdierDual, Etale.DerivedCategory.coefficientDual, Etale.projectionMapOfCompactification, and the ProEtale dual definitions. They match the displayed recipes in their own ambient coefficient-category interfaces, but do not identify the completed/rational/common-stage formalism of this whole item; no attachment is claimed and no compiler was run.

Downstream check of the scope clarification: lem-sf-tensor-hom and thm-sf-kunneth-relative apply A3 to finite-Tor inputs in the supplied datum; the latter also needs its asserted operations to preserve that domain. thm-sf-pf-finite supplies the separate larger finite-level assertion, and prop-sf-pf-reduction, thm-sf-pf-adic, thm-sf-pf-field and thm-sf-pf-proetale supply their own reduction/realization claims. prop-sf-pf-coherence and lem-sf-kunneth-coherence state the required map compatibilities separately. thm-sf-global-duality, thm-sf-verdier-exchange, thm-sf-identification and def-sf-kv-maps retain the same dual formulas. No reverse dependency was added. Existing out-of-item issue reported upward here: def-sf-pairing attributes an evaluation map to this node, whereas this node defines only the dual object; that citer must obtain evaluation from the tensor–internal-Hom adjunction (or its existing evaluation definition). The original imported item already omitted this evaluation map, so this is not a new break caused by the repair.

Changes: clarified A3's exact input domain; exposed the current constituent's compactification/comparison prerequisites and coefficient interpretations; appended independent search evidence. All displayed formulas, existing statement dependencies, blueprint metadata, pointers, first-worker sections and empty proof/citation arrays were retained. No new nodes or Mathlib leaves.

Second-reader validation: the required `deliver.py Q28 def-sf-pf --no-push` printed `OK (not pushed) deliver/Q28/def-sf-pf at 1e358f2f88: preflight passed`. The delay was shared-tool contention; no check failure was reported. The final delivery command is run after this record is appended.
