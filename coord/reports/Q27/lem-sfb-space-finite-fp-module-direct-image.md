# Stage-1 report: lem-sfb-space-finite-fp-module-direct-image

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-finite-fp-module-direct-image.json`: existing statement, now split in four steps; no exact Mathlib match. Statement and statement dependencies unchanged. Source place now also identifies Tags 03M9 and 07U8 explicitly.
- No new nodes and no new Mathlib leaves.
- `citations.json`: 16 step/node entries, each quoting the relevant statement verbatim; full statements are quoted where several comparison clauses are needed.
- `searches.jsonl`: actual msearch.py log for this worker. The existing item's five inherited searches are retained, with two additional queries actually run here. The repeated original LeanFinder and Loogle queries confirm the inherited hits.

The sandbox initially contained only dispatcher brief markers, with no prior node or report. There is no released repair order for this item in the read repository. The item was unsplit. I worked only in the sandbox and ran no git, Lean, compiler, Lake, or build command in the read repository.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for finite-presentation/direct-image terminology. The scheme theorem `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_unit` in `AlgebraicGeometry/Modules/FinitePushforward.lean:57` needs a locally Noetherian target and only treats the structure sheaf. The same file's finite-locally-free pushforward results require flatness and address a stronger special property. They do not state the present algebraic-space, arbitrary-quasi-coherent-module equivalence. No exact attachment was found.

## WANTED

None. All Stacks sources used are present locally.

## What was wrong or missing

The statement agrees with Tag 0610 and needs no mathematical correction. Its proof was empty. The source mentioned quasi-coherence by a label without its tag; the source field now supplies Tag 03M9 and the affine alternative 07U8. I preserved the inherited blueprint provenance, including its null nearest imported ancestor, as `blueprint_refs.py ancestor` confirms. This is a supporting statement below the inherited compactification/flattening branch, not a new coefficient or six-functor route.

A possible gap in a short localization proof would be to apply the Zariski scheme finite-presentation theorem directly to an etale module. I explicitly use the existing scheme quasi-coherent equivalence, its direct-image comparison, and `lem-sfb-scheme-etale-module-exact-finiteness-comparison`, whose statement includes finite presentation in both directions. No comparison is inferred merely from an equivalence of categories.

## Not duplicates

No new nodes. The DAG already contains the two scheme halves `lem-trf-finite-pushforward-preserves-finite-presentation` and `lem-trf-finite-pushforward-reflects-finite-presentation`; I cite them rather than creating a copy of Tag 05B4 or an algebraic-space clause of the item. Likewise, the scheme finiteness comparison, affine module direct image, chart criterion, and etale restriction comparison all already have nodes. Whole-DAG statement/source searches and whole-blueprint searches for `0610`, `finite finitely presented module`, `finitely presented direct image`, and the broader `finite presentation` found no imported blueprint statement to attach as `same_as`.

## Mathlib searches and readings

I ran the required search command with LeanFinder, Loogle, grep, and LeanSearch, including two natural-language phrasings of the item. LeanFinder and LeanSearch returned the general local-presentation predicates in `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`, not finite direct-image preservation/reflection. I read its `SheafOfModules.IsFinitePresentation` definition at lines 265–278. Loogle returned algebraic finite-presentation facts; I read `Mathlib/RingTheory/Finiteness/ModuleFinitePresentation.lean:70–96`, in particular `Module.FinitePresentation.of_finite_of_finitePresentation` at line 80. It proves finite presentation of the finite algebra as module, not the full sheaf theorem. The grep hit `RingTheory/Extension/Presentation/Basic.lean:120` is an algebra-presentation quotient equivalence and does not supply the sheaf assertion. Thus this item is not a one-line specialization of a Mathlib declaration. The relevant algebra inputs already belong below the existing scheme nodes.

## Review by Q27

I read the source statement and entire proof of Stacks `spaces-descent.tex` Tag 0610, `lemma-finite-finitely-presented-module`, and its scheme input `descent.tex` Tag 05B4 with its affine proof. I also read `spaces-descent.tex` Tag 060T's introductory atlas criterion; `spaces-properties.tex` Tag 03LX; `descent.tex` Tag 05VG and Tag 03LC(3); `spaces-morphisms.tex` Tags 0410 and 03M9; and `spaces-cohomology.tex` Tag 07U8. There are no new-node sources to review. I read the chapter and recorded unit, SETUP's three levels, GOAL, and the current blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images proof. This supporting proof retains the inherited branch and does not alter any unit or chapter.

Step 1 uses `def-trf-algebraic-space` for the scheme atlas and scheme-test representability; `lem-trf-space-fibre-products-etale-covers` states that pulling back the atlas is still a jointly surjective etale family. Finiteness of the pulled-back scheme morphism is exactly the item's scheme-test hypothesis. `def-weil-finite-integral-morphism` says finite scheme maps are affine, and `lem-weil-pbc-affine-morphism-permanence` explicitly supplies quasi-compactness and separatedness. `lem-sfb-space-local-properties-chart-test` includes local finite presentation and permits every pair of charts, so it applies with the identity atlas of the scheme U. Restriction of the local presentations in `def-trf-space-quasi-coherent-module` supplies quasi-coherence of M_U. These statements are sufficient; no base-change theorem for an unstated property is assumed.

Step 2 tests the affine condition on arbitrary affine schemes over Y; finiteness of these scheme tests and affine permanence give affine source. The statement of `lem-sfb-space-affine-module-base-change` explicitly says the affine direct image is quasi-coherent; this is the only clause needed. `lem-trf-space-etale-module-pushforward-restriction` explicitly states the isomorphism after etale localization and its identity on compatible sections with the module action. Thus G is the actual etale direct image used in the item, rather than a different pushforward on the big site. No flatness of f is used.

Step 3 uses `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence` twice: it provides the Zariski module F corresponding to M_U and identifies the two direct images when psi is quasi-compact and separated. These hypotheses were proved in step 1. The statement of `lem-sfb-scheme-etale-module-exact-finiteness-comparison` explicitly equates Zariski and etale finite presentation, with no Noetherian assumption. The two existing scheme pushforward nodes state respectively the forward and reverse implication, under finite, locally finitely presented, quasi-coherent hypotheses, all established here. I did not cite their proofs as statements or duplicate their clauses as new nodes.

Step 4 is elementary composition and restriction of the local presentation witnesses. Its two cited statements give composition/base change of covering families and identify etale tensor restriction with restriction on localized sites, including structure sheaves. Restricting an exact local presentation remains the same local presentation on the smaller slice; in the other direction compose the presentation covers with the atlas. This establishes the atlas test in each direction without invoking stronger fpqc descent. I marked only this step elementary. The steps have lengths 706, 633, 830, and 870 characters; none exceeds 2000 characters or hides a separate standard lemma.

I checked B–E of delivery-errors against the statements and sources: all notions in the unchanged statement are cited or defined inline; no new nodes, elementary helper nodes, duplicate nodes, or one-clause relabellings were introduced. All non-elementary inputs are cited by node, with literal quotes verified against their statements. The proof-dependency list is exactly the union of uses. I checked that none of these dependencies has a path back to the item through statement/proof dependencies. The generic off-unit module/chart results are declared in `split_report.tool_uses`, without writing the maintainer-owned top-level tool_uses field. These support the source's own localization proof and do not replace a step of the unit.

Small cases: zero modules and empty spaces give zero direct image and empty/vacuous presentation witnesses; the identity of an arbitrary non-Noetherian, non-quasi-compact scheme gives precisely the same finite-presentation property on both sides. The finite finitely presented closed immersion Spec(F_p) -> Spec(Z) is non-flat and is allowed throughout. Taking infinite disjoint unions of identity maps shows why no finite atlas or absolute quasi-compactness is used. The finite-presentation hypothesis on f is substantive: for a non-finitely-generated ideal I of A, Spec(A/I) -> Spec(A) is finite, while O on its source is finitely presented and its direct image is not finitely presented over A. The proof retains that hypothesis and never replaces finite presentation by finite type. No source error or statement dispute was found. I corrected an imprecise introductory-section pointer to the verified Tag 060T before validation.

## Unfinished work

No mathematical part of this one-level split remains. Validation and push are performed with the required delivery tool; the maintainer's independent review remains the normal next step.
