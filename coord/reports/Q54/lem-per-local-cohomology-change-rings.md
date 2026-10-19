## Worker report

### Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-change-rings.json`: statement, now split; statement and statement dependencies unchanged. No Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-ideal-torsion-cech-computation.json`: new statement-only lemma, unsplit; no Mathlib match. It states the explicit extended localization complex calculation of right-derived ideal-power torsion for arbitrary modules over a Noetherian ring.
- `citations.json`: verbatim statement excerpts for every step citation. Search records are in `searches.jsonl`.

### Attachments

None. Searches of `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2` for the item's blueprint tag and local-cohomology/change-of-rings notions found no declaration stating this theorem. The upstream master checkout was read only as reference and supplies no attachment. The item has no existing Lean audit declaration.

### WANTED

None: all needed sources are available in `literature/stacks-project/`.

### What was wrong or missing

The item was a correct, unsplit statement with no proof. Stacks 0DXA (local-cohomology.tex, `lemma-cd-change-rings`) allows arbitrary rings and a finitely generated ideal, while this node intentionally assumes both rings Noetherian and defines local cohomology as right-derived ideal-power torsion. Those assumptions make its module interpretation correct. No statement correction or dispute was needed.

The source's short reference to derived base change should not be expanded by assuming ordinary tensor is exact: the ring map need not be flat. I instead used the explicit restriction-of-scalars calculation of dualizing.tex 0BJB (`lemma-local-cohomology-and-restriction`), together with its Noetherian module interpretation 0956 (`lemma-compute-local-cohomology-noetherian`). This is the same extended-localization-complex argument used for 0ALZ in 0DXA's cited proof. The item writes the fraction identification and the vanishing argument itself. A new node stating the restriction comparison or the inequality would obscure that argument, so neither was created.

### Unfinished work

The one new foundational computation is deliberately unsplit. Its source proves it from the Noetherian derived-torsion comparison and the extended Cech model; a later worker can split that computation. Everything required for this item's one-level split is present. No Lean was written, and no compiler, Lake, local DAG check, or local preflight was run.

## Search and route audit

I read the chapter `sec-deligne-laumon-a1` and unit `sk-p-dl-a1-perverse`, and inspected the ancestor `lem-per-artin-gabber-affine-curve` and the parent `lem-per-isolated-intersection-dimension-bound`. This item supplies the change-of-rings inequality used in the parent's Step 4. Its provenance passes through the complete-local connectedness and finite-coefficient potential-dualizing inputs of the ancestor's Step 1. No chapter or unit route or unit realization field was changed. The new node inherits that exact ancestor, with the current item prepended to `via`.

Whole-DAG searches used the tags 0DXA, 0ALZ, 0BJB, 0956 and 0A6R, their lemma labels, local-cohomology/derived-torsion words, and Cech/localization words, and I read the statements of the nearby candidates. Whole-blueprint searches with `tools/blueprint_refs.py search` used `cd-change-rings`, `local cohomological dimension`, `Cech`, `local cohomology`, `local-cohomology`, `cohomological dimension`, `0956` and `0BJB`. No blueprint node states the item or the new computation, so `same_as` is empty.

Mathlib searches were made through the required `msearch.py`, including two semantic phrasings for the new lemma, Loogle, LeanSearch and two grep queries; the item was separately searched with two ring-change phrasings, LeanSearch and grep. The item retains Q41's historical searches as instructed and adds the searches from this run. The new node records only searches actually run in this sandbox's log. All services responded. I read the returned hits and LocalCohomology.lean, particularly lines 40–47 and 161–174: the Cech characterization is explicitly future work, and the present definition is a colimit of Ext. The same-radical theorem has one fixed coefficient ring; Krull-dimension inequalities are not cohomological-dimension inequalities. Module-localization results do not prove the right-derived torsion computation. Consequently neither delivered statement is a Mathlib leaf.

## Not duplicates

- lem-per-ideal-torsion-cech-computation vs lem-sbc-local-cohomology-derived-torsion: the existing statement identifies an Ext colimit with derived torsion, not with any localization complex; it does not supply the new node's computation.
- lem-per-ideal-torsion-cech-computation vs lem-pc-affine-cech-complex: the existing statement assumes the generators span the unit ideal and gives exactness; the new statement allows every ideal and computes potentially nonzero derived torsion.
- lem-per-ideal-torsion-cech-computation vs lem-pc-cech-computes: the existing statement computes sheaf cohomology from an affine open cover, rather than right-derived ideal-power torsion from the extended module complex.
- lem-per-ideal-torsion-cech-computation vs lem-weil-pbc-ring-complex-cech-base-change: the existing statement assumes two chosen augmented complexes already have ordered localization models and proves an augmentation-compatible scalar-extension map is a quasi-isomorphism; it does not identify derived ideal torsion of an arbitrary module with that model.
- lem-per-ideal-torsion-cech-computation vs lem-weil-pbc-ring-complex-functorial: the existing statement concerns functoriality of an assigned family of augmented ring complexes, not computation of derived ideal-power torsion for arbitrary modules.
- lem-per-ideal-torsion-cech-computation vs lem-per-local-cohomology-generator-bound: the existing statement bounds cohomological dimension and adds slicing equations; it does not compute any local cohomology module.

No existing node's source states the same module assertion of 0956. Incidental numeric matches in unrelated search digests and metadata are not source matches.

## Review by Q54

I read local-cohomology.tex 0DXA, including the absence of a flatness assumption for the inequality, and dualizing.tex 0BJB, 0ALZ and 0956 with their displayed complexes. I also read the cohomological-dimension definition 0DX8 and its generator bound 0DX9. The item's Noetherian hypotheses permit finitely many generators of I and identify its right-derived torsion interpretation with the local-cohomology complexes. The new node states exactly the module computation in 0956, with the localization fractions, degree range, alternating differential, and cohomology quotient spelled out; it does not add finite generation of M, locality, a nonzero-ring condition or a proper-ideal condition. Its only notion dependencies are the actual definitions of Noetherianity and the torsion functor, whose full statements I read. Allowing n=0 in that definition or requiring n>=1 yields the same torsion submodule, since n=0 only contributes the zero element.

Step 1 cites `def-weil-pbc-noetherian-ring`, whose statement is precisely that every ideal is finitely generated. The verification that image generators generate IB is written using the defining sums, so this is elementary. No theorem about flat extension of ideals is used.

Step 2 cites the new Cech computation twice, once over A on the restricted B-module N_A and once over B on N. I verified both rings satisfy its Noetherian hypothesis and both lists generate the required ideal. The lemma explicitly allows every module, so N_A need not be finitely generated over A. The finite-length complex also supplies the existence of the least dimension bound by direct inspection of the zero terms. The step does not appeal to a definition node for an unproved computation.

Step 3 uses the exact complex and fraction definitions in that same cited statement. I checked the equality relation: multiplication by t on N_A is multiplication by f(t) on N, so precisely the same relation defines both fractions. The inverse formulas, sums, scalar multiplication and ordered face maps agree. A cochain isomorphism then takes each kernel onto its counterpart and each image onto its counterpart, giving the quotient isomorphism. Forgetting the B-action changes none of those additive groups. Thus this is a written elementary argument from the cited complex calculation, rather than an uncited base-change theorem, an appeal to a node's proof, or a second comparison lemma. I copied the entire cited statement into citations.json so the fraction and complex clauses used here can be checked verbatim.

Step 4 uses only the definition of the least vanishing bound from the unchanged item and the comparison already proved in Step 3. It quantifies over every B-module, not merely B or finitely generated modules. A module whose additive group is zero is zero. Thus the implication covers every j>q, including degree zero when q=-1. No non-elementary fact is hidden in this step.

For small cases I checked I=0 using an empty list (the complex is M in degree zero), I=(1) (the complex is M -> M with the identity), a zero generator (its localization is zero), the zero ring, N=0, f=id and a non-flat quotient f. For example A=k[x], I=(x), B=A/(x) has source dimension 1 and target ideal zero of dimension 0; the localized B-module terms vanish on both sides. For B=A[1/x] the extended ideal is the unit ideal and its cohomology is zero, illustrating the q=-1 possibility on the target. These examples test, rather than exclude, the cases most likely to break the claim.

I checked delivery-errors B–E against the actual two JSON files: the new lemma is a self-contained statement only; its source tag/label is correct; its searches and blueprint provenance are real; it is neither elementary, a duplicate, nor a clause restating the dimension inequality. Each non-elementary use in the item is precisely a cited statement, the use sets equal proof_deps, and no candidate node depending back on this item was cited. The proof has no step longer than 2000 characters. The fraction comparison is deliberately kept in the item's proof. No statement dispute, no SGA citation, no off-unit statement tool and no target modification is involved. This direct-delivery self-review was performed by Q54; there was no second worker and no purported independent review.
