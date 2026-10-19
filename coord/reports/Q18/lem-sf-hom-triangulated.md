# Worker report: lem-sf-hom-triangulated

## Files written

- `dag/nodes/sec-six-functors/lem-sf-hom-triangulated.json`: the corrected statement and three-step split, using existing definitions and the existing ringed-site internal-Hom theorem; no exact Mathlib match.
- `report.md`: repaired source comparison and complete evidence appendices. This is packaged at `coord/reports/Q18/lem-sf-hom-triangulated.md` by the delivery tool.
- `citations.json` and `searches.jsonl`: standalone sandbox evidence, whose exact complete contents are reproduced below in this report. They are not separately packaged by the current delivery tool.
- `sources/lem-sf-hom-triangulated.md`: sandbox reference copy of the exact archived blueprint source read for this repair; not a delivered node.

New nodes: 0. New Mathlib leaves: 0. Only the sandbox was written. No Lean was written and no compiler, Lake command or build was run: the human's stage-1-only instruction governs the generic repair brief's request to compile. The required dry run is performed with `deliver.py --no-push`; a fresh second reader delivers afterward.

## Attachments

None. The source search for `lem-sf-hom-triangulated` found no exact project declaration. The internal-Hom/triangulated search found related infrastructure and results restricted to lisse Weil sheaves, which do not give this arbitrary-ring, arbitrary-complex assertion. The earlier reading of `SixFunctors/Etale/Derived/Hom.lean`, `Derived/AdjunctionShift.lean` and `CategoryTheory/DerivedCategory/Monoidal/Closed.lean` found a closed-structure derived Hom and adjunction, second-variable shifts, and an explicit outstanding comparison with the concrete K-injective model, respectively. No exact attachment is claimed from these constructions.

## WANTED

None for this split. The previous report's claim that the exact blueprint source could not be found was wrong. It is available in the launcher literature archive at `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-rf-shriek-preservation/lem-sf-hom-triangulated.md`; that is the physical copy read here. The canonical project-relative source path in the node remains `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-rf-shriek-preservation/lem-sf-hom-triangulated.md`. The archive's `COMMITS.txt` identifies master commit `967897d1c5e775be739997d7e847a9205fae1359`.

## Repair F1: exact blueprint comparison

I read the complete exact master source, including its front matter, statement and proof, rather than relying on the imported DAG transcription. A literal comparison after removing front matter and surrounding whitespace confirms that the source statement equals the shared imported node's statement and that its proof equals the shared imported proof paragraph. The corrected sandbox statement preserves the original text through both displayed triangles, all six complexes, the arbitrary commutative ring, arbitrary scheme and both distinguished-triangle hypotheses. Its changed final explanation specifies the ringed-site operation and the size convention instead of pointing at a pro-étale coefficient-stage definition. The source and the correction therefore differ only at the previously disputed typing reference and its explicit interpretation, not at the claimed exactness conclusions or their hypotheses.

The source proof actually writes `I → M`. The corrected first step uses `M → I(M)`, as required by a K-injective resolution. The source next invokes the contravariant shifted-cone identity, and then the covariant cone identity with a degreewise-injectivity justification. The two corresponding exactness steps here cite the existing generic ringed-site theorem, whose statement supplies exactly these conclusions and shifts. This realizes the source's Hom-complex/cone route using an already reviewed theorem; it does not replace any step of the exceptional-inverse-image unit above this item. Stacks `sites-cohomology.tex`, Tags 08J7 (`section-internal-hom`) and 08JC (`lemma-RHom-triangulated`), was also read from the sandbox reference copy. Tag 08JC explicitly treats both variables on any ringed site and proves the claim by termwise split sequences, omitting details. Those details are in the existing generic node, not asserted from definitions here.

## Source error

STATEMENT-DISPUTED: the imported and exact blueprint statements quantify over complexes on the small étale site for an arbitrary commutative ring, but refer to `def-weil-derived-pullback-tensor-hom`. Its current statement defines finite-level operations on `D(W_proet,A_E,n)`, integral operations with completed coefficient sheaves on the pro-étale site, and subsequent rational/common-stage operations. Already `A = Z`, `X = Spec Z` gives an input outside those signatures. An arbitrary étale complex is not thereby an input of the cited pro-étale finite-level operation; no comparison equivalence was supplied.

The corrected item uses `def-pur-derived-internal-hom` on `(X_Et,A_X)` and identifies `D(X_Et,A)` with `D(Mod(A_X))`. This repairs the operation's type while keeping the source's intended étale exactness assertion. It adds no geometric restriction, coefficient restriction, boundedness or finiteness hypothesis. The K-injective arrow is corrected as above. K-injectivity alone does not imply degreewise injectivity; cone exactness uses finite biproducts and termwise split sequences and needs no such assertion. These are defects of the node-level source argument, not of the chapter or unit route.

## What was wrong in the earlier delivery

F1 was the false missing-source claim, now removed and replaced by the exact source comparison above. F2 was a packaging mismatch: the sandbox files existed, but `deliver.py` reads them for checks and commits only node files and `report.md` (plus permitted unit realization fields when present). Thus the prior packet did not contain the evidence despite the report's implication that it did. The two complete evidence files are now embedded verbatim in the report's named appendices. Since the report is delivered, their contents survive in the delivery tree without changing the launcher or relying on untracked sandbox files. The SHA-256 checks below allow a second reader to verify the extracted bytes against the sandbox originals.

The mathematical split returned as type-correct and acyclic is retained. Only its repair/source metadata and one search-result description were corrected: the first étale semantic search's actual log lists derived-category structure and Yoneda results, rather than the earlier report's generic mapping-cone description. No query was invented or retroactively inserted into the search log.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for internal Hom, triangulated, and 08JC identify the existing `lem-weil-pbc-ringed-internal-hom-exact-restriction` as a more general tool. Its exactness clauses are reused; no child restates either clause of the item. Other imported internal-Hom nodes concern definitions, perfect inputs, coefficient comparison, or Weil structures, and do not state the same arbitrary étale assertion. The item's `blueprint.is` is unchanged and `same_as = []`.

## Review by Q18

For the item I read the exact master blueprint source described above, the chapter and unit records, and Stacks 08J7 and 08JC. There are no new nodes needing separate source reviews. I also read the full existing ringed-site tool statement and its signed-cone argument, without using its proof as a substitute for its statement. The off-unit citation is declared in `split_report.tool_uses`: it is generic ringed-site homological algebra, and no statement of this unit provides that infrastructure.

For step 1 I opened each of `def-weil-pbc-etale-site`, `def-weil-size-convention`, `def-weil-pbc-derived-categories`, and `def-pur-derived-internal-hom`. The first defines the site and covers; the second supplies the small skeleton in a universe containing the scheme and coefficients; the third gives the constant sheaf of rings and the derived category with its triangulated structure; the fourth gives the precise K-injective-second-variable internal Hom on a small ringed site. Substituting `O = A_X` is an elementary identification. Existence and descent are not inferred from an unrelated definition to prove exactness: steps 2 and 3 use the generic theorem which already treats this functor.

For step 2 the cited generic theorem's statement says that H sends distinguished triangles to distinguished triangles contravariantly in the first variable, with the corresponding shift sign. With M fixed, the objects therefore appear in the order K'', K, K', and the connecting target is H(K'',M)[1]. For step 3 the same statement supplies covariant second-variable exactness and shifts, retaining the order M', M, M''. The statement explicitly imposes no boundedness or finite-generation condition. These are exactly the non-elementary facts used; both steps cite that theorem and are marked non-elementary. No hypothesis of the theorem is missing: the site is small under the stated convention and A_X is a sheaf of commutative rings.

I checked all six quotes against the current cited statements with whitespace normalization. They are verbatim and cover every citation in every step. The definition quote includes the actual K-injective construction. `proof_deps` is exactly the union of the steps' uses; the five cited nodes are not merged. A traversal of the generic theorem and its dependencies visits 215 nodes with no path back to this item, confirming acyclicity for the added edges.

I rechecked edge cases: zero ring, empty scheme, zero complexes, identity and zero arrows, and unbounded complexes. The zero cases give zero Hom objects and zero triangles; split cone cases retain the required contravariant/covariant orders and shifts. No perfection, constructibility, coefficient invertibility, or finite-dimensionality assumption is needed. Against delivery-errors B–E: there is no new unsplit node with a hidden proof; no elementary fact or item clause is promoted to a node; the two non-elementary exactness assertions are statements of the cited theorem; no omitted Stacks detail is treated as elementary; the site and coefficient types are checked explicitly; all source changes are disclosed.

The recorded Mathlib searches retain the actual tool/query text. The 11 entries in the item all occur in the original 27-entry command-generated log below (which also contains earlier exploratory searches). The two later semantic phrasings give generic derived-category, Ext and Tor infrastructure; valid quoted Loogle searches give no hits; broad grep hits include unrelated substrings. LeanSearch failed with Internal Server Error and is recorded as unavailable, never as evidence of absence. No Mathlib leaf is claimed. This repair creates no new node and makes no new Mathlib search.

## What remains

No mathematical repair remains for this one-level split. The next action is the required dry run, followed by handoff to a fresh second reader. This worker does not push.

## Delivered evidence format

The following fenced payloads reproduce each sandbox file in full, including its final newline. They are evidence inside this delivered report; they are not claims that standalone files are committed by the launcher. A reader can extract the text between each named heading's fence and verify the listed SHA-256. The source copy is also reproduced to make the F1 comparison reviewable directly from the packet.

## Exact master blueprint source

SHA-256: `9566ef04ec2a93998faaa686034d5cb65ffcaf42e10ba6b3bb93f41b5e76ac41`.

```markdown
+++
id = "lem-sf-hom-triangulated"
kind = "lemma"
title = "Exactness of the internal Hom in each variable"
order = 2081
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-pbc-etale-site", "def-weil-pbc-kinjective-resolutions", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $A$ be a commutative ring, let $X$ be a scheme and let
$K',K,K'',M,M',M''$ be complexes of $A$-modules on $X_{\Et}$. If
$K'\to K\to K''\to K'[1]$ and $M'\to M\to M''\to M'[1]$ are
distinguished triangles of $D(X_{\Et},A)$, then the sequences

$$
R\mathcal Hom_A(K'',M)\to R\mathcal Hom_A(K,M)\to R\mathcal Hom_A(K',M)
\to R\mathcal Hom_A(K'',M)[1],
$$

$$
R\mathcal Hom_A(K,M')\to R\mathcal Hom_A(K,M)\to R\mathcal Hom_A(K,M'')
\to R\mathcal Hom_A(K,M')[1]
$$

are distinguished triangles, the internal Hom being that of
[def-weil-derived-pullback-tensor-hom], computed by a K-injective
resolution of the second variable.

## Proof

Choose a K-injective resolution $I\to M$, which exists by
[prop-weil-pbc-kinjective-resolutions-exist] and
[def-weil-pbc-kinjective-resolutions]. By
[def-weil-derived-pullback-tensor-hom] the object
$R\mathcal Hom_A(K,M)$ is represented by the Hom-complex
$\mathcal Hom^\bullet_A(K,I)$, and represent the first variable by a
complex of the same name. The Hom-complex of complexes of modules is
triangulated in each variable: the standard termwise identity
$\operatorname{Hom}^\bullet(\operatorname{Cone}(u),I)\cong \operatorname{Cone}(\operatorname{Hom}^\bullet(u,I))[-1]$ exhibits the
first sequence as a triangle, and the identity
$\operatorname{Hom}^\bullet(K,\operatorname{Cone}(v))\cong \operatorname{Cone}(\operatorname{Hom}^\bullet(K,v))$, valid because a
complex of injectives is degreewise injective, exhibits the second. This
is the basic homological algebra of the Hom-complex, and it applies to the
sheaves of [def-weil-pbc-etale-site] termwise because the Hom-complex
is formed degreewise in the abelian category of module sheaves.
```

## citations.json

SHA-256: `f6babaaade4d0bcc70971383fa0287a589a7c2a95569c19620a6a53f5db545e4`.

```json
[
 {
  "step": 1,
  "node": "def-weil-pbc-etale-site",
  "quote": "For a scheme $T$, the *small etale site* $T_{\\Et}$ has as objects the etale\nmorphisms [def-weil-pbc-scheme-conventions] $U\\to T$, as morphisms the\n$T$-morphisms between them, and as covering families the finite or arbitrary\njointly surjective families $\\{U_i\\to U\\}$ of etale morphisms. Fibre products\nexist in $T_{\\Et}$ and are computed as scheme-theoretic fibre products, so\n$T_{\\Et}$ is a site with finite limits."
 },
 {
  "step": 1,
  "node": "def-weil-size-convention",
  "quote": "Fix Grothendieck universes $\\mathcal U\\in\\mathcal V$ containing the schemes\nand coefficient rings under consideration. Replace every site by a\n$\\mathcal V$-small skeleton within the chosen bound. Derived categories and\nfiltered colimits are formed in $\\mathcal V$."
 },
 {
  "step": 1,
  "node": "def-weil-pbc-derived-categories",
  "quote": "For a scheme $T$ let $T_{\\Et}$ be its small etale site [def-weil-pbc-etale-site], and for a commutative ring $R$ let $R_T$ be the constant sheaf of rings on $T_{\\Et}$ [def-weil-pbc-constant-sheaf] and\n$\\Mod(T_{\\Et},R)=\\Mod(R_T)$ the abelian category of sheaves of $R_T$-modules [def-weil-sheaf-of-modules-category], [def-weil-pbc-etale-sheaves]. Define\n\n$$\n D(T_{\\Et},R)=D(\\Mod(T_{\\Et},R))\n$$\n\nto be its derived category [def-weil-abstract-derived-category]: the localization of the category of cochain complexes of $R_T$-module sheaves at the quasi-isomorphisms, with its triangulated structure. "
 },
 {
  "step": 1,
  "node": "def-pur-derived-internal-hom",
  "quote": "Let $\\mathcal C$ be a site whose underlying category is small and $\\mathcal O$ a sheaf of commutative rings on $\\mathcal C$ (a ringed site); let $\\Mod(\\mathcal O)$ be its abelian category of sheaves of $\\mathcal O$-modules [def-weil-sheaf-of-modules-category] and $D(\\mathcal O)$ the derived category [def-weil-abstract-derived-category] of $\\Mod(\\mathcal O)$, the localization of the category of cochain complexes of $\\mathcal O$-modules [def-pc-cochain-complex-modules] at the quasi-isomorphisms [def-pc-quasi-iso-modules]. For complexes $\\mathcal L^\\bullet,\\mathcal M^\\bullet$ of $\\mathcal O$-modules, let $\\mathcal Hom^\\bullet(\\mathcal L^\\bullet,\\mathcal M^\\bullet)$ be their Hom complex [def-pur-hom-complex], with terms $\\prod_{p\\in\\mathbf Z}\\mathcal Hom_{\\mathcal O}(\\mathcal L^p,\\mathcal M^{p+n})$ and differential $d(\\varphi)=d_{\\mathcal M}\\circ\\varphi-(-1)^n\\varphi\\circ d_{\\mathcal L}$. Every complex $\\mathcal M^\\bullet$ has a K-injective resolution $\\mathcal M^\\bullet\\to\\mathcal I^\\bullet$ [def-pur-kinjective-complex], which can be chosen functorially in $\\mathcal M^\\bullet$ [prop-pur-kinjective-resolutions-exist]; fix such a functorial choice $\\mathcal M^\\bullet\\mapsto\\mathcal I^\\bullet(\\mathcal M^\\bullet)$. For $L,M\\in D(\\mathcal O)$, represented by complexes $\\mathcal L^\\bullet$ and $\\mathcal M^\\bullet$, the *derived internal Hom* is\n\n$$\n R\\mathcal Hom_{\\mathcal O}(L,M)\n =\\mathcal Hom^\\bullet\\bigl(\\mathcal L^\\bullet,\\mathcal I^\\bullet(\\mathcal M^\\bullet)\\bigr)\\in D(\\mathcal O).\n$$"
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-ringed-internal-hom-exact-restriction",
  "quote": "The functor $H$ sends distinguished triangles in either variable to distinguished triangles (contravariantly in the first variable), and commutes with shifts with the corresponding sign of the shift. No boundedness or finite-generation condition is imposed on the three objects."
 },
 {
  "step": 3,
  "node": "lem-weil-pbc-ringed-internal-hom-exact-restriction",
  "quote": "The functor $H$ sends distinguished triangles in either variable to distinguished triangles (contravariantly in the first variable), and commutes with shifts with the corresponding sign of the shift. No boundedness or finite-generation condition is imposed on the three objects."
 }
]
```

## searches.jsonl

SHA-256: `55f8fbb2f1303c6995bba6cd2963770795a9e4c872a597f0e50ceedd113307d6`.

```jsonl
{"t": "2026-10-15T22:54:55Z", "tool": "leanfinder", "query": "internal Hom complex mapping cone triangulated in first variable cochain complexes", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CochainComplex.mappingCone.triangle", "CochainComplex.mappingConeCompTriangle", "CochainComplex.mappingCone.triangleh", "HomotopyCategory.mappingConeCompTriangleh_distinguished", "CochainComplex.mappingConeCompTriangleh", "HomotopyCategory.mappingCone_triangleh_distinguished", "CochainComplex.mappingConeCompTriangle_obj₂", "CochainComplex.mappingConeCompTriangle_obj₁"], "digest": "5f8b89cd14d8dc21"}
{"t": "2026-10-15T22:54:56Z", "tool": "loogle", "query": "CochainComplex.HomComplex mappingCone", "sub": "", "ok": true, "n_hits": 0, "note": "loogle: Unknown identifier `mappingCone`", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T22:54:56Z", "tool": "grep", "query": "HomComplex|mappingCone", "sub": "Mathlib/Algebra/Homology", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T22:56:37Z", "tool": "leansearch", "query": "derived internal Hom on etale sheaves is triangulated in each variable", "sub": "", "ok": false, "n_hits": 0, "note": "service unavailable: Internal Server Error", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:05:00Z", "tool": "leanfinder", "query": "derived internal Hom on etale sheaves is triangulated in each variable", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["DerivedCategory.instIsTriangulated", "DerivedCategory.instPretriangulated", "DerivedCategory.instIsTriangulatedHomotopyCategoryIntUpQh", "CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory", "CategoryTheory.Pretriangulated.instIsHomologicalOppositeAddCommGrpCatObjFunctorPreadditiveYoneda", "DerivedCategory.instCommShiftHomotopyCategoryIntUpQh", "HomotopyCategory.instIsTriangulatedIntUpSubcategoryAcyclic", "HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory"], "digest": "7f5b44aa9d0f1017"}
{"t": "2026-10-15T23:05:01Z", "tool": "loogle", "query": "CochainComplex.HomComplex mappingCone", "sub": "", "ok": true, "n_hits": 0, "note": "loogle: Unknown identifier `mappingCone`", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:05:01Z", "tool": "grep", "query": "HomComplex|mappingCone in Mathlib/Algebra/Homology", "sub": "", "ok": true, "n_hits": 25, "note": "", "top": ["Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean", "Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean", "Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean", "Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean", "Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean", "Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean", "Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean", "Mathlib/Algebra/Homology/HomotopyCategory/HomComplexShift.lean"], "digest": "dd13f7269325109f"}
{"t": "2026-10-15T23:05:02Z", "tool": "leansearch", "query": "derived internal Hom on etale sheaves is triangulated in each variable", "sub": "", "ok": false, "n_hits": 0, "note": "service unavailable: Internal Server Error", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:07:35Z", "tool": "leanfinder", "query": "Hom complex mapping cone identity first and second variables cochain complexes", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CochainComplex.mappingCone.map_id", "CochainComplex.mappingCone.id", "CochainComplex.mappingCone.id_X", "CochainComplex.mappingCone.desc_f", "CochainComplex.cm5b.p", "CochainComplex.mappingCone.inr_snd", "CochainComplex.mappingCone.snd", "CochainComplex.mappingCone.inl"], "digest": "f29c6c07ea844627"}
{"t": "2026-10-15T23:07:36Z", "tool": "loogle", "query": "CochainComplex.HomComplex mappingCone homological complex", "sub": "", "ok": true, "n_hits": 0, "note": "loogle: Unknown identifier `mappingCone`", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:07:36Z", "tool": "grep", "query": "HomComplex|mappingCone|Hom.*Cone|Cone.*Hom", "sub": "Mathlib/Algebra/Homology", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:07:36Z", "tool": "leansearch", "query": "Hom complex of cochain complexes identifies Hom of a mapping cone with a mapping cone", "sub": "", "ok": false, "n_hits": 0, "note": "service unavailable: Internal Server Error", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:28:12Z", "tool": "grep", "query": "HomComplex.*[Cc]one|[Cc]one.*HomComplex|internalHom.*[Cc]one", "sub": "", "ok": true, "n_hits": 1, "note": "", "top": ["Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean"], "digest": "60da54acd2caa5bd"}
{"t": "2026-10-15T23:28:12Z", "tool": "leanfinder", "query": "The complex of homomorphisms is an exact contravariant functor: Hom of a cone is a shifted cone", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CategoryTheory.Functor.IsHomological.exact", "CategoryTheory.Functor.map_distinguished_op_exact", "CategoryTheory.Functor.homologySequence_exact₁", "CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₁", "CategoryTheory.Functor.homologySequence_exact₂", "CategoryTheory.Functor.homologySequenceComposableArrows₅_exact", "CategoryTheory.Functor.homologySequence_exact₃", "DerivedCategory.triangleOfSESδ"], "digest": "a7f6c6ff948f0690"}
{"t": "2026-10-15T23:28:12Z", "tool": "loogle", "query": "\"HomComplex\", \"cone\"", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:30:22Z", "tool": "grep", "query": "isKInjective.*mappingCone|mappingCone.*isKInjective|KInjective.*cone", "sub": "Algebra/Homology", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:30:22Z", "tool": "leansearch", "query": "If two complexes in a distinguished cone triangle are K-injective then the third is K-injective", "sub": "", "ok": false, "n_hits": 0, "note": "service unavailable: Internal Server Error", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-15T23:30:22Z", "tool": "leanfinder", "query": "mapping cone of a morphism between K-injective complexes is K-injective", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CochainComplex.cm5b.instInjectiveXIntMappingConeIdI", "CochainComplex.cm5b.i", "CochainComplex.isKInjective_of_injective_aux", "CochainComplex.cm5b.p", "CochainComplex.IsKInjective", "CochainComplex.isKInjective_of_injective", "CochainComplex.cm5b", "CochainComplex.cm5b.i_f_comp_assoc"], "digest": "d8e868358bdba831"}
{"t": "2026-10-15T23:30:22Z", "tool": "loogle", "query": "IsKInjective (mappingCone f)", "sub": "", "ok": true, "n_hits": 0, "note": "loogle: Unknown identifier `IsKInjective`", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T00:18:59Z", "tool": "grep", "query": "internalHom.*(IsTriangulated|[Dd]istinguished)|[Rr]hom|derivedInternalHom", "sub": "", "ok": true, "n_hits": 25, "note": "", "top": ["Mathlib/Analysis/CStarAlgebra/GelfandDuality.lean", "Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean", "Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean", "Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean", "Mathlib/Analysis/CStarAlgebra/PositiveLinearMap.lean", "Mathlib/Analysis/CStarAlgebra/Spectrum.lean", "Mathlib/Analysis/CStarAlgebra/Spectrum.lean", "Mathlib/Analysis/CStarAlgebra/Spectrum.lean"], "digest": "6985fd25cdb4e73c"}
{"t": "2026-10-16T00:18:59Z", "tool": "leansearch", "query": "derived internal Hom on a ringed site sends distinguished triangles in both variables to distinguished triangles", "sub": "", "ok": false, "n_hits": 0, "note": "service unavailable: Internal Server Error", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T00:18:59Z", "tool": "loogle", "query": "\"internalHom\", \"IsTriangulated\"", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T00:18:59Z", "tool": "leanfinder", "query": "derived internal Hom on a ringed site sends distinguished triangles in both variables to distinguished triangles", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["DerivedCategory.instIsTriangulated", "DerivedCategory.instPretriangulated", "DerivedCategory.mem_distTriang_iff", "DerivedCategory.instIsTriangulatedHomotopyCategoryIntUpQh", "DerivedCategory.triangleOfSESIso", "DerivedCategory.triangleOfSES_distinguished", "DerivedCategory.triangleOfSESδ", "DerivedCategory.triangleOfSES"], "digest": "9d14defb38bdb16c"}
{"t": "2026-10-16T00:19:18Z", "tool": "grep", "query": "\\bRHom\\b|derivedInternalHom|internalHom.*(IsTriangulated|distinguished)", "sub": "Algebra", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T00:19:18Z", "tool": "leanfinder", "query": "derived sheaf Hom is an exact bifunctor on the unbounded derived category of modules on a site", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CategoryTheory.Abelian.Ext.mapExactFunctor", "CategoryTheory.Abelian.Ext.mapExactFunctor_hom", "CategoryTheory.Functor.instLinearDerivedCategoryMapDerivedCategory", "Ext", "CategoryTheory.Tor'", "CategoryTheory.Tor", "CategoryTheory.Abelian.Ext.mapExactFunctor_zero", "DerivedCategory.instLinear"], "digest": "d71a8886323c6cf7"}
{"t": "2026-10-16T00:19:18Z", "tool": "loogle", "query": "\"sheafHom\", \"derived\"", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T00:28:53Z", "tool": "leanfinder", "query": "RSheafHom distinguished triangles both variables", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CategoryTheory.sheafHom", "CategoryTheory.Pretriangulated.preadditiveYoneda_map_distinguished", "DerivedCategory.triangleOfSESδ", "DerivedCategory.triangleOfSES", "DerivedCategory.triangleOfSES_mor₁", "CategoryTheory.sheafHom'", "DerivedCategory.triangleOfSES_mor₂", "CategoryTheory.ShortComplex.ShortExact.singleTriangle"], "digest": "fd5620d220ae803d"}
```

## Second reading by Q18

- Item statement: checked against the exact blueprint source and Stacks Sites Cohomology Tags 08J7 and 08JC; verdict: faithful after the documented repair from the pro-étale operation to the ringed-site internal Hom, with all hypotheses and both triangle clauses retained.
- Step 1: checked the cited site, size, derived-category, and internal-Hom statements; verdict: each supplies the stated type identification and K-injective model, and the substitution $\mathcal O=A_X$ is elementary.
- Step 2: checked the cited generic ringed-site exactness statement; verdict: its contravariance and shift clause gives exactly the reversed triangle and no extra hypothesis is used.
- Step 3: checked the same cited statement; verdict: its covariance and shift clause gives exactly the second triangle, including the stated unrestricted complexes.
- New nodes: none; no B1–B7 node audit is applicable, and whole-DAG searches found the existing generic ringed-site theorem rather than a duplicate to create.
- Citations: checked every `citations.json` quote verbatim against the current cited node statements; verdict: all six quotes support the uses and the dependency graph is acyclic.
- Edge cases: checked zero ring, empty scheme, zero complexes, split/identity triangles, and unbounded complexes; verdict: all remain well typed and the conclusions reduce to zero or split triangles as expected.
- Changes made: appended this independent second-reading record only; no node, statement, proof step, citation, or search record required repair.
