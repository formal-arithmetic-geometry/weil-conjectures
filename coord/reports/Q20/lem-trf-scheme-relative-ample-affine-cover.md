# Repair report: lem-trf-scheme-relative-ample-affine-cover

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-scheme-relative-ample-affine-cover.json`: item; unchanged statement; three-step assembly, 1943 characters.
- `dag/nodes/sec-trace-formula/lem-trf-scheme-etale-separated-space-comparison.json`: statement, status `unsplit`; no Mathlib match; empty proof and proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-affine-base-ample-canonical-data.json`: statement, status `unsplit`; no Mathlib match; empty proof and proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-canonical-proj-open-cover-gluing.json`: statement, status `unsplit`; no Mathlib match; empty proof and proof dependencies.
- `citations.json`: verbatim statement quotations for all six citations in the three assembly steps.
- `searches.jsonl` and `search-results/`: actual logged search results, retained in the sandbox.

## Attachments

None. The project theorem `AlgebraicGeometry.scheme_relative_ample_affine_cover` in `lean/Sheaf/TraceFormula/SchemeRelativeAmpleAffineCover.lean` ends in `sorry`. Searches by blueprint tag, ampleness/locality, canonical Proj and representable separation in `lean/WeilConjectures/` found no project theorem proving the whole item or a new statement. Existing ordinary Proj and ample-pullback results cover only ingredients.

## WANTED

None. All source texts used are present under `literature/stacks-project/`.

## Returned issue and repair

The return asks that the 5454-character proof be spread into at least two comparable statement-only nodes, leaving an assembly of at most 3000 characters. The sandbox initially contained only dispatcher marker files: no prior item, report, citations or search log was available to retain. I copied the live, maintainer-reviewed version as the baseline; it contains the returned seven-step proof. The original statement, source, blueprint ancestry, old Mathlib searches, and all maintainer-owned metadata are retained. No statement dispute or target change was needed.

| New work item | Old steps assigned | Old argument size |
| --- | --- | --- |
| `lem-trf-affine-base-ample-canonical-data` | 1–2 | 1569 characters |
| `lem-trf-scheme-etale-separated-space-comparison` | 3–4 | 1722 characters |
| `lem-trf-canonical-proj-open-cover-gluing` | 5–6 | 1634 characters |

Old step 7 remains the assembly’s final application of the existing reverse canonical-Proj criterion. The three new nodes are independent of one another; their common input interfaces are already existing nodes. A worker can start any one of the three immediately. The new statements introduce all objects and hypotheses and include the identifications the old argument needs. They contain no proof sketches; their arguments are preserved below as handoff material.

## Preservation of every old argument

The following is the baseline proof verbatim, grouped by its new owner. This is handoff material for future workers, not a proof field in any new node.

### lem-trf-affine-base-ample-canonical-data

Old step 1: Put $Z_i=h^{-1}(U_i)$, $h_i:Z_i\to U_i$, and $N_i=N|_{Z_i}$. For an arbitrary affine open $W\subseteq U_i$, the inclusion $W\to U_i$ is affine by [lem-weil-pbc-morphism-affine-schemes-affine]. Its base change $a:h_i^{-1}(W)\to Z_i$ is affine by [lem-weil-pbc-affine-morphism-permanence](1). Here $Z_i\times_{U_i}W=h_i^{-1}(W)$: a map into either side is a map into $Z_i$ whose composite to $U_i$ factors through the open $W$. The pullback $a^*N_i$ is its restriction, since the formula in [def-pc-module-pullback] reduces on an open immersion to $\mathcal O\otimes_{\mathcal O}N_i|=N_i|$. By [lem-weil-pbc-pullback-ample-invertible], this restriction is ample. Moreover $h_i$ is quasi-compact: each affine open $W\subseteq U_i$ is an affine open of $S$, and $h_i^{-1}(W)=h^{-1}(W)$ is quasi-compact by the given quasi-compactness of $h$. These two facts together give $h_i$-ampleness of $N_i$ in the current, quasi-compactness-inclusive sense of [lem-trf-scheme-ample-canonical-proj-criterion].

Cited nodes: `lem-weil-pbc-morphism-affine-schemes-affine`, `lem-weil-pbc-affine-morphism-permanence`, `def-pc-module-pullback`, `lem-weil-pbc-pullback-ample-invertible`, `lem-trf-scheme-ample-canonical-proj-criterion`, `def-weil-finite-type-morphism`.
Source: literature/stacks-project/morphisms.tex, Tag 01VJ (lemma-characterize-relatively-ample), (3) implies (5), with the affine-base reduction justified by the affine specialization of Tag 0892 (lemma-pullback-ample-tensor-relatively-ample)(2).

Old step 2: Apply [lem-trf-scheme-ample-canonical-proj-criterion] to the quasi-compact $(h_i,N_i)$ of Step 1. Its forward implication gives quasi-separatedness of $h_i$, the canonical section algebra $\mathcal A_i=\bigoplus_{d\geq0}(h_i)_*N_i^{\otimes d}$ with evaluation $\psi_i$, the equality $U(\psi_i)=Z_i$, and an open immersion $r_i:Z_i\to\operatorname{Proj}_{U_i}(\mathcal A_i)$. Its final assertion also makes $h_i$ separated. Thus the criterion is applied with its quasi-compactness hypothesis already established; its algebra is formed only after obtaining quasi-separatedness.

Cited nodes: `lem-trf-scheme-ample-canonical-proj-criterion`.
Source: literature/stacks-project/morphisms.tex, Tag 01VJ (lemma-characterize-relatively-ample), local canonical section-algebra maps in the proof of (3) implies (5); Tag 01VI (lemma-relatively-ample-separated).


### lem-trf-scheme-etale-separated-space-comparison

Old step 3: View our schemes as representable algebraic spaces over $S$ [def-trf-algebraic-space]. Check the local $h_i$ against the definitions in [lem-trf-space-qc-separated-etale-local]. For each affine scheme $T\to U_i$, [lem-weil-pbc-qcqs-morphism-permanence](3) makes $q:Z_i\times_{U_i}T\to T$ quasi-compact. Its identity presentation is the required surjective etale presentation by a quasi-compact scheme. Hence $h_i$ is quasi-compact as a space morphism. Its scheme diagonal is a closed immersion by Step 2 and [def-weil-proper-morphism]. Every scheme test of the representable diagonal is a base change of this same scheme diagonal (both fibre products classify pairs with equal image). It is a closed immersion by [lem-weil-pbc-closed-immersion-base-change]. Thus $h_i$ is separated as a space morphism as well.

Cited nodes: `def-trf-algebraic-space`, `lem-trf-space-qc-separated-etale-local`, `lem-weil-pbc-qcqs-morphism-permanence`, `def-weil-proper-morphism`, `lem-weil-pbc-closed-immersion-base-change`.
Source: literature/stacks-project/spaces-morphisms.tex, Tags 03KG (lemma-quasi-compact-local), 03KM (lemma-separated-local), scheme tests; schemes.tex Tag 01K5 (lemma-quasi-compact-preserved-base-change); morphisms.tex Tag 01QR (lemma-base-change-closed-immersion).

Old step 4: The inclusions $U_i\hookrightarrow S$ are etale by [lem-weil-pbc-etale-composition-cancellation](1) and jointly surjective by hypothesis. Apply [lem-trf-space-qc-separated-etale-local] to $h$ and this family, whose base changes are the $h_i$ checked in Step 3. It gives quasi-compactness and separatedness in the space sense. To recover scheme separatedness, take the scheme test $Z\times_SZ\to Z\times_SZ$ equal to the identity in its representable diagonal: the resulting closed immersion is exactly $\Delta_h:Z\to Z\times_SZ$. Thus $h$ is scheme-separated by [def-weil-proper-morphism]; its scheme quasi-compactness is the original hypothesis. Moreover [def-weil-closed-immersion] says $\Delta_h$ is affine, so [lem-weil-pbc-affine-morphism-permanence](3) makes it quasi-compact. Consequently $h$ is quasi-separated by [def-weil-quasi-separated-morphism], as required for the current canonical-Proj criterion.

Cited nodes: `lem-weil-pbc-etale-composition-cancellation`, `lem-trf-space-qc-separated-etale-local`, `def-weil-proper-morphism`, `def-weil-closed-immersion`, `lem-weil-pbc-affine-morphism-permanence`, `def-weil-quasi-separated-morphism`.
Source: literature/stacks-project/morphisms.tex, Tag 01VJ (lemma-characterize-relatively-ample), first paragraph of (3) implies (5); spaces-morphisms.tex Tags 03KG, 03KM; schemes.tex Tag 01KK (definition-separated), and Tag 01K6 (lemma-closed-immersion-quasi-compact).


### lem-trf-canonical-proj-open-cover-gluing

Old step 5: By [lem-trf-scheme-zariski-etale-quasi-coherent-equivalence], $N$ corresponds to a line module on the small etale site of $Z$, and its direct images and pullbacks agree with the Zariski ones under that equivalence. Use [lem-trf-space-section-algebra-etale-base-change] for the quasi-compact separated $h$ from Step 4. It supplies the quasi-coherent graded algebra $\mathcal A=\bigoplus_{d\geq0}h_*N^{\otimes d}$ on $S$ and its evaluation map $\psi:h^*\mathcal A\to\bigoplus_{d\geq0}N^{\otimes d}$. For each $U_i\to S$, it identifies $\mathcal A|_{U_i}$ with $\mathcal A_i$ and the restricted evaluation with $\psi_i$. Its last clause identifies all these maps with the ordinary scheme maps, so the canonical criterion of Step 2 concerns exactly these algebras and evaluations.

Cited nodes: `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`, `lem-trf-space-section-algebra-etale-base-change`.
Source: literature/stacks-project/morphisms.tex, Tag 01VJ (lemma-characterize-relatively-ample), section-algebra and adjunction paragraphs; descent.tex Tags 03DX,03LC and spaces-properties.tex Tag 03LX for the existing comparison interfaces.

Old step 6: Apply [lem-trf-space-line-module-proj-map] to $(h,N,\mathcal A,\psi)$. It gives an open $U(\psi)\subseteq Z$ and a canonical map $r:U(\psi)\to P=\operatorname{Proj}_S(\mathcal A)$. Its restriction compatibility and Step 5 identify $U(\psi)\cap Z_i$ with $U(\psi_i)=Z_i$, and identify the restricted map with $r_i$ under $P\times_SU_i\simeq\operatorname{Proj}_{U_i}(\mathcal A_i)$. Since the $Z_i$ cover $Z$, the first equality gives $U(\psi)=Z$: every point belongs to a $Z_i$ and hence to $U(\psi)$. By [lem-weil-pbc-etale-covering-base-change] applied to the covering family of Step 4 and $P\to S$, the schemes $P\times_SU_i$ form a jointly surjective etale family over $P$. The base changes of $r:Z\to P$ to this family are exactly the open immersions $r_i$ of Step 2. Thus [lem-trf-space-open-immersion-etale-local] implies that $r$ is an open immersion.

Cited nodes: `lem-trf-space-line-module-proj-map`, `lem-weil-pbc-etale-covering-base-change`, `lem-trf-space-open-immersion-etale-local`.
Source: literature/stacks-project/morphisms.tex, Tag 01VJ (lemma-characterize-relatively-ample), conclusion of (3) implies (5); constructions.tex Tag 01O9, spaces-divisors.tex Tag 0D2Z for restriction compatibility.


### Assembly

Old step 7: The original hypothesis makes $h$ quasi-compact, and Step 4 proves it quasi-separated. Steps 5 and 6 give its canonical graded algebra and evaluation with full generation locus $Z$ and canonical Proj map an open immersion. Thus condition (2) of [lem-trf-scheme-ample-canonical-proj-criterion] holds, with all its prerequisites. Its reverse implication gives $h$-ampleness of $N$, which the statement defines to include precisely ampleness of $N|_{h^{-1}(V)}$ for every affine open $V\subseteq S$. This is the required conclusion.

Cited nodes: `lem-trf-scheme-ample-canonical-proj-criterion`.
Source: literature/stacks-project/morphisms.tex, Tag 01VJ (lemma-characterize-relatively-ample), (5) implies (4) implies (1); Definition 01VH (definition-relatively-ample).

The first new statement packages the affine-target argument: smaller affine opens pull back by affine morphisms, tensor pullback is restriction, and affine pullback preserves ampleness; the canonical-Proj criterion is applied only after relative ampleness and quasi-compactness have been established. Its outputs include all local data used later, not merely the existence of some projective embedding.

The second new statement generalizes the old open-cover comparison to an etale scheme cover, without ampleness hypotheses. For this generalization the base changes $h_i$ are quasi-compact by `lem-weil-pbc-qcqs-morphism-permanence`(3); over an affine test, that node’s (2) makes the source quasi-compact, so its identity is a quasi-compact atlas. The representable diagonal tests are base changes of the scheme diagonal. Etale locality then applies in its actual space sense. The identity scheme test of the global diagonal recovers scheme separatedness, and affineness of a closed immersion gives a quasi-compact diagonal. These are exactly the old steps 3–4, now a separate task with their scheme/space comparison stated explicitly.

The third new statement preserves both comparisons in old step 5 (Zariski to etale modules, and restriction of section algebra plus evaluation) and the two descent conclusions in old step 6 (full generation locus, then open immersion after a jointly surjective etale cover of relative Proj). It assumes the local canonical data rather than ampleness, and does not conclude ampleness.

## Mathlib and blueprint searches

Before creation I searched the whole DAG by all cited Stacks tags and by the affine-ampleness/canonical-Proj, etale-separated/representable-space, and section-algebra/gluing concepts. I used `tools/blueprint_refs.py search` with `ample affine`, `separated scheme space`, `section algebra`, `canonical Proj`, `scheme separated`, `etale separated`, and `ample canonical`. No blueprint node states any of the three new statements. `tools/blueprint_refs.py ancestor` identifies `lem-trf-local-term-locality`; each new node has that ancestor and its via list prepended by this item. The item’s historical polarized-descent place is retained. Unit/chapter route records are unchanged.

For each new id I ran two semantic phrasings with LeanFinder, one LeanSearch query, Loogle and an actual Mathlib grep through the required `msearch.py` command. The node records contain the exact query strings and results as returned. All services answered. The ordinary `Proj.fromOfGlobalSections` candidate was read at `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:435–515`: it starts with a graded ring mapping to global functions and does not state any of our relative line-module section-sheaf comparisons. Its chart inclusion and restriction lemmas do not prove an ample module gives a canonical open immersion. `IsSeparated.instQuasiSeparated` and the locality instances at `Morphisms/Separated.lean:60–102` concern schemes only; they do not prove the representable-space comparison. Loogle refinements for `AlgebraicGeometry.Proj.fromOfGlobalSections` and `"AlgebraicSpace"` were also run and logged. Thus all three are unsplit, with zero new Mathlib leaves.

## Not duplicates

- lem-trf-scheme-etale-separated-space-comparison vs def-weil-proper-morphism: the existing node defines scheme separatedness by the closed diagonal and properness; it does not establish etale descent or scheme/space comparison.
- lem-trf-scheme-etale-separated-space-comparison vs def-weil-quasi-separated-morphism: the existing node defines the quasi-compact diagonal condition; it does not prove etale descent or scheme/space comparison.
- lem-trf-scheme-etale-separated-space-comparison vs lem-coef-relative-categorical-cylinder-criterion: the existing statement is about simplicial categorical mapping cylinders and equivalences, not morphisms of schemes or algebraic spaces; the tag collision is not mathematical overlap.
- lem-trf-scheme-etale-separated-space-comparison vs lem-pc-projective-base-change: the existing statement preserves projectivity under base change; it has no representable-space comparison or canonical section-algebra gluing assertion.
- lem-trf-scheme-etale-separated-space-comparison vs lem-pc-quasi-compact-base-change: the existing statement preserves scheme quasi-compactness under base change; it does not establish separation or its representable-space comparisons.
- lem-trf-scheme-etale-separated-space-comparison vs lem-pc-quasi-compact-local-on-target: the existing statement descends only quasi-compactness of scheme morphisms over an open cover; the new statement takes quasi-compactness as input and proves separation plus the representable-space comparison over an etale cover.
- lem-trf-scheme-etale-separated-space-comparison vs lem-pc-separated-quasi-separated: the existing statement only derives scheme quasi-separatedness from scheme separatedness; the new statement establishes separatedness from local scheme data and compares both morphisms with representable-space properties.
- lem-trf-scheme-etale-separated-space-comparison vs lem-trf-space-qc-separated-etale-local: the existing locality statement assumes and concludes space quasi-compactness and separation; the new statement starts from SCHEME separatedness of the base changes and supplies the representable scheme-test comparisons, including recovery of the scheme diagonal.
- lem-trf-scheme-etale-separated-space-comparison vs lem-weil-pbc-qcqs-morphism-permanence: the existing statement supplies qc/qs permanence and base change for schemes; it does not state etale descent of separatedness or agreement with space scheme-test properties.
- lem-trf-scheme-etale-separated-space-comparison vs lem-weil-pbc-qcqs-over-affine: the existing statement concludes the source is qcqs from a qcqs morphism to an affine base; it does not establish separatedness or compare scheme and space tests.
- lem-trf-scheme-etale-separated-space-comparison vs lem-weil-pbc-surjective-universally-closed-separated: the existing statement descends separatedness through a surjective universally closed SOURCE map; the new statement descends from an etale cover of the TARGET and establishes representable-space comparisons.
- lem-trf-scheme-etale-separated-space-comparison vs lemma-nagata-finite-type-to-separated-target: the existing statement concerns cancellation of finite type through a separated target, with finite-type hypotheses absent from the new node.
- lem-trf-affine-base-ample-canonical-data vs def-sfb-relative-section-algebra-canonical-map: the existing node specifies section-algebra and chart-characterization data without an existence assertion; the new statement proves existence and full-generation/open-immersion consequences under its hypotheses.
- lem-trf-affine-base-ample-canonical-data vs lem-pc-chow-relative-ample: the existing statement concerns a given projective-space immersion and proper morphisms in Chow data; the new statement has no such immersion or properness assumption and deals with its own canonical section algebra.
- lem-trf-affine-base-ample-canonical-data vs lem-per-relative-ample-absolute-twist: the existing statement twists a relatively ample module by powers of a base ample module; our affine-base module is already absolutely ample and the conclusion is canonical Proj data.
- lem-trf-affine-base-ample-canonical-data vs lem-per-surface-point-blowup-geometry: the existing statement concerns blowups of a regular excellent surface at a point; the new statement has no blowup, regularity, dimension or excellence assumptions.
- lem-trf-affine-base-ample-canonical-data vs lem-sfb-nodal-log-canonical-reconstruction: the existing statement concerns nodal marked curve families and their log dualizing polarization; the new statement applies to arbitrary qc scheme morphisms without the curve, nodal, proper or Noetherian hypotheses.
- lem-trf-affine-base-ample-canonical-data vs lem-sfb-relative-ample-absolute-twist: the existing statement twists a relatively ample module by a sufficiently large power of an ample module on the base to obtain absolute ampleness; the new statement neither takes such a base module nor concludes a twisting bound.
- lem-trf-affine-base-ample-canonical-data vs lem-trf-graded-immersion-ample-criterion: the existing statement takes an everywhere-defined graded Proj immersion and concludes relative ampleness; the new statement constructs or glues canonical open-immersion data instead.
- lem-trf-affine-base-ample-canonical-data vs lem-trf-scheme-ample-canonical-proj-criterion: the criterion starts from relative ampleness on EVERY affine base open (or its equivalent canonical data); the new affine-base statement starts from absolute ampleness on X and must establish the smaller-affine restrictions before invoking that criterion.
- lem-trf-affine-base-ample-canonical-data vs lem-trf-scheme-relative-ample-affine-cover: the existing item concludes ampleness on every affine base open from an ample cover; the new statement supplies a different intermediate canonical-data or scheme/space-comparison interface and does not state that locality conclusion.
- lem-trf-affine-base-ample-canonical-data vs lem-weil-pbc-pullback-ample-invertible: the existing statement preserves ampleness along an affine morphism; the new statement must identify the smaller-affine base pullback, establish relative ampleness, and produce the canonical section algebra, full generation and open Proj map.
- lem-trf-affine-base-ample-canonical-data vs lem-weil-pbc-tensor-power-section-nonvanishing-pullback: the existing statement pulls back one section and identifies its nonvanishing locus; it does not produce a section algebra or canonical Proj open immersion.
- lem-trf-canonical-proj-open-cover-gluing vs def-sfb-relative-section-algebra-canonical-map: the existing node specifies section-algebra and chart-characterization data without an existence assertion; the new statement proves existence and full-generation/open-immersion consequences under its hypotheses.
- lem-trf-canonical-proj-open-cover-gluing vs def-trf-space-line-module-proj-input: the existing node defines scheme-test input and canonical-map conventions; it does not prove canonical section algebras exist or that a resulting map is an open immersion.
- lem-trf-canonical-proj-open-cover-gluing vs lem-pc-chow-relative-ample: the existing statement concerns a given projective-space immersion and proper morphisms in Chow data; the new statement has no such immersion or properness assumption and deals with its own canonical section algebra.
- lem-trf-canonical-proj-open-cover-gluing vs lem-sfb-nodal-log-canonical-reconstruction: the existing statement concerns nodal marked curve families and their log dualizing polarization; the new statement applies to arbitrary qc scheme morphisms without the curve, nodal, proper or Noetherian hypotheses.
- lem-trf-canonical-proj-open-cover-gluing vs lem-trf-graded-immersion-ample-criterion: the existing statement takes an everywhere-defined graded Proj immersion and concludes relative ampleness; the new statement constructs or glues canonical open-immersion data instead.
- lem-trf-canonical-proj-open-cover-gluing vs lem-trf-projective-bundle-quotient-geometry: the existing statement classifies rank-one quotients for a symmetric algebra; our canonical section algebra is not assumed symmetric or generated in degree one.
- lem-trf-canonical-proj-open-cover-gluing vs lem-trf-scheme-ample-canonical-proj-criterion: the existing criterion equates relative ampleness with canonical Proj data on a single morphism; the new statement assumes local canonical data and proves the global section-algebra/evaluation identifications and descent of its full open immersion.
- lem-trf-canonical-proj-open-cover-gluing vs lem-trf-scheme-relative-ample-affine-cover: the existing item concludes ampleness on every affine base open from an ample cover; the new statement supplies a different intermediate canonical-data or scheme/space-comparison interface and does not state that locality conclusion.
- lem-trf-canonical-proj-open-cover-gluing vs lem-trf-space-etale-module-pushforward-restriction: the existing statement compares arbitrary module direct images after etale restriction, not full generation loci or open canonical Proj maps.
- lem-trf-canonical-proj-open-cover-gluing vs lem-trf-space-line-module-proj-map: the existing statement constructs a canonical map on a possibly proper generation open for a GIVEN graded algebra and gives base-change compatibility; it does not construct the canonical section algebra from a qc separated morphism or descend full generation and open immersion.
- lem-trf-canonical-proj-open-cover-gluing vs lem-trf-space-section-algebra-etale-base-change: the existing statement constructs and restricts the section algebra and its evaluation; it has no hypothesis of full local generation or local canonical open immersions and no global generation/open-immersion conclusion.

## Review by Q20

I read Stacks `morphisms.tex`, Tags 01VH/01VI/01VJ (definition of relative ampleness, separatedness, and the proof of (3) implies (5) implies (1)), and Tag 0892(2) for affine pullback of an ample module. These justify the item and the first new statement. I read `spaces-morphisms.tex`, Tags 03KG and 03KM, including the affine scheme tests and etale-local formulations, for the second new statement. For the third I read the section-algebra paragraphs of 01VJ, `constructions.tex` Tag 01O9(3), `spaces-divisors.tex` Tag 0D2Z(3), and `spaces-properties.tex` Tag 03LX. The latter source is a module direct-image comparison, not by itself a canonical-Proj descent theorem; the new gluing statement includes the additional compatibility and local-to-global open-immersion argument.

For assembly Step 1 I opened the statement of `def-weil-finite-type-morphism`: it defines quasi-compactness separately from finite type. Only that quasi-compactness definition is used. Affine opens of $U_i$ remain affine opens of $S$, so the restriction $h_i$ is quasi-compact without any finite-type assumption. The first new statement explicitly assumes an affine target and absolute ampleness, and supplies every local canonical datum used by Steps 2 and 3. Invertibility of $N_i$ follows by restricting trivializing opens, not by a nontrivial unstated comparison theorem.

For assembly Step 2 I opened `lem-weil-pbc-etale-composition-cancellation`; its (1) really says open immersions are etale. The covering condition is exactly joint surjectivity. The second new statement assumes only the original quasi-compactness and local SCHEME separatedness, which Step 1 supplies. Its conclusions explicitly include both space qc/separatedness and scheme separatedness/quasi-separatedness, so there is no silent transfer between the two notions.

For assembly Step 3 I checked the third new statement against the local algebra, evaluation, locus and map output of the first new statement. Quasi-compactness remains the original hypothesis, and separatedness is supplied by Step 2 before constructing the global algebra. I opened `lem-trf-scheme-ample-canonical-proj-criterion`: its condition (2) requires quasi-separatedness, its own canonical section algebra/evaluation, full generation and the canonical open immersion. The third statement supplies exactly these ordinary scheme constructions and their identifications, and Step 2 supplies quasi-separatedness. The reverse implication then means ampleness on every affine base open, literally the unchanged item statement. The quotations in `citations.json` cover the complete new interfaces and the criterion, rather than relying on anything in their proofs.

I also opened every dependency statement of the baseline proof before assigning its argument: the affine-morphism and qcqs permanence lemmas really include arbitrary base change; the affine-pullback ampleness lemma assumes an affine morphism; the closed-immersion base-change lemma controls all diagonal tests; the Zariski/etale equivalence identifies both pullbacks and direct images; the section-algebra base-change lemma identifies evaluation as well as the graded algebra; the canonical-map lemma compares both generation loci and the maps; and etale-cover base change plus etale-local open immersion gives the final descent. The new nodes state these tasks instead of relying on a definition node for a missing theorem. They have no proof steps and no proof dependencies.

Small cases checked: the empty source makes every generation-locus equality and open-immersion assertion vacuous, and a covering of the empty base may be empty. A one-member covering makes the new gluing statement a canonical identity comparison. The scheme/space comparison does not assert all separated morphisms are etale and does not assume target separatedness. No intersection of affine opens is assumed affine; every smaller affine open is used only as a genuine scheme chart, and the gluing is over the supplied covering. No finite generation of the section algebra, degree-one generation or equality $\mathcal A_0=\mathcal O_S$ is imposed. In particular $h=\mathrm{id}_S$, $N=\mathcal O_S$ is compatible with the canonical relative Proj model, while an ample sheaf is never declared ample merely because it is locally trivial.

Against delivery-errors B–E: the three statements are self-contained and use defining nodes for their notions; their sources name Stacks tags and labels; the searches are actual logged runs with two semantic phrasings; the source-tag overlaps are distinguished above; no new statement restates the locality conclusion or absorbs the whole proof; and every non-elementary assembly step cites the statement carrying its argument. There are no proof steps over 2000 characters, and the total assembly is below 3000. The repair preserves all seven old arguments instead of shortening away a comparison.

## What remains unfinished

Exactly the three new statement-only nodes remain to be split by other workers. There is no Lean writing or compilation in this delivery. The original item is split by assembly; its theorem is not claimed proved. Required server validation and delivery results are recorded below.

## Validation

The server `review_split` check returned PASS. The first `deliver.py --no-push` completed successfully with `OK (not pushed)` at cd90ee83a58, including the server preflight, DAG and split checks. A subsequent exact tag-table check detected the baseline source typo: Schemes `lemma-closed-immersion-quasi-compact` is Tag 01K7, whereas 01K6 labels composition of quasi-compact morphisms. The new comparison node and assembly source now use 01K7. The verbatim historical argument above is preserved as historical text, including its old source label. A final dry run is required after this source correction; delivery uses the identical reviewed files.
