# Q19 stage-1 delivery: lem-trf-ordered-nodal-branch-overlap

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ordered-nodal-branch-overlap.json`: item, split into eleven proof steps; statement unchanged. Mathlib: no match after two semantic phrasings, LeanSearch, Loogle and source grep; inherited searches retained.
- `dag/nodes/sec-trace-formula/lem-trf-normal-topologically-noetherian-components.json`: one new statement-only supporting lemma, unsplit, Mathlib: no match. This is the normal-component decomposition with a topologically Noetherian, rather than locally Noetherian, hypothesis.
- `citations.json`: one exact statement quotation per node use in every numbered step.
- `report.md`: this report.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag and for ordered branches, branch overlaps, vertical ideals and coordinate notation. No declaration states this item. The upstream master source is reference material only; no sorry declaration is counted as finished.

## WANTED

None for the proof delivered here. I read local Stacks sources. The historical Temkin archival-PDF warning remains in the inherited ancestry; this delivery neither uses that PDF as a proof nor attributes this relative branch-comparison assertion to Temkin.

## Problems in the inherited material

The item was an unsplit agent reconstruction, with no proof. Stacks 0CBY is an existence theorem for etale neighbourhoods and supplies neither branch ordering on overlaps nor a Zariski chart on X itself. I read `curves.tex`, `lemma-etale-local-structure-nodal-family` and its proofs. The supplied etale chart is already a hypothesis of this item. The proof here is explicitly agent-written: it uses normal branch families over all primes of the finite valuation spectrum, rather than pretending that 0CBY asserts the conclusion.

The current main-20261015 ancestor `lem-trf-local-term-locality` and its unit proof now use contracting correspondences. The item's historical semistable ancestry is retained, as inherited; I have not altered the unit, chapter, or maintainer-owned bindings. Within the historical strict-chart parent, this item supplies exactly its Step 3 overlap comparisons. No conclusion about effective descent or a Zariski nodal chart has been inserted into this item.

No statement dispute or statement change was needed. The proof actually does not need separable closedness after the given chart and the smooth-component hypothesis are available; those hypotheses have been retained.

## Unfinished work

No part of this item's argument is left unproved at this split level. The new general normal-component lemma is statement-only, as required, and its independent proof remains a later item. Its source is Stacks Tag 0357, with the topological finiteness input 0052; the report below explains its use without putting a hidden proof into that new node.

## Blueprint and duplicate searches

I read the chapter `sec-trace-formula`, the unit `sk-i-curve-zero`, the current main-20261015 ancestor statement and proof, the item, and the strict-chart parent. `tools/blueprint_refs.py ancestor` gives `lem-trf-local-term-locality`. Blueprint searches for ordered nodal branch overlap, 0357, normal irreducible, normal components, irreducible components normal, and topologically Noetherian normal found no equivalent blueprint node. The normal-components search did find `lem-fin-etale-normal-components`, which requires a Noetherian source; it cannot be applied to these valuation-base branch schemes. Whole-DAG searches by the tag, normal-component wording and Lean-source terminology were also read.

The new node's `blueprint.from` names this precise auxiliary branch-family component-isolation argument and extends the historical via chain by the item. Neither the item nor the new node claims to be a new statement in the present ancestor blueprint.

## Not duplicates

lem-trf-normal-topologically-noetherian-components vs rem-pc-regular-normal: its decomposition clause assumes the scheme is locally Noetherian and quasi-compact; the new lemma assumes only the underlying topology is Noetherian. Valuation rings here need not be Noetherian.
lem-trf-normal-topologically-noetherian-components vs lem-fin-etale-normal-components: that node assumes an algebraically Noetherian etale source over a normal integral target; the new lemma applies directly to any normal scheme with Noetherian topology and has no etale-map or algebraic Noetherian hypothesis.
lem-trf-normal-topologically-noetherian-components vs lem-sbc-normal-sections-finite-product: that node concerns sections on a quasi-compact open in a locally Noetherian normal scheme; it cannot give a decomposition when the section rings are not Noetherian.
lem-trf-normal-topologically-noetherian-components vs lem-sbc-normalization-dense-open: that node identifies a relative normalization under a locally Noetherian hypothesis; it does not decompose a topologically Noetherian normal scheme.
lem-trf-normal-topologically-noetherian-components vs lem-sbc-normal-dense-open-integral-section: that node extends integral sections from a dense open of a locally Noetherian normal scheme; no such extension assertion is in the new lemma.
lem-trf-normal-topologically-noetherian-components vs lem-sbc-relative-normalization-normal-stalks: that node establishes normality of a relative normalization of a locally Noetherian source; the new lemma assumes normality and decomposes the original scheme.
lem-trf-normal-topologically-noetherian-components vs new-finite-normal-dense-etale-stalk-going-down: that node gives going down for a finite morphism with dense etale open and locally Noetherian target, not component decomposition.
lem-trf-normal-topologically-noetherian-components vs new-stalk-normalization-boundary-dimension-two-transfer: that node transfers local dimension along a particular finite normalization, not decomposition under topological Noetherianity.
lem-trf-normal-topologically-noetherian-components vs lem-trf-valuation-normalized-graph-model: that node constructs an intermediate normalized valuation-curve graph model; it does not state the generic normal-component decomposition.
lem-trf-normal-topologically-noetherian-components vs lem-trf-dnc-generic-local-system-devissage: that node constructs a finite-cover exact sequence of coefficient sheaves; component decomposition is not its conclusion.
lem-trf-normal-topologically-noetherian-components vs lem-trf-graph-frobenius-open-exchange: that node compares coefficient functors for Frobenius and an open immersion, not normal-scheme topology.
lem-trf-normal-topologically-noetherian-components vs lem-trf-quasi-finite-composition: that node proves composition of quasi-finite ring maps, not normal-component decomposition.
lem-trf-normal-topologically-noetherian-components vs lem-pc-fp-chart-map-zero-eventually: that node detects vanishing of a module map at a finite affine approximation stage, not components of a normal scheme.
lem-trf-normal-topologically-noetherian-components vs lem-dl-a1-constant-field-charts: that node constructs pointed affine charts and an adic open-image comparison over finite fields; the new lemma is about arbitrary normal schemes.
lem-trf-normal-topologically-noetherian-components vs lem-weil-pbc-etale-injective-colimit-acyclic: that node concerns acyclicity of colimits of injective etale sheaves, not scheme decomposition.
lem-trf-normal-topologically-noetherian-components vs lem-weil-pbc-geometrically-reduced-extension-separable: that node concerns separability of geometrically reduced field extensions, not normal-scheme components.
lem-trf-normal-topologically-noetherian-components vs lem-weil-pbc-etale-directed-cohomology-colimit: that node concerns etale cohomology and directed colimits, not normal-scheme components.
lem-trf-normal-topologically-noetherian-components vs lem-pur-constant-two-term-resolution: that node constructs a constant coefficient resolution, not components of a normal scheme.

lem-trf-normal-topologically-noetherian-components vs lem-sc-affine-noetherian-underlying-space: that node passes from an algebraically Noetherian affine ring to Noetherian topology; the new lemma starts with Noetherian topology and normality, and decomposes the scheme.
lem-trf-normal-topologically-noetherian-components vs lem-sc-components-open-injection: that node identifies components under intersection with an open subset; it does not prove normal components disjoint or open.
lem-trf-normal-topologically-noetherian-components vs lem-sc-locnoeth-components-locally-finite: that node assumes local algebraic Noetherianity and proves local finiteness, not the disjoint decomposition in the non-Noetherian case needed here.
lem-trf-normal-topologically-noetherian-components vs lem-sc-noetherian-finite-irreducible-components: that node proves only finiteness in a topological space, without normality, openness, disjointness or integral open subschemes; it is cited where only finiteness is needed.
lem-trf-normal-topologically-noetherian-components vs lem-weil-pbc-noetherian-open-subscheme-noetherian: that node preserves algebraic Noetherianity on open subschemes, not normal-component decomposition under a purely topological hypothesis.
lem-trf-normal-topologically-noetherian-components vs lem-sfb-noetherian-component-open: that node produces some nonempty open inside each component; the new lemma makes every entire component open, disjoint and integral by normality.
lem-trf-normal-topologically-noetherian-components vs lem-sfb-noetherian-connected-components-open: that node concerns connected components, which can contain intersecting irreducible components; the new conclusion concerns irreducible components and their integral scheme structures.
lem-trf-normal-topologically-noetherian-components vs lem-sbc-constant-local-dimension-components: that node deduces component dimensions in a locally Noetherian scheme, not normal decomposition with Noetherian topology alone.
lem-trf-normal-topologically-noetherian-components vs lem-weil-pbc-irreducible-refinement-topological: that node constructs an irreducible refinement of a finite stratification of a Noetherian scheme, not a disjoint decomposition into the original scheme's open integral components.

The last several pairs involving the digits 0357 are incidental occurrences of the digits 0357 elsewhere in the full JSON, rather than matching mathematical sources; they are listed to make the complete grep audit explicit.

## Review by Q19

I checked the item against the actual statement of Stacks 0CBY and against the parent's use of it. The chart is supplied in the hypotheses, so the argument begins after the etale local-model theorem, and it ends with both stated ideal equalities at every fibre-component generic point. I made no appeal to an uncited branch-ordering theorem. I read the new node's sources in `properties.tex`, Tag 0357 (`lemma-normal-locally-finite-nr-irreducibles`), and `topology.tex`, Tag 0052 (`lemma-Noetherian`). The former requires finite components on quasi-compact opens; the latter supplies this on every subspace of a Noetherian underlying space. Thus no algebraic Noetherian hypothesis has been smuggled into the new lemma.

For Step 1 I checked the actual etale base-change, open-immersion/composition, and qcqs-finite-presentation statements. Their hypotheses hold for the affine chart maps. A finite chain of primes makes the generizations of the image of y an actual affine open, so making that image the closed base point is legitimate even if it was not initially closed.

For Step 2 I checked the valuation-normality, polynomial-normality and etale-over-normal-ring statements. The quotient by a prime is a domain and satisfies the valuation alternative by the explicit two-residue fraction argument in the step. The branch schemes are genuine closed subschemes etale over the two polynomial lines; I also checked the localization-normal-domain node: it makes each polynomial normal domain a normal ring in the local sense needed by etale normality. Etale normality therefore applies to the branch coordinate rings. This does not assume X itself normal.

For Step 3 the finite-type-over-Noetherian node is applied only to fibres over fields. The topology on the whole branch family is then Noetherian because a closed-set chain stabilizes on each of finitely many fibres. The new node says exactly that the normal branch family's components are disjoint and clopen integral schemes. Therefore removing all but the component containing y removes a closed subset avoiding y, simultaneously for all base primes. This is the essential shrinking argument. The new node is a general normal-scheme fact, neither a clause of this item's overlap conclusion nor a copy of its hypotheses.

For Step 4 the cited etale base-change statement gives N etale over Spec R/(c); the flat-lfp-open node gives an open image. R/(c) is local, so that image is the whole base because it contains the closed point. This proves existence of a point z_t on both branches for every relevant fibre; no finite-etale section or chosen lift over an unproved residue-field identification is used.

For Step 5 I checked the flat ring definition, the affine flatness comparison and the generic-fibre localization statement. The integral branch coordinate ring H is nonzero and flat over the domain R/t. The explicit multiplication-injectivity argument verifies the injective base-map hypothesis of the localization lemma. It then gives an integral generic fibre over t. Thus the fibre branches are single components, not just locally chosen branches at y. This distinction is what makes comparison on all overlaps possible.

For Step 6 the open-image statement gives points off the origin on each branch, so the branches are distinct. Etale reducedness applies to the reduced standard fibre, whose reduction is checked by the displayed polynomial injection. The nonsmoothness of the origin is proved from the smooth lifting definition using the explicit square-zero extension k[epsilon]/epsilon^3 -> k[epsilon]/epsilon^2. It is valid in every characteristic. The etale-source-smoothness node states the needed pointwise reflection, not just global smoothness descent.

For Step 7 I wrote out the topological generic-point argument using the finite components of the field fibres and the open-map statement. The existing topological node lem-sc-noetherian-finite-irreducible-components supplies finiteness; I added that explicit citation during review. Step 8 then uses exactly the assumed smoothness of reduced irreducible components of X_t. If both branches mapped to one component, its ideal would pull back to zero on each integral branch; the flat-tensor-exact node applied to the explicit standard-model injection gives injectivity into the two branch quotients. Hence the factorization through that smooth component is scheme-theoretic. Etale base change and the cited smooth affine comparison/composition nodes make Y_t smooth, contradicting the actual node on it. This checks both the C1 issue (tensor exactness is cited as a theorem, not merely flatness defined) and the C4 issue (the cited statements give these precise operations).

For Step 9 the final principal-open inverse image is affine and surjects onto its chosen target open. Restriction preserves all preceding properties. In Step 10 the projections of the overlap are etale by the cited base-change statement, hence open. The written argument of Step 7 applies again to their component generic points. Opposite branch labels would have different generic images in X_t, contradicting p r1 = p r2. Step 11 is the explicit local calculation: the unit coordinate has ideal (1) and its partner has ideal (c). Both coordinate equalities follow, including fibres where c is invertible and empty fibres outside the base restriction.

I tested the argument on the standard chart uv=c, on c a unit on a generization, on a non-Noetherian valuation ring with a finite prime chain, and on a disconnected etale chart. Disconnected branch components are removed as closed sets, rather than assumed absent. Removing the smooth-component hypothesis would allow a self-node of one irreducible component: the two labels could then have the same generic image, so Step 8 correctly identifies where that hypothesis is needed. The field-base case has no point with u=v=0 when c is nonzero, and is vacuous as it should be. The empty-scheme case for the new lemma is explicitly allowed. All eleven steps are shorter than 2000 characters. I reread them for hidden comparisons and extracted precisely the normal-component theorem that is non-elementary.

For every step I opened the cited node statement and checked its actual hypotheses and conclusion; the exact text is recorded in `citations.json`. Generic off-unit algebraic tools are declared in `split_report.tool_uses` for the maintainer's judgment; I did not edit maintainer-owned `tool_uses`. All new Mathlib search entries correspond to commands actually run and outputs read in `searches.jsonl`; no unavailable service is recorded as a mathematical failure to match. No Lean source was written and no compiler or build was run.
