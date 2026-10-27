## Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-normal-subgroup-central-neutral-test.json` (statement, now split, no Mathlib match), and `citations.json` (14 step/node entries with verbatim statements). No new nodes and no Mathlib leaves. `searches.jsonl` is the search command's log; `milne.txt` is a local reading aid extracted from the existing literature PDF.
2. Attachments: none. Searches of the live `lean/WeilConjectures/` found no declaration with this blueprint tag or the full criterion. The related `AlgebraicGeometry.GeneralLinearGroup.central_subgroupSchemeHom_le_center`, `GroupScheme/GeneralLinear/ClosedSubgroup.lean:709`, assumes a radical defining ideal and concerns the already defined reduced centre. It does not assert this arbitrary-normal-subgroup criterion or normality of its unreduced open neutral component.
3. WANTED: Brian Conrad, *Reductive Group Schemes*, local copy of `https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf`, Theorem 3.3.4 proof, printed p.100, and Proposition 3.3.8 proof, printed p.102. Read those passages online. WANTED: Conrad--Gabber--Prasad, *Pseudo-reductive Groups*, Lemma 5.3.2 (the reference Conrad gives for the central-neutral-component argument); not read and not used as a black-box dependency.
4. The item was statement-only. Its mathematical statement is retained. I normalized the doubled TeX escape before `hookrightarrow`; there is no change of hypotheses or conclusion. The proof is explicitly marked agent-written. Rather than cite the desired criterion under another name, it supplies its commutator argument from existing component and reductive-structure statements. The inherited null `blueprint.from.node` is retained: the ancestor command reports None. The current latest sketch was read; neither its statement nor its route was changed.
5. Unfinished work: none for this one-level stage-1 split. The existing cited unsplit statements remain their own queue items; this delivery creates none.

## Sources and searches

I read Stacks `groupoids.tex`, Tag 0B7R (`proposition-connected-component`), including its connected-product factorization argument; `varieties.tex`, Tag 038F (`lemma-bijection-irreducible-components`); and `algebra.tex`, Tag 05CK (`lemma-faithfully-flat-universally-injective`). I read Milne, `literature/milne-algebraic-groups_iAG2017.pdf`, Proposition 1.34 and Corollary 1.35, printed pp.16--18, Proposition 12.46 and its proof, pp.245--246, Corollary 17.62 and its proof, pp.372--373, and Proposition 21.60 and its proof, p.442. These provide the existing inputs to the explicit argument. Conrad's p.100 passage invokes perfectness of the adjoint quotient, and p.102 explicitly preserves normality of the neutral component; the written proof realizes this group-theoretic principle using the central radical times derived subgroup, as given by the existing Milne-route nodes. No SGA source was used.

All five searches already recorded on the live item were actually rerun under Q04 with the required msearch.py command, with exactly those tool/query strings. The log records successful leanfinder (both phrasings), loogle, grep and leansearch calls. The hits are abstract-subgroup normality/centres, upper central series, and characteristic-zero Lie algebra facts. Their displayed hypotheses and types do not state a theorem about arbitrary, potentially nonreduced subgroup schemes in a reductive group. The grep has zero hits. There is consequently no Mathlib leaf or attachment. No unrun search has been added.

I searched the whole DAG for the same criterion, component translations, central torus/derived multiplication, perfect groups, and commutator arguments, read the matching statements, and reused the existing nodes. The blueprint searches `central`, `normal subgroup`, `component` and `semisimple`, and the latest blueprint text search, produced no imported node stating this criterion. The algebraic-component coset node is about algebraic matrix groups and does not state the full nonreduced criterion; it was not substituted for the stronger existing scheme-translation result.

## Not duplicates

No new nodes. Every input was already present, so no new/existing pair requires separation.

## Review by Q04

This is my own check of the split, not an independent second reading. I checked the sources above and opened the statement of every cited node. The important point is that a topological image is used only to factor through an OPEN subscheme; no step infers factorization through a general closed subscheme from its underlying set.

Step 1 uses the affine quotient characterization in `def-weil-closed-immersion` to write the closed subgroup as Spec(A/I); the finite affine cover definition in `def-weil-finite-type-morphism` makes this finite type. `lem-sfb-locally-algebraic-group-identity-component` states clopenness, the open subgroup structure and geometric irreducibility, with no smoothness assumption on N. Applying it also to connected G identifies G with G^0. The composition of closed immersions is written out using surjective ring maps. Thus the later irreducibility argument really applies to unreduced C as well.

Step 2 uses normality exactly as defined in `def-sc-group-scheme-subgroup`, giving conjugation into N. Both G and C are geometrically irreducible by Step 1, which are precisely the hypotheses of `lem-sc-irreducible-product-over-field`; its conclusion gives irreducibility of their product. The conjugation image is connected and contains the identity. `lem-weil-pbc-morphism-factors-through-open-subscheme` applies because C is open, and gives an actual scheme morphism into C. Applying conjugation by g and g inverse proves normality on every algebra. This establishes the item's normality clause rather than creating a node restating it.

Step 3 uses the same normal-subgroup definition and open-factorization statement for b_n. Connectedness of G and b_n(e)=e put its image in C. I checked the displayed commutator identity directly: b_n(xy)=x b_n(y) x inverse b_n(x); the centrality assumption allows the conjugation to be removed and the two factors to be reordered. The group-homomorphism definition in `def-sc-group-scheme` then applies. This proves a morphism identity over arbitrary algebras; rational points are used solely to choose a constant representative n, not to detect equality of functions on N.

Step 4 takes exactly the central torus and semisimple quotient clauses from `lem-sfb-reductive-radical-quotient`. G is smooth, connected, affine, finite type over the algebraically closed field, so the hypotheses of `lem-sfb-central-torus-semisimple-derived-product` hold with this R. That statement supplies the faithfully flat multiplication and defines D by its minimal closed-subgroup property for the commutator morphism. `lem-sc-kernel-subgroup` supplies a CLOSED kernel for b_n, which is a homomorphism by Step 3. Since its target C is commutative, the kernel contains the image of the commutator and hence D. The radical is central, so b_n kills it directly. This proves b_n composed with multiplication is the identity constant; neither kernel smoothness nor centrality of an arbitrary finite normal subgroup is assumed.

Step 5 applies `lem-weil-pbc-faithfully-flat-ideal-contraction` with I=0: its statement explicitly gives injectivity. The multiplication morphism of Step 4 has faithfully flat coordinate map in the stated sense; all its source/target schemes and C are affine. The two coordinate maps from k[C] therefore agree before composing with m*. This detects b_n=e as a morphism, including nilpotent functions, and yields centrality of n after every extension. This is the reason no reduced-source density argument appears.

Step 6 uses precisely the translation-isomorphism clause of `lem-sfb-group-neutral-component-translates`, whose statement explicitly allows nonreduced N. Its finite clopen components cover N as open schemes and each has a rational representative. On each translated component both factors of n_j c commute with g, so the commutator identity holds as a scheme morphism. Equality of morphisms is local on the source open cover; this handles an arbitrary algebra point that meets multiple components. The reverse implication is restriction to the subgroup C. No additional non-elementary lemma is hidden here.

I checked that each cited node exists, is unmerged, and has no dependency path back to this item. The generic off-unit geometric-product, closed-kernel and faithfully-flat-injectivity inputs are declared in split_report.tool_uses with their reasons; the open-factorization node is already Mathlib. The union of uses is exactly proof_deps, and citations.json includes a verbatim statement for every occurrence. No proof step exceeds 2000 characters (the longest is 859), and every argument remains in the item.

Small cases checked: G a torus has R=G and D=1, so Step 4 immediately kills b_n. G semisimple has R=1 and D=G, giving the same conclusion. N=1 and N=G give the expected tautologies. In characteristic p, N=mu_(pm) in G_m with m>1 prime to p is disconnected and nonreduced, with N^0=mu_p; the translation and coordinate arguments preserve these nilpotents. A connected Frobenius kernel has N=N^0 and does not become central by an unstated smoothness assumption. The connectedness assumption cannot be dropped (a finite nonabelian constant G has trivial neutral component); reductivity also matters (in the characteristic-p Heisenberg group, the normal subgroup with first coordinate in F_p, second coordinate zero, and arbitrary central coordinate has central neutral component but is not central). Thus the proof does not assert the false general connected-group variant.

## Delivery-errors B--E audit

| Point | Check |
|---|---|
| B1 | No new nodes; no proof was hidden in a statement-only child. |
| B2 | The item introduces k,G,N and the full unreduced N^0. |
| B3 | Existing notion dependencies retained; auxiliary notions come from the cited statements. |
| B4 | Corrected the doubled hookrightarrow escape; proof TeX is escaped once. |
| B5 | Stacks references use 0B7R, 038F and 05CK with actual source labels read. |
| B6 | No Mathlib leaf asserted without a declaration/file/line. |
| B7 | Centrality and reductivity are spelled out, not defined by tags. |
| B8 | All search hits were read as abstract group or Lie algebra facts, not scheme matches. |
| B9 | Blueprint ancestor/search checked; inherited provenance retained, same_as searched, split_report explains the below-unit place. |
| B10 | Project tag and notion searches found no exact finished declaration. |
| C1 | All non-elementary inputs have cited existing nodes; the remaining group and ring identities are written out. |
| C2 | Only final open-cover assembly is marked elementary; structural inputs are explicit. |
| C3 | No object is taken from another node's proof. |
| C4 | Every cited statement was opened; all 14 citation occurrences have verbatim text. |
| C5 | Whole-DAG and whole-blueprint searches preceded the decision to reuse existing inputs. |
| C6 | Dependency-path checks found no cycle through this item. |
| C7 | The unit's route is unchanged; these are prerequisites below its existing group-theoretic branch. |
| C8 | Off-unit tools are declared only in split_report.tool_uses, for maintainer review. |
| D1 | Both clauses are proved in the item's steps. |
| D2 | No new node receives the item's content. |
| D3 | The proof cites actual component, product, kernel, reductive-structure and flat-injectivity theorems. |
| D4 | The order is components/normality, commutator, vanishing, then assembly; no circular use. |
| D5 | The commutator calculation and descent from multiplication are explicit. |
| E1 | Every finiteness, affineness, geometric irreducibility and faithful-flatness hypothesis was checked above. |
| E2 | No new statement; nonreduced, torus and semisimple cases tested. |
| E3 | Only open-target factorization is inferred from image containment. |
| E4 | C is the open neutral component itself, never its reduction. |
| E5 | Explicit commutator and injective-coordinate-map calculations replace an unspecified transport. |
| E6 | Normal and central both mean the functorial group-scheme conditions on every algebra. |
| E7 | No mathematical source error identified; only TeX normalization was needed. |
