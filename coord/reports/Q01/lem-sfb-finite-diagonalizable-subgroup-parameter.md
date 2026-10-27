# Stage-1 report: lem-sfb-finite-diagonalizable-subgroup-parameter

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-diagonalizable-subgroup-parameter.json`: item split; its statement and statement dependencies are unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-flat-group-hom-scheme.json`: statement-only input, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-closed-embedding-locus.json`: statement-only input, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-quasi-affine-reflection.json`: statement-only input, unsplit, no Mathlib match.
- `citations.json`: verbatim statements for all 29 step/node citations.
- `searches.jsonl` and `work/`: actual search records, printed results and sandbox preparation scripts; not DAG deliveries.

## Attachments

None. Searched the item id, finite diagonalizable subgroup terminology, Hom-scheme/closed-immersion-locus names and norm/quasi-affine combinations in the read-only `lean/WeilConjectures/`. Read the existing relative quasi-affine module. No declaration states the item or any new input. Mathlib hits give affine/quasi-affine properties, local finite presentation, abstract groups and generic representability; none constructs this Hom scheme, represents this embedding locus or reflects quasi-affineness along a finite flat cover. In particular `Scheme.IsQuasiAffine.of_isAffineHom` proves quasi-affineness of the source from the target, the reverse of the needed implication.

## Literature wanted

WANTED: Brian Conrad, *Reductive Group Schemes*, local copy `literature/conrad-reductive-group-schemes.pdf`, Lemma 2.1.3, printed pp.58-59, and Lemma 2.3.4, printed pp.69-70, for the item and the Hom/embedding-locus inputs. Read the primary-source PDF online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf. No download or repository write was performed.

## What needed correction

No statement dispute and no change of the item's statement. The imported prerequisite had no proof. Conrad starts the argument after a Noetherian reduction, whereas the item allows arbitrary rings. I made that issue explicit by stating a general quasi-compact closed-embedding-locus input, rather than asserting that every open in the Hom scheme is quasi-compact. I use the existing Stacks quotient theorem and the Stacks norm argument, not the source's group-specific quotient reference. No SGA theorem is invoked.

The automorphism group is written as Aut(M)^op: character duality reverses composition. Freeness is checked on all scheme tests, not just geometric points. The functor classifies abstract forms embedded in G, so the proof uses embeddings modulo precomposition, not a conjugacy orbit or G/N_G(H).

## Unfinished work

No part of this one-level split is unfinished. The three new nodes remain statement-only as required and join the ordinary stage-1 queue. Their proofs have deliberately not been installed as splits.

## Searches and blueprint

The sandbox was empty apart from dispatcher markers. I searched the complete DAG by titles, statements and the relevant source tags, and used `tools/blueprint_refs.py ancestor` on the item and `search` for diagonalizable, Hom-scheme, closed immersion locus, free action, finite locally free, quotient and 0BD1. I also searched the current `literature/blueprint/latest/blueprint/`. No imported blueprint statement is the same as the item or a new input. The ancestor command reports None; each new node retains that null ancestor and extends the item's inherited place and via chain. No chapter/unit route was changed. I read GOAL.md, the chapter, the unit and the three blueprint levels in SETUP.md.

All new nodes have actual msearch executions in all three search families (LeanSearch, LeanFinder/Loogle and Mathlib grep), and a second semantic phrasing. The full service outputs are retained under `work/`; `mathlib_searches` contains the exact logged tool and query text, result digest and verdict. All services responded. The earlier item searches were retained and additional real searches appended. General scheme and descent lemmas from other units are declared only in `split_report.tool_uses`.

## Not duplicates

lem-sfb-finite-flat-group-hom-scheme vs lem-sfb-affine-weil-restriction-charts: the existing node represents unrestricted scheme morphisms into an affine chart, with no finite-presentation conclusion; the new node represents group homomorphisms with all group equations and finite presentation.

lem-sfb-finite-flat-group-hom-scheme vs lem-sfb-finite-free-algebra-map-coordinates: the existing node gives algebra coordinates for maps over a specified finite-free algebra, not the global group Hom functor or its group-operation equations.

lem-sfb-finite-locally-free-closed-embedding-locus vs lem-sfb-finite-locally-free-source-factorization-locus: the existing node represents factorization through a specified closed subscheme by a closed parameter locus; the new node represents surjectivity of the varying coordinate map by a quasi-compact open parameter locus.

lem-sfb-finite-locally-free-quasi-affine-reflection vs lem-a1-affine-groupoid-basechange-polynomial-norm: the existing node gives a polynomial norm and invariant-base specialization identity for affine groupoids, not descent of quasi-affineness for schemes.

lem-sfb-finite-locally-free-quasi-affine-reflection vs lem-a1-affine-groupoid-norm-prime-separation: the existing node separates two field-valued groupoid orbits by an invariant norm, not quasi-affineness of a target of a finite locally free cover.

lem-sfb-finite-locally-free-quasi-affine-reflection vs lem-a1-affine-groupoid-invariant-norm: invariance of a norm under an affine groupoid is different from quasi-affine reflection.

lem-sfb-finite-locally-free-quasi-affine-reflection vs lem-sfb-finite-locally-free-ample-reflection: the existing node reflects ampleness of a given invertible module. It does not state the needed equivalence between quasi-affineness and ampleness of the structure sheaf. The new input directly records the geometric quasi-affine conclusion of 0BD1, with 0BD2 furnishing its norm; no unstated ample/quasi-affine comparison is used by the item.

lem-sfb-finite-locally-free-quasi-affine-reflection vs lem-sfb-finite-locally-free-pullback-section-norm: the existing node supplies a norm section of a tensor power of a line bundle and its nonvanishing set, not quasi-affine reflection.

lem-sfb-finite-locally-free-quasi-affine-reflection vs lem-sfb-finite-locally-free-function-norm: the existing node constructs the function norm with multiplication, scalar power and vanishing properties, not quasi-affine reflection.

lem-sfb-finite-locally-free-quasi-affine-reflection vs lem-sfb-finite-field-picard-norm-base-change: that node concerns Picard norms for a finite field extension, with no quasi-affineness conclusion.

lem-sfb-finite-locally-free-quasi-affine-reflection vs lem-pur-finite-flat-kummer-norm-degree: that node concerns the norm/Kummer transfer square and curve degrees, with no quasi-affineness conclusion.

## Review by Q01

I read Conrad's actual statements and proofs of Lemmas 2.1.3 and 2.3.4 online, rather than assuming that the parameter functor was a homogeneous quotient. For the new Hom node, Lemma 2.1.3 explicitly includes group homomorphisms, finite flat finitely presented source and affine finitely presented target. This matches finite locally free sources. Its coordinate construction gives finite presentation over arbitrary rings, not just finite type over a Noetherian ring. Smoothness of G is not required by this input.

For the new embedding-locus node, I read the kernel/Nakayama argument in Lemma 2.3.4, p.70, and separately checked the arbitrary-ring and quasi-compact strengthening rather than silently copying its Noetherian argument. On a finite-free chart of rank r>0, choose algebra generators x_1,...,x_n of the affine target. The images of monomials of total degree at most r-1 span the whole fibre algebra exactly where that algebra map is surjective: in an r-dimensional vector space the increasing spans of monomials either stabilize or strictly grow, starting at dimension one. Surjectivity is therefore the union of the maximal-minor principal opens for one finite matrix into a rank-r module. This union is quasi-compact, and on it that finite module map is surjective, so the algebra map is surjective after every base change. The converse is checked on fibres. Rank zero gives the entire base. Finite locally free charts over an affine base have a finite subcover, so the argument glues with quasi-compactness. This explains the stronger statement's provenance in the report; the node itself contains only the statement.

For the new quasi-affine-reflection node, I read `divisors.tex`, labels `lemma-norm-quasi-affine` and `lemma-finite-locally-free-has-norm`, Tags 0BD1 and 0BD2. The latter gives a positive-degree determinant norm without dividing by d; the former reflects quasi-affineness using it. Applying them over each affine open of S gives exactly the relative statement. I compared every same-tag existing node listed above: none already states that conclusion.

For step 1 I checked that the group algebra basis is finite even in bad characteristic and wrote its finite algebra presentation explicitly; the Hom node's source and target hypotheses are then in force. For step 2 the cited locus node states a universal closed-immersion condition, not merely a pointwise injectivity condition. The cited open-immersion/etale/local-presentation statements apply to all schemes. Quasi-compactness comes from the locus node, while quasi-separatedness comes from an open in an affine scheme.

For step 3 I opened the full statement of relative character duality: its local character-map classification supplies the locally constant automorphisms and works over nonzero rings; the empty affine case is handled separately. The opposite group corrects composition. Cancellation proves freeness on arbitrary tests. For step 4 I opened prime avoidance and the affine-principal-open statement; together they give an affine neighbourhood for every finite orbit. I read the admissible free finite-quotient statement and checked absolute separation, the orbit condition and test-wise freeness before using its finite etale quotient, kernel-pair identity and universal property. No quotient-existence hypothesis was smuggled into a new lemma.

For step 5 I checked constant positive degree from the finite etale torsor and its free geometric orbits, including an empty base. The norm reflection node supplies exactly quasi-affineness; it is not used for finite presentation. I opened `lem-trf-lfp-fppf-source-locality`: it allows a flat lfp surjective source family and no Noetherianity, so q is an admissible single cover. The quotient statement supplies quasi-compactness and separation; the scheme-conventions node then supplies the exact finite-presentation criterion.

For step 6 I opened the finite-flat closed-subscheme descent node and checked equality as embedded subschemes on the double overlap and constant degree |M|. Precomposition changes no embedded image. I also opened fppf-to-fpqc, fpqc-cover base change and representable descent. They justify the actual cover and the local factorization/gluing of multiplication, identity and inverse into the descended subgroup; no definition node is being cited as an effective-descent theorem. For step 7 I checked that local trivializations give the same embedded image, that character duality supplies precisely the transition automorphisms, and that representable descent and uniqueness of embedded descent give both inverse identities. Naturality is explicit pullback, with the needed covers still covering by the cited base-change theorem.

I tested the new statements with the trivial source, rank-zero source where allowed, an empty base, nonreduced coefficient rings and mu_p in characteristic p. In particular the p-torsion diagonalizable source is finite flat, not etale; only its automorphism group and the quotient cover are etale. The actual statement assumes an embedding H into G but the construction needs no extra hypothesis from that embedding. No field, reducedness, smoothness of H, invertibility of an order, normality or Noetherianity was introduced. Every cited node's statement was read in full and copied verbatim into citations.json. All proof steps are below 900 characters and none hides a long inline comparison.

I checked delivery-errors B through E: the new statements introduce their objects and notions, have no proofs or proof dependencies, and are searched; source places identify the exact assertions; no elementary observation, existing character-duality theorem, quotient theorem or descent theorem was reintroduced as a node. The parent carries the construction and the inverse maps, not an application of a renamed copy of itself. Review-split already passed on the server. The required full dry run follows this report.
