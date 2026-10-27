# Stage-1 report: lem-sfb-finite-flat-group-hom-scheme

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-flat-group-hom-scheme.json: item, split in six steps; statement and statement dependencies preserved.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-fp-relative-hom-scheme.json: new statement-only prerequisite, unsplit; ordinary relative Hom representability with finite presentation, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-base-change.json: new Mathlib leaf; conjunction of finite, flat, and locally finite presentation base-change instances.
- citations.json: verbatim statement excerpts for every citation of every item proof step.
- searches.jsonl: actual msearch.py records; query text and returned records are retained in each node's mathlib_searches.

## Attachments

None. Searched the read-only project's WeilConjectures source for the exact item id, HomScheme, homScheme, WeilRestriction, weilRestriction, and representability/group-homomorphism combinations, including the GroupScheme directory. The hits concern ordinary arrows, Lie theory or representations; no declaration gives all clauses of this item. The existing finite-free ordinary Hom declaration is sorried and lacks finite presentation; it is not an attachment for this item or the new ordinary Hom node.

## Wanted literature

WANTED: Brian Conrad, Reductive group schemes, Lemma 2.1.3, printed pp.58-59, and Exercise 2.4.5, printed p.77, for lem-sfb-finite-flat-group-hom-scheme and lem-sfb-affine-fp-relative-hom-scheme; local destination literature/conrad-reductive-group-schemes.pdf. Read the primary-source PDF at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf online. Did not download or write into literature. The item proof is marked agent-written because its assembly and equalizer calculation are supplied here and this source is not locally present.

## Findings and scope

The original item has no proof. Its statement is correct and is unchanged. Conrad first represents ordinary scheme morphisms and then asks the reader to impose the group operations by fibre products. I wrote out those fibre products, their natural point description, their finite equations over affine base opens, and why preserving multiplication and identity also preserves inverse. This is not an application of the item to a newly renamed clause: the ordinary Hom lemma has no group structures or group laws; all equations defining the group-homomorphism subfunctor are proved in the item.

Read the three blueprint levels in SETUP, GOAL, the recorded chapter/unit, and the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The inherited from.node is null, and blueprint_refs.py ancestor confirms None; I retained the precise historical from.place and entire via chain, rather than inventing an imported ancestor. The latest direct-images proof (3) remains the route above this supporting moduli argument. The item is not the unit's key node, so no unit record was edited.

Generic tool use: lem-weil-pbc-scheme-morphism-gluing is used only for equality and gluing of scheme morphisms over arbitrary open covers. It is declared in split_report.tool_uses; no other unit's proof is substituted. The composition, Yoneda and affine-permanence statements used here are existing Mathlib leaves.

## Not duplicates

lem-sfb-affine-fp-relative-hom-scheme vs lem-sfb-affine-finite-free-hom: the existing theorem assumes an affine base and a chosen finite free source algebra and asserts affineness only, without finite presentation; the new theorem is global over an arbitrary scheme and asserts finite presentation and finitely presented coordinate algebras on every affine base open.
lem-sfb-affine-fp-relative-hom-scheme vs lem-sfb-affine-weil-restriction-charts: the existing theorem represents maps over S prime on an affine base chart and asserts affineness only; it gives no finite presentation conclusion. The new ordinary Hom theorem asserts finite presentation globally and on every affine base open.
lem-sfb-affine-fp-relative-hom-scheme vs lem-sfb-finite-free-algebra-map-coordinates: the existing statement is an explicit algebra-map coordinate bijection for a chosen finite free basis and arbitrary generating/relating sets; it neither asserts a global scheme over arbitrary S nor finite presentation of that scheme. Its statement does not permit citing the finite-presentation fact from its proof.
lem-sfb-affine-fp-relative-hom-scheme vs lem-sfb-induced-unit-torus-characters: the existing theorem concerns the units torus of a finite separable field extension and its character lattice; it is not a relative Hom theorem over an arbitrary base.
lem-sfb-affine-fp-relative-hom-scheme vs lem-sfb-finite-locally-free-relative-hom-space: the existing theorem represents ordinary Hom by an algebraic space, without affineness or finite presentation; neither conclusion required here is in its statement.
lem-sfb-affine-fp-relative-hom-scheme vs lem-sfb-finite-locally-free-weil-restriction: algebraic-space representability alone gives neither affineness nor finite presentation, which are the new theorem's needed conclusions.
lem-sfb-affine-fp-relative-hom-scheme vs lem-sfb-weil-restriction-geometric-properties: that node supplies separatedness, local finite type, smoothness and, over a locally Noetherian base, quasi-compactness; it supplies no finite-presentation assertion over arbitrary bases.
lem-sfb-finite-locally-free-base-change vs lem-a1-finite-locally-free-polynomial-basis-charts: the existing theorem concerns only polynomial base change with fixed degree and chosen local bases; the new Mathlib leaf handles every base change and varying rank.
lem-sfb-finite-locally-free-base-change vs lem-sfb-finite-locally-free-fppf-descent: that node concerns the fixed-degree groupoid and its descent; its pullback assertion assumes constant degree. The new leaf imposes no degree hypothesis and is used before any rank decomposition.
lem-sfb-finite-locally-free-base-change vs lem-trf-finite-locally-free-composition: composition and base change are different operations; both are needed for D times D over S.

The whole-DAG title/statement/source searches and blueprint_refs.py searches for Hom scheme, Weil restriction, finite locally free, equalizer, 0BL3 and 02KD found no node already giving the new assertions. Mathlib semantic searches were tried with a second phrasing; general local representability requires an atlas as input, affine-space theorems do not represent Hom, and finite-presentation algebra constructors do not give this global Hom theorem. All records are actual calls, with returned hits read. The base-change leaf is an allowed clausewise Mathlib match, with all three declaration names, paths and lines read in its how field.

## Review by Q97

I read delivery-errors B through E in full, and checked the written statements and each cited statement against those rules. For the item I read Conrad Lemma 2.1.3 and Exercise 2.4.5 online. For the ordinary Hom prerequisite I read the local Stacks more-morphisms.tex proofs of Tags 05Y6 (lemma-hom-from-finite-free-into-affine) and 0BL3 (lemma-hom-from-finite-locally-free-into-affine), together with Conrad's first assertion. Those proofs construct coefficient equations after choosing a basis locally, and glue. A finite presentation of the target gives finitely many variables and coefficient relations; this works over non-Noetherian bases and does not require a basis containing 1. The prerequisite's statement is self-contained and includes the affine-chart conclusion actually used in step 4; it contains no proof sketch. I checked that none of the existing Hom/Weil-restriction statements already has this finiteness conclusion.

For the base-change leaf I read morphisms.tex Tag 02KD (lemma-base-change-finite-locally-free), and the source of Mathlib's AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme (Morphisms/Finite.lean:60), AlgebraicGeometry.Flat.isStableUnderBaseChange (Morphisms/Flat.lean:81), and AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange (Morphisms/FinitePresentation.lean:85). The project's definition is exactly their conjunction; taking each clause is a one-line specialization, with no hidden equivalence to a module-based definition. I tested this on the identity, an empty source, a non-surjective base map, and a family with differing ranks on disconnected components.

Step 1 uses the new base-change leaf for the projection D times D to D and the existing composition node for its map to S; the latter's statement says precisely that composites of finite locally free maps are finite locally free. The new ordinary Hom theorem then applies separately to D, D times D, and S. In every application the target is the given affine finitely presented G. No theorem about flat maps alone is used.

Step 2 uses only the fibre-product universal property for the product map and compatibility with base change, and the exact fully faithful Yoneda statement for morphisms between representables. I read that node's bijection and its inverse at the identity; it supplies the arrows a,b,c,d used here. This is not the more general Yoneda evaluation statement for arbitrary presheaves that the cited node might fail to provide.

Step 3 is an elementary expansion of the cited fibre-product definition: a point of B consists of a point of H and a forced common point of M. It imposes exactly multiplication and identity. It does not claim that an arbitrary closed subscheme of a finitely presented scheme is finitely presented.

Step 4 uses the explicit chart clause in the new ordinary Hom statement, the affine spectrum correspondence in def-weil-affine-spectrum, and the existing morphism-gluing theorem. I checked its statement really glues morphisms on any open cover with equality on the full intersections. The proof covers overlaps by affine opens rather than asserting the overlaps affine. The finite list of differences of generators cuts out exactly the two equalities; agreeing on generators implies agreement on every polynomial and therefore the entire algebra. The two pointwise constructions are mutually inverse and commute with algebra maps, so they glue. Lifting finitely many additional relations to the polynomial presentation of P gives a finite presentation of P/J. This is one routine calculation, not a hidden comparison theorem or a restatement of the parent; it is below 2000 characters, as are all other steps.

Step 5 uses the definition of an affine morphism and the affine-local definition of local finite presentation. Clause (3) of lem-weil-pbc-affine-morphism-permanence explicitly supplies quasi-compactness and quasi-separatedness of the resulting affine map. I checked those are relative properties, so S itself need not be quasi-compact or quasi-separated.

Step 6 checks the inverse law on every test scheme, not merely geometric points, and uses faithful Yoneda to identify morphisms. The inverse equation is the elementary group calculation u(x)u(x inverse)=1. The converse is exactly the definition already in the item. The naturality of the final bijection follows from the fibre-product restriction in step 3.

Small cases: empty base gives the empty representing S-scheme; D=S as the trivial group gives B=S; trivial G also gives B=S; a nonreduced finite group such as alpha_p in characteristic p is not excluded, and no geometric-point test or smoothness step is used. For the new ordinary Hom theorem, empty X gives H=S, X=S gives H=Y, and Y empty gives the clopen zero-rank locus; varying rank and zero rings cause no omitted positive-rank hypothesis. No statement was disputed or weakened. Sources were cited without invoking any prohibited SGA route. The elementary equalizer universal-property step and inverse calculation stayed in the proof instead of becoming artificial nodes.

I copied a verbatim statement quote for every cited node into citations.json and checked the equality of proof_deps with the union of uses. New nodes have complete statements, named notions, no proofs, searched blueprint references, and actual logged searches. The imported fields, source, statement and statement dependencies of the item are retained. No repository, launcher, Lean file or unit file was changed; no compiler, Lake or local DAG checker was invoked.

## Unfinished work

No part of this one-level split remains unfinished. The ordinary Hom prerequisite is intentionally statement-only and joins the stage-1 queue; the base-change prerequisite is a Mathlib leaf. Required server dry run and push follow this report.

## Dry-run repair

The first server preflight required an explicit mathlib_match.line field in addition to the three verified paths and lines already recorded in how. Added line 60 for the primary Finite.lean declaration; the Flat.lean:81 and FinitePresentation.lean:85 references remain in how. No mathematical change.
