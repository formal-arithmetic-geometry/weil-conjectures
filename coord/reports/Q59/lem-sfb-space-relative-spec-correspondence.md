## Worker report

Q59, stage 1, 2026-10-23. Item: lem-sfb-space-relative-spec-correspondence.

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-spec-correspondence.json: split, unchanged statement, eight proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-integral-finite-etale-locality.json: new statement-only node, unsplit; no Mathlib match.
- citations.json: a verbatim statement quotation for every step/node citation.

Attachments: none. The blueprint tag and notion searches in lean/WeilConjectures found no declaration of the item. AffineMorphismRelativeSpec.lean and RelativeGluing/BaseChange.lean concern schemes; they do not establish the assertion for an arbitrary algebraic-space base. No Lean was written and no compiler was run.

WANTED: none. All sources used are present in literature/stacks-project/.

The initial item had no proof. It correctly distinguished finite presentation of an algebra from finite presentation of its underlying module. That distinction and all hypotheses are retained. The source's two omitted verifications (the relation and arbitrary base change) have been written out, as has full faithfulness on morphisms. No imported statement error or statement dispute was found. There is no unfinished work in the item's assembly proof; the new general locality theorem remains a statement-only input for a subsequent worker.

## Sources and route

I read spaces-morphisms.tex, Tag 081V (lemma-affine-equivalence-algebras), its complete proof, and Tag 081W (definition-relative-spec and following base-change sentence). For the property clauses I read Tag 03WG (lemma-affine-local), Tag 03ZQ (lemma-integral-local), and Tag 0410 (lemma-finite-presentation-local). I also read the scheme equivalence, morphisms.tex Tag 01SA (lemma-affine-equivalence-algebras), and Tag 01TQ (lemma-locally-finite-presentation-characterize). The quotient/chart argument was checked against spaces.tex Tag 02WW (theorem-presentation) and groupoids.tex lemma-criterion-fibre-product. For quasi-coherent descent I read spaces-properties.tex Tag 03M3 (proposition-quasi-coherent).

The single new node is precisely Tag 03ZQ, equivalence (1)/(3), for the integral and finite alternatives separately. Its conclusion is representability with the scheme property on every scheme base change; it is not a claim about pointwise integrality or about an arbitrary nonrepresentable morphism.

The chapter record and sk-thm-sf-ctf-stability unit were read, together with the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This item is the relative-Spec foundation used by the parent's Tag 09YA approximation, along the already recorded direct-image alteration route. It replaces no unit argument. blueprint_refs.py ancestor returns None for this created-node chain; the inherited null ancestor and detailed from.place were retained. The new node prepends this item to the inherited via chain and states the exact supporting sentence it serves.

## Searches

Before creating the node I searched all dag/nodes for 03ZQ and lemma-integral-local and for affine-space, integral, finite, locality and relative-Spec notions, then read the candidate statements. I ran blueprint_refs.py searches for equivalence-algebras, relative spec, relative spectrum, integral local, integral morphism, finite presentation affine, criterion-fibre-product, and affine algebraic spaces. No blueprint result states the new algebraic-space locality theorem. Scheme finite locality and scheme integral affine-cover locality already exist, and are cited rather than recreated. The existing space-affine-locality, space-local-properties-chart-test and space-qcoh-groupoid-equivalence nodes also supply their respective inputs.

All new Mathlib queries were run through batch2/msearch.py; searches.jsonl contains the actual responses. The item has LeanFinder, Loogle, grep and LeanSearch queries; the different LeanSearch wording was also read. They returned scheme Spec/global-sections equivalences and scheme affine base-change properties. Those are not an algebraic-space theorem. The new node has the same four search kinds and a second LeanFinder wording. The first wording returned IsIntegralHom/IsFinite and their scheme properties; the second returned Scheme.Etale and its pullback infrastructure. The displayed signatures quantify over Scheme. Grep of AlgebraicGeometry for AlgebraicSpace or algebraic.space had no hits; a broader grep's measure-theory and IsIntegralHom namespace hits were irrelevant. No Mathlib leaf was claimed. Existing item search records from its creation were preserved; only actual new query records were added.

## Not duplicates

lem-sfb-space-integral-finite-etale-locality vs lem-sfb-finite-space-morphism-topology: that node assumes a scheme-test finite morphism and proves closedness and fibre/topology assertions; it does not descend finiteness or integrality from an etale chart.

lem-sfb-space-integral-finite-etale-locality vs lem-sfb-space-relative-spec-correspondence: the item constructs an anti-equivalence, charts, and arbitrary base change, then translates three algebra properties; the new node is a general descent criterion for any space morphism and has no algebra sheaf or relative-Spec assertion.

lem-sfb-space-integral-finite-etale-locality vs lem-sfb-integral-affine-cover-criterion: that node is for schemes and an affine Zariski open covering; it gives neither algebraic-space representability nor descent along an etale atlas.

lem-sfb-space-integral-finite-etale-locality vs lem-weil-pbc-finite-local-on-target: that node gives Zariski locality of finiteness for schemes, not integral/finite representability for algebraic spaces.

lem-sfb-space-integral-finite-etale-locality vs lem-sfb-parameter-root-integral-nil-fibre: that node concerns a specific integral ring construction and its nilpotent special fibre, not etale descent of space morphisms.

lem-sfb-space-integral-finite-etale-locality vs lem-weil-pbc-spec-integral-ring-map-integral: that node converts an integral ring homomorphism into an integral affine scheme morphism; it does not descend a space morphism from an atlas.

## Review by Q59

I checked the item against the complete Tag 081V proof and the new node against Tag 03ZQ(1)/(3), with the node files open. The latter needs no finite type, Noetherian, separation or quasi-compactness assumptions on the spaces or on the atlas: the adjective integral or finite is a property of the morphism. Its quantifier is every scheme test, not only affine etale points. The source's (1) implies the test on every atlas, and its (3) implies (1), which is exactly the stated iff for each fixed atlas.

Step 1 uses affine-etale-cover for an actual scheme atlas that is a disjoint union of affine schemes. Etale-atlas-presentation supplies the scheme kernel relation and quotient presentation. Space-qcoh-groupoid-equivalence supplies the ordinary scheme module and its cocycle and the etale/Zariski identification; its coherence clause is not used. Etale-module-pushforward-restriction explicitly identifies etale tensor pullback with restriction, which justifies retaining multiplication and the unit in that descent datum. I did not assume a quasi-compact atlas or affine overlaps.

Step 2 uses the full scheme relative-Spec anti-equivalence, including functoriality on algebra maps, and the scheme base-change isomorphism to construct the two cartesian squares. Fibre-products-etale-covers now explicitly supplies etale stability. The source's omitted relation check is not hidden in a new node: uniqueness of the underlying R arrow proves monicity; the identity, symmetry and cocycle of the descent algebra give identity, inverse and composition of its spectrum. These checks hold on arbitrary test schemes and prove an equivalence relation, not just a groupoid with possible stabilizers.

Step 3 invokes the etale-relation-quotient statement for algebraicity, the etale surjection, kernel pair, and quotient universal property. The input monomorphism and equivalence relation were proved in step 2. I checked chart recovery against the cartesian-relation argument of groupoids.tex and wrote its local lifting and injectivity argument in the step, using the atlas kernel relation from etale-atlas-presentation. It does not cite that general lemma merely by tag or assume the desired fibre square. Space-affine-locality then gives affineness and representability of q from this scheme atlas.

Step 4 uses the explicit section-preserving etale restriction comparison, scheme relative Spec's quasi-coherence/counit, and the full faithfulness of space-qcoh-groupoid-equivalence. The definition of quasi-coherence is the local-presentation predicate, so quasi-coherence on the atlas gives it on X. The algebra equations are checked after restriction; no tensor-compatible equivalence was assumed without justification. On any affine etale T, representability and the restricted direct-image identification allow the scheme equivalence to give precisely Spec(A(T)); this is not an unjustified independence-of-atlas assertion.

Step 5 uses the scheme theorem on both V and R, then the quotient universal property and the groupoid-module equivalence on compatible maps. The unit and product equations hold locally and therefore globally as equations of sheaf maps. The proof explicitly gives both directions on morphisms and recovers every affine space by its local counits; it does not obtain the whole item by applying a new node containing its conclusion.

Step 6 uses the arbitrary-space tensor-pullback quasi-coherence node without a flatness assumption. The source of the comparison is the canonical tensor pullback, and etale-module-pushforward-restriction explicitly identifies its two localized paths. I checked that T=U' times_X U is a scheme: U' is a scheme and U to X is representable etale. It covers U' by fibre-products-etale-covers. The scheme base-change theorem then applies to the actual scheme morphism T to U, even when X' to X is not etale. The comparison agrees on overlaps because the same algebra map induces it, and inverse maps glue too. Thus the argument proves an isomorphism and its naturality, not just an equality of point sets.

Step 7 uses the defining affine-ring characterizations from finite-integral-morphism and the new general space locality node. In review I replaced a direct finite-product argument by the already existing scheme nodes integral-affine-cover-criterion and finite-local-on-target. Their statements give exactly the passage from the affine components of U to the scheme morphism over U. These tests involve integral elements or finite modules respectively, with no assumption that finite implies finitely presented over a non-Noetherian ring.

Step 8 uses scheme affine-morphism-permanence clause (3) on every scheme base change, so q and its relative diagonal are quasi-compact in the scheme-test sense. This repaired an initially implicit assertion that separatedness alone supplied the needed quasi-separatedness. Space-local-properties-chart-test supplies local finite presentation on the atlas and on arbitrary etale scheme charts; its statement has no Noetherian assumption. Lfp-affine-opens-finite-presentation applies to the entire affine source and affine target, giving a finite polynomial presentation. In the reverse direction the definition of local finite presentation applies using those entire affine charts as neighbourhoods. Hence the property here is finite presentation as an algebra, never as a module.

Small-case checks: the zero algebra gives the empty relative spectrum, the structure algebra gives X, and the empty base/atlas makes all tests vacuous as it should. Polynomial algebras illustrate finite presentation without module finiteness; an infinite integral algebra illustrates integrality without finiteness. A finite non-finitely-presented quotient over a noncoherent base must not be asserted finitely presented; the proof does not do that. A non-quasi-separated base is allowed because it is the affine morphism's relative diagonal that is tested. The new locality theorem also applies to an empty source and to a scheme base, where it reduces to the known etale-local scheme property. No step exceeds 2000 characters, and no non-elementary subclaim is left merely as a source tag. citations.json quotes the actual cited statements, including all 30 uses after repair. The off-unit citations are generic atlas, quotient, module-restriction and scheme-relative-Spec tools; split_report.tool_uses explains them. There is no SGA source and no route change.

The preliminary server review_split passed. The required full delivery dry run and push are performed after this report is written; their output is the delivery evidence.
