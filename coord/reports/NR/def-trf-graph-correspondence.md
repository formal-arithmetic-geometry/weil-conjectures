# def-trf-graph-correspondence — stage 1, NR

## Files written

- `dag/nodes/sec-six-functors/def-trf-graph-correspondence.json`: definition, split by naming existing prerequisites; no Mathlib match for the complete construction.
- `citations.json`: empty list, since this definition has no proof steps.
- `report.md`: this self-review. The search command maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No chapter or unit record changed: this recorded-in-advance definition is not its preservation unit's key statement.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact id, blueprint tag, graph correspondence, `ofGraph`, and `upperShriekIdIso`. I read `AlgebraicGeometry.ProEtale.Correspondence.ofGraph` at `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Correspondence.lean:460`, its support-map lemma at line 486, and `Correspondence.fix` at line 164. These provide the intended graph data and an equalizer, but `ofGraph` uses the additional `GeometricOperations A s` package and its `ctf` predicate. I also read the module's structure declaration and the explanation in `TraceFormula/Frobenius.lean:93`: the identity exceptional comparison relies on a package field, rather than deriving that field from the trivial compactification. Thus this is not an exact attachment under this item's hypotheses. `WeilComplex.graph` at `Frobenius.lean:279` is further specialized to Frobenius iterates. No master declaration containing sorry was treated as a finished proof.

## WANTED

None. All source material needed for this definition is present.

## Corrections

STATEMENT-DISPUTED: literally writing `u=v` equates morphisms with different targets: `v` ends in `K`, whereas the correspondence coefficient ends in `R(id_X)^!K`. This is a type check, not a counterexample to the intended construction. I faithfully expanded the suppressed identity identification to `u=iota_{X,K} composed with v`. The source Lean `ofGraph` uses precisely this composite. The support, orientation, endomorphism, coefficients and hypotheses are unchanged.

The earlier sandbox attempt attributed a pro-etale identity-adjoint isomorphism directly to `lem-asd-etale-compact-support-normalization`. On opening that statement, its adjunction normalization is on the ordinary etale derived categories. It does not itself state the pro-etale comparison used here. I removed that attribution and dependency. Instead the definition specifies iota by the constructible adjunction of `def-trf-admissibility` and the trivial compactification in `def-compact-support-direct-image-detailed`. The elementary identity-adjunction calculation is written below. No normalization claim is being inferred from a definition of an unrelated object.

I retained all import flags, blueprint history and maintainer-owned metadata. The split report now describes the actual revised dependencies. `blueprint.same_as=[]`: the whole-DAG and blueprint searches for graph correspondence and identity adjunction found no distinct node stating the complete definition.

## Mathlib searches

I reran LeanFinder, LeanSearch, Loogle and grep through the required `msearch.py` command, with two semantic phrasings, and recorded the actual queries and returned names in the item. The first Loogle query using project-qualified names returned an unknown-identifier diagnostic; it is explicitly recorded as an invalid query with no absence conclusion. The replacement quoted `upperShriek` query succeeded with zero hits. Both grep searches succeeded with zero hits. All semantic hits were read: affine-space morphisms, simple graphs, scheme sheaf/module maps, and generic derived-category Hom/Ext constructions do not define this finite-coefficient exceptional graph correspondence or specialize to it in one line. No service outage was recorded as absence. There are no new-node search records to invent or backfill.

## Not duplicates

No new nodes. The existing graph-independent fibre-product, correspondence, fixed-scheme, coefficient, pullback, exceptional-adjoint and compact-support nodes suffice. The blueprint searches included the complete imported blueprint, not just this unit.

## Review by NR

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three-level rules in `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, the worker role and delivery-errors B–E. The source I checked for the item is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-trf-graph-correspondence.md`, especially the displayed four data and its final equalizer clause. The master definition is identical apart from its recorded-in-advance note; the item's `blueprint_update` agrees. I read the chapter and unit records and preserved their route. There are no new nodes requiring additional literature or Stacks tags.

For this definition, there are no numbered proof steps: `proof=[]`, `proof_deps=[]`, and hence `citations.json=[]`. I checked each construction prerequisite against the opened node's statement, as follows.

The statements of `def-weil-finite-field-fiber` and `def-trf-coefficient-conventions` give k, s, A, the geometric fibre X of a separated finite-type model, and the category D^b_ctf(X,A). `def-weil-scheme-morphism-properties` gives the meanings of separated and finite type. I have not generalized X beyond the coefficient conventions or assumed properness. The derived pullback statement in `def-weil-derived-pullback-tensor-hom` defines Lh* at this finite coefficient level on the ambient category, so v is allowed without an additional preservation claim about its source.

The statement of `def-trf-correspondence` requires a separated finite-type support C, the product morphism c, and a coefficient from Lc2*K to Rc1!K. Taking C=X meets the support requirement. Because h is a k-map, id_X and h have equal composites to s. The universal property in `def-pc-fibre-product` therefore defines c=(id_X,h), with exactly these projections. No graph closed-immersion theorem is needed to supply these data.

I opened `def-weil-exceptional-inverse-image` and checked its finite-level construction: it transports the ordinary etale right adjoint and defines the constructible exceptional inverse image, without an arbitrary ambient pro-etale adjoint. `def-trf-admissibility` explicitly specifies its adjunction on D^b_ctf and says that this datum is available for every separated finite-type morphism here. Thus it applies to id_X without adding an exceptional-admissibility hypothesis to the item.

The formula in `def-compact-support-direct-image-detailed` is Rp_* j_!. For the trivial compactification (id_X,id_X), extension by zero has on every test object the original sheaf, because every test object factors uniquely through id_X; its presheaf is already a sheaf. Direct image along id_X is likewise identity on sections. Applying the identity to a resolution identifies its derived functor with the original object via the resolution quasi-isomorphism. Hence this compactification gives the canonical alpha:F=R(id_X)_! to id. This is an elementary evaluation of that formula; it uses no etale/pro-etale equivalence and no claim about a general compactification on arbitrary objects.

Explicitly, with G=R(id_X)^!, unit eta and counit epsilon of F adjoint to G, the iota defined in the node is G(alpha_K) eta_K. Transporting this adjunction along alpha gives id adjoint to G. In these transported coordinates the triangle identities give epsilon_M eta_M=id_M and G(epsilon_M) eta_{GM}=id_{GM}. Naturality of eta at epsilon_M gives eta_M epsilon_M=G(epsilon_M) eta_{GM}=id_{GM}. Thus its unit is the canonical isomorphism K to GK, with inverse the transported counit. This two-line formal calculation is why no separate identity-adjoint lemma is created. It also verifies that iota composed with v has exactly the required target.

Finally, `def-trf-fixed-scheme` states both the diagonal fibre product and the graph-endomorphism convention Fix(h), including the scheme-theoretic equalizer universal property. Substitution gives exactly the displayed fixed scheme. As a further check, a test-scheme map into the fibre product is a pair a,b:T to X with (a,h a)=(b,b); the first projection forces b=a and the second forces h a=a. Conversely such a gives the unique pair (a,a). This checks the claim for all schemes T, including nonreduced ones, rather than only rational points.

I tested h=id_X (Fix(h)=X with all nilpotents), empty X, K=0, v=0, and translation h(t)=t+1 on the affine line (empty fixed scheme). None requires h proper, v invertible, a finite fixed set, smoothness or reducedness. The exceptional leg is id and the ordinary leg is h throughout. The B–E audit found no new statement-only-node, duplicate, Mathlib-leaf, cycle or proof-step citation obligation. The only source repair is the typed identity comparison; the earlier mistaken citation has been replaced rather than supported by an assertion hidden in a cited proof.

## Unfinished work

The first worker left independent second reading and delivery to the next reader; those actions are recorded below.

## Second reading by NR

- Item statement: checked against the current `main-20261015` blueprint node `def-trf-graph-correspondence` and the imported master node; the hypotheses on the finite-field datum, coefficient stage, separated finite-type $k$-scheme, endomorphism, derived pullback map, graph legs, coefficient map, and scheme-theoretic fixed equalizer agree. The explicit target $R(\operatorname{id}_X)^!K$ is the necessary typing of the source's suppressed identity identification.
- Proof steps: none (`proof=[]` and `proof_deps=[]`), so there are no uncited steps or elementary-step classifications to repair.
- New nodes: none; B1--B7, duplicate-node checks, and Mathlib-leaf checks therefore introduce no additional obligations. The recorded Mathlib searches were rerun and their actual results remain in the node and `searches.jsonl`.
- Dependency walk: `def-trf-correspondence` supplies the correspondence type and exceptional/ordinary leg orientation; `def-trf-admissibility` supplies the constructible adjunction; `def-compact-support-direct-image-detailed` supplies the trivial compactification comparison; `def-weil-derived-pullback-tensor-hom` supplies $Lh^*$; `def-pc-fibre-product` supplies $(\operatorname{id}_X,h)$; and `def-trf-fixed-scheme` supplies the diagonal pullback and equalizer interpretation. Every cited statement says the fact used.
- Edge cases: checked $h=\operatorname{id}_X$, empty $X$, $K=0$, $v=0$, $n=1$, a field, and translation on $\mathbb A^1$; the fixed scheme and coefficient typing remain valid, with no hidden properness, smoothness, reducedness, or nonempty-fixed-point hypothesis.
- Changes made: none to the node or citations; this section records the independent second reading. The prior source-typing correction and removal of the mistaken ordinary-etale normalization attribution remain as documented above.
