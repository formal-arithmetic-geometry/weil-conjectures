## Worker report

Files written in this sandbox only:

- `dag/nodes/sec-six-functors-basics/lem-sfb-isolated-curve-formal-lifting.json`: item split into eight steps; its mathematical statement and the earlier Q21 search results are retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-isolated-curve-two-affine-cover.json`: statement, unsplit, no Mathlib match; the geometric cover used in 0DZP.
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-isolated-deformation-lift.json`: statement, unsplit, no Mathlib match; the affine, one-extension lifting input of 0DZF, including its reduction square.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-open-deformation-lift.json`: statement, unsplit, no Mathlib match; the one-extension lifting input of 0DZN across a smooth affine open.
- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-nilpotent-base-change-reflection.json`: statement, unsplit, no Mathlib match; 09ZW(7), with no flatness assumption.
- `citations.json`: one verbatim statement quotation for every node cited in every numbered proof step. Search outputs, search-plan.json, search-results.json and the small sandbox scripts preserve the research and construction.

Attachments: none. Searching the live `lean/WeilConjectures/` for the item's blueprint tag, isolated curve terminology, affine/local deformation terminology, and proper nilpotent reflection found no finished declaration giving this item or one of the four new inputs. Deformation-to-the-normal-cone modules concern a different construction.

WANTED: none.

The original node was an unsplit statement, with no proof. Its statement is faithful to the formal-system step used in Stacks 0E7Y. No statement dispute or correction was needed. The split makes the local isomorphisms and their compatibility part of the inductive choices, and proves properness and finite presentation at each finite level. It makes no assertion that a local ring of an algebraization is the supplied local deformation; the warning in 0E7Y explicitly rules out that stronger assertion.

The item has no recorded Lean audit or declaration, so there was no sorry-free attachment to use. I added the existing topological dimension definition to its statement dependencies, to specify the dimension convention including the empty scheme. No chapter, unit, target, source or launcher file was written. No Lean was written or compiled, and no git command was run by this worker.

All requested stage-1 work on this item is prepared. The four new statement-only inputs deliberately remain unsplit for subsequent items; this is the required single-level split.

## Sources and searches

For the item I read `examples-defos.tex`, Tag 0DZP (`lemma-curve-isolated`, including its proof), Tag 0E7Y (`lemma-smoothing-proper-curve-isolated-lci`, the formal-system paragraph and its local-ring warning), and `formal-defos.tex`, Tag 06HN (`lemma-smooth-morphism-essentially-surjective`, the compatible induction). I also read the definition of a smooth morphism of deformation categories in `formal-defos.tex`: it requires the triangle with the specified lower deformation to commute. This is why merely choosing separate lifts at each n is insufficient.

For the new cover node I read 0DZP's first proof paragraph and the existing `lem-sc-dim-one-ample-invertible`, `lem-sc-dim-one-quasi-projective` and `lem-sc-ample-finite-set-affine` statements. A single affine neighbourhood is not the required two-affine covering: 0DZP first includes all component generic points in V, making its complement finite, and then chooses an affine in the smooth complement of the marked points. Separatedness gives the affine intersection. All three affines are finite type over k. This geometry is the smaller, independent input being left for later splitting.

For the affine lifting node I read 0DZF (`lemma-isolated`), its first arrow and proof, Example `example-rings`, 0DYX (`lemma-affine`) and the scheme deformation Example `example-schemes`. The node asserts just the first smooth lifting arrow, expressed using actual flat schemes and local algebras; it does not assert the henselization/completion arrows or tangent-space statements. Its bases are explicitly finite-dimensional local augmented k-algebras, a specialization of the Artinian bases in the source. Its affine scheme can have any dimension: this is not the proper-curve tower restated as a child.

For the smooth-open node I read Situation `situation-glueing` and 0DZN (`lemma-glueing-smooth`) with its proof. The second arrow applies because the first open is smooth, hence in particular a local complete intersection, and the intersection is smooth affine. The node asserts a single lift across an arbitrary surjection of the specified Artinian bases and the actual commutative reduction equation. It assumes no isolated singularities or dimension bound and no properness; the item must still obtain and lift the other affine piece.

For the properness node I read `more-morphisms.tex`, 09ZW (`lemma-thicken-property-morphisms-cartesian`), especially hypothesis X = S times_{S'} X', the finite-order base hypothesis, part (7), and its proof using (2) and the morphism-thickening properties. I checked that it does not assume the lifted morphism is finite type or flat. No separate existence or lifting conclusion is hidden in this node.

Before creating these nodes I searched the whole current DAG for 0DZP, 0DZF, 0DZN, 0DYX and 09ZW, as well as two-affine covers, affine isolated deformation lifting, smooth overlaps, deformation categories and nilpotent properness reflection. The whole imported blueprint was searched with `tools/blueprint_refs.py search` for deformation, isolated, isolated singularities, two affine, smooth overlap, thickening proper, and the relevant tags. No blueprint node states one of these four results. `blueprint_refs.py ancestor` returns None for this item's existing created-item chain; I retained that null ancestor and extended the existing via list with this item, rather than inventing an ancestor. All from.place fields explain which part of the inherited alteration/smoothing route they serve.

Each new node has two separately phrased LeanFinder searches, Loogle, grep and LeanSearch, all run through msearch.py and recorded with the exact queries, outputs, dates and verdicts. Further scoped greps and a namespaced properness Loogle query were also recorded. All services returned results, so none was described as unavailable. The hits give arbitrary affine covers, algebra-homomorphism formal smoothness, existing scheme glue data, and stability of properness under base change. None supplies respectively the finite-point two-affine cover, deformation of the algebra itself, compatible extension of the smooth open, or reflection of properness. Thus there are four new unsplit statements and zero new Mathlib leaves. The older searches on the existing item were preserved verbatim.

## Not duplicates

lem-sfb-isolated-curve-two-affine-cover vs lem-sfb-isolated-curve-formal-lifting: although both cite 0DZP, the new node only constructs two affine opens on a separated finite-type curve; it has no Artinian bases, deformations, local algebras or tower.

lem-sfb-isolated-curve-two-affine-cover vs lem-sfb-isolated-lci-curve-smoothing: the existing node produces a projective smoothing over k[[t]] under a complete-intersection hypothesis; the new node only supplies affine covering geometry and does not require that hypothesis.

lem-sfb-proper-nilpotent-base-change-reflection vs lem-weil-pbc-finite-type-lift-nilpotent: the existing node is the ring finite-generation argument for 09ZW(2); the new node is the properness equivalence of 09ZW(7), including universal closedness and separatedness.

lem-sfb-proper-nilpotent-base-change-reflection vs lem-weil-pbc-thickening-lft-cartesian: the existing statement is exactly local finite type, 09ZW(2); it does not assert properness.

lem-sfb-proper-nilpotent-base-change-reflection vs lem-weil-pbc-thickening-finite-cartesian: the existing statement is finiteness, 09ZW(8); it cannot handle a positive-dimensional proper curve.

lem-sfb-proper-nilpotent-base-change-reflection vs lem-weil-pbc-finite-etale-lifting-complete: 09ZW is mentioned inside that node's proof, but its statement concerns algebraizing a finite etale cover of the special fibre of an already proper scheme; it does not assert properness reflection for an arbitrary morphism.

There is no DAG node carrying 0DZF, 0DZN or 0DYX as the statement of one of the other new inputs. Existing elementary consequences and definitions were reused, not recreated.

## Review by Q74

I reviewed the final statements and steps against the sources above and the B--E return cases, opening the cited node statements rather than using their proof sketches.

Step 1 uses the definition of properness only for separatedness and finite type, both explicit in that definition. The new cover statement supplies U, V, their affine intersection, the marked-point containment/avoidance, their finite type, and the two smoothness conditions. Its hypotheses match the item over an arbitrary field. I did not use an algebraically closed-field curve lemma here.

Step 2 uses `lem-pc-flat-field`, whose statement covers every scheme over a field, to supply the base case. The rest sets up the actual induction data, including the specified n=1 local identifications. The calculation 2n >= n+1 uses n >= 1, so the n=1 extension to the dual numbers is included. Finite-dimensionality, the augmentation, and locality of k[t]/(t^n) follow directly from its basis and the finite geometric-series inverse. There is no unjustified claim that a chosen lift of an element is an idempotent or that a completion is regular.

Step 3 uses `lem-weil-pbc-thickening-affine-scheme`, whose statement requires only an affine closed subscheme and surjectivity on points; it applies to V inside V_n because t is nilpotent and thus lies in every prime. It does not require a Noetherian hypothesis or affineness of X_n. `lem-weil-pbc-affine-open-stalk-localization` explicitly identifies the ambient local ring with the stalk on the affine open, including its germs. The prescribed reduction of C_{i,n+1} is composed with h_{i,n}^{-1}, not with an unrelated special-fibre isomorphism. This is also where the hypotheses on every supplied local algebra are checked.

Step 4 uses exactly the new affine lifting statement. V is finite type by the cover node, the special-fibre singular set is contained in the marked points, V_n is affine by step 3 and flat as an open of the inductive flat scheme (flatness is pointwise on the local rings). The finite-dimensional local augmented bases were checked in step 2. The output is a flat affine lift Z with the specified reduction and the compatible local isomorphisms. This step does not assume an arbitrary singular curve is unobstructed: the local deformations are input data.

Step 5 uses exactly the new smooth-open extension statement and its equation e composed with gamma_A = theta restricted to V_n. Its two smooth affines are those supplied in step 1. The affine-open stalk node supplies the local identifications for the final isomorphisms. The equation with e together with the affine lifting node's delta/beta equation gives the displayed equality of reduced local maps. I checked both reduction arrows use t^n at the n+1 to n step. This supplies compatible isomorphisms, not just compatible isomorphism classes.

Step 6 uses only the new properness statement. I explicitly checked its cartesian hypothesis against the special-fibre square and its finite-order hypothesis against (t)^n = 0. This can be applied after constructing X_n without presupposing finite type. It applies equally in dimension zero and to nonreduced curves.

Step 7 uses the actual locally Noetherian definition: the one affine chart of Spec R_n has Noetherian coordinate ring, because each ideal has a finite k-basis. `pqf-lem-lft-fp-locnoeth` then supplies precisely local finite presentation, not any unmentioned stronger conclusion. The properness definition gives quasi-compactness and separatedness, and `lem-pc-separated-quasi-separated` explicitly supplies quasi-separatedness. The finite-presentation definition combines these three conditions. This checks the n=1 level as well, rather than assuming it was already finitely presented.

Step 8 is the elementary recursion/composition argument; it invokes no new geometric input. Longer transition isomorphisms are defined by composing adjacent ones, so their associativity and the iterated local compatibility follow from the displayed adjacent equations. No inverse limit or existence of an algebraization is used. The empty marked list uses the r=0 affine lifting input and therefore does not force a fictitious singular point. For the empty scheme one may take the empty tower. For the cover node I also checked a zero-dimensional component lying in the marked set: it can lie wholly in V and need not meet U. For properness reflection I checked the zero ideal, a zero ring base, and the distinction between a nilpotent closed immersion and an arbitrary closed immersion. For the two lifting nodes I checked the identity base extension, the dual-number extension, empty opens and no local factors.

All new statements introduce their own objects; locality of the Artinian bases and of D_i is written inline, and tensor products, smoothness, flatness, finite type, essential finite type, properness and dimension cite their actual definition nodes. Their proof and proof_deps fields are empty. No new node is a clause of the tower theorem: cover geometry, arbitrary-dimensional affine lifting, two-open extension and general properness reflection are distinct smaller inputs. The complete argument joining them remains in the item. During review I made finite type of all three affine opens explicit in the cover node so step 4 does not silently import an uncited finite-type restriction theorem.

The only off-route non-leaf generic tool declared in split_report.tool_uses is the existing affineness-of-thickenings lemma, exactly the tool used in 0DYX's proof. The other reused statement nodes are Mathlib leaves. Every non-elementary step is below 2000 characters (the longest is 1013), and each cited statement is copied verbatim into citations.json for checking. There is no citation of a downstream smoothing theorem, so no circular dependency on the item is introduced.
