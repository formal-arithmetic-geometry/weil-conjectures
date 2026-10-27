# Worker report: lem-sfb-dolbeault-acyclic-resolution

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dolbeault-acyclic-resolution.json: statement unchanged; five-step split, explicit category comparison and edge cases.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-scalar-dolbeault.json: statement; unsplit, no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-function-modules-acyclic.json: statement; unsplit, no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-chart-exterior-derivative-square-zero.json: statement; Mathlib leaf extDeriv_extDeriv_apply, Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean:229; real field and infinite smoothness specialize in one line.
- citations.json: one verbatim statement quotation per step/dependency pair.
- searches.jsonl: unedited output log of the mandated msearch.py calls.

## Attachments

None. Searched lean/WeilConjectures for the item blueprint tag, Dolbeault, d-bar and fine sheaves. No project declaration states the item. The upstream sorry-containing DAG material was not accepted as a proof.

## Wanted literature

WANTED: Demailly, Complex Analytic and Differential Geometry, I §1.A and §3.C/§3.E Lemma (3.29), IV §4 Corollary (4.19) and §6 Example (6.13), for lem-sfb-dolbeault-acyclic-resolution and its three new inputs. The PDF is absent at literature/demailly-complex-analytic-differential-geometry.pdf. Read online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf (2012 version); no document downloaded. Proof origin remains agent because the literature is absent locally. Printed pp.28--29 cover local solvability; pp.204--205 the soft smooth-ring argument; p.216 the Dolbeault resolution. The online text renderer sometimes prints a greater-than sign for a greater-than-or-equal sign: the local lemma includes q=1 and the acyclicity assertion includes H^1.

## Audit findings and corrections

The item statement is correct and has been kept verbatim. Its inherited source incorrectly locates the type decomposition in I §2; the actual formulas are I §3.C (3.13)--(3.16), pp.23--24, and every proof step uses the corrected locator. No hypotheses or conclusions changed. Added existing definition dependencies for module sheaves and right-derived sheaf cohomology rather than using the scheme-only pqf-def-cohomology on a complex manifold.

The inherited blueprint ancestor is null: blueprint_refs.py ancestor prints None. This is retained on item and new nodes, with the full inherited place and via chain. Searched the entire imported blueprint for Dolbeault, Dolbeault-Grothendieck, fine sheaf, partition of unity, smooth modules, acyclic smooth, Cauchy and exterior derivative; none states a new input. Read the chapter record, unit record and current latest blueprint unit. The item supports the existing Popa/Hodge prerequisite chain under direct-image stability; no unit or chapter is changed. The key unit statement is not this item, so no unit realization fields were edited.

The two off-unit statements are generic tools: lem-pe-ringed-site-derived-evaluation-slice compares module cohomology with underlying abelian sheaf cohomology, and lem-sc-ringed-space-module-sheaves-enough-injectives supplies its hypothesis on (M,C_M). Declared both in split_report.tool_uses. These are not replacement routes for the unit.

## Not duplicates

lem-sfb-local-scalar-dolbeault vs lem-sfb-dolbeault-acyclic-resolution: the former is only the scalar local analytic PDE on an open subset of C^n, with a shrinking neighborhood; it has no manifold sheaf exactness or acyclicity clause. Steps 2--3 carry the coefficient reduction, wedge sign, and sheafification argument for arbitrary p.

lem-sfb-smooth-function-modules-acyclic vs lem-sfb-dolbeault-acyclic-resolution: the former is the general smooth-module vanishing theorem on a real manifold and contains no holomorphic forms, d-bar operator or resolution. Step 4 constructs its module action and reconciles abelian with complex-vector-space cohomology using existing nodes.

lem-sfb-chart-exterior-derivative-square-zero vs lem-sfb-kahler-laplacian-identity: the former is the pointwise real differential-form Mathlib identity; the latter compares metric Laplacians on Kähler manifolds and does not state the local square-zero theorem.

DAG-wide statement/title searches for Dolbeault, fine or soft sheaves, partitions of unity, Cauchy--Riemann and exterior derivatives found only the item, its algebraic comparison parent and metric Hodge nodes, besides unrelated affine sheafification substring hits. A whole-DAG extDeriv_extDeriv search found references in proof/search records, not a node with that statement. The new nodes have no Stacks source tags, so there are no unreported equal-tag pairs. For reused Stacks results read sites-cohomology.tex labels lemma-cohomology-modules-abelian-agree (03FD), lemma-cohomology-of-open (03F3), and injectives.tex lemma-sheaves-modules-space (01DI).

## Review by NY

I read Demailly online at I §3.C and §3.E (3.29), IV §4 (4.12), (4.15), (4.18), (4.19), and IV §6 (6.13)--(6.16). The local scalar statement takes only the smooth p=0 case of (3.29); its q=0 assertion is the Cauchy--Riemann criterion in (3.14). It requires only an open neighborhood of the point and gives a primitive after shrinking, not on every non-Stein open set. For the smooth-module input I checked that Corollary (4.19) applies to every module, not only locally free ones: the smooth ring is soft by (4.12), modules over a soft ring are soft by (4.18), and soft sheaves on a paracompact space are acyclic by (4.15). Hausdorff second-countable locally Euclidean spaces are locally compact with countable base, the class explicitly noted to be paracompact after (4.4); allowing component dimensions to vary does not change that hypothesis. These new nodes are statement-only, and their eventual workers must split these analytic theorems rather than inherit a hidden proof.

Step 1 uses the exact pointwise identity in lem-sfb-chart-exterior-derivative-square-zero. I read Mathlib Basic.lean:229--237; the theorem assumes smoothness at the point and an automatic lower bound on smoothness. The complex coefficient space is regarded as a real normed space, as permitted by its variables. The remaining type decomposition is the coordinate formula and chain rule; the three bidegrees of d squared are distinct, yielding each identity separately. A chart-defined form extends arbitrarily away from a smaller neighborhood of the point, so the global function domain in Mathlib adds no global extension hypothesis.

Step 2 uses exactly the q=0 clause of lem-sfb-local-scalar-dolbeault and the independence of dz_I wedge dbar z_j; it proves, rather than assumes, the degree-zero kernel and injectivity. Step 3 uses its positive-degree local primitive clause separately on finitely many coefficients. I checked the sign: dbar(dz_I wedge beta_I)=(-1)^p dz_I wedge dbar beta_I, so multiplying the primitive by (-1)^p gives alpha. The intersection is finite, hence still a neighborhood. The statement of def-weil-sheaf-of-modules-category explicitly identifies cokernels with sheafifications of sectionwise cokernels; thus local image generation is exactly the needed sheaf exactness. The statement of def-weil-abstract-derived-category supplies cochain-complex and cohomology conventions only, not a theorem about local solvability.

Step 4 uses precisely the vanishing for underlying abelian sheaves in lem-sfb-smooth-function-modules-acyclic. I opened the statements of lem-pe-ringed-site-derived-evaluation-slice and lem-sc-ringed-space-module-sheaves-enough-injectives, and the Stacks .tex labels 03FD, 03F3 and 01DI. The category is the set-sized site of opens of M and the object is its terminal open M; its slice is the same opens category. The ring is the constant complex ring sheaf, not the holomorphic or smooth ring, when applying the comparison. Enough injectives holds for that ringed space by the cited node. Applying evaluation to an injective complex-sheaf resolution and then forgetting scalars computes the same additive cohomology, so zero additive group implies zero vector space. No assertion that the forgetting functor preserves injectives is used.

Step 5 is an elementary case check. Tested point manifolds (positive forms vanish), p or q greater than chart dimension (empty coefficient families), the zero form and q=1 (a smooth function primitive), finite disjoint unions with unequal dimensions, and the empty manifold. Checked the arbitrary smooth-module statement on the zero module, arbitrary modules on a point and a countable discrete 0-manifold. Nothing needs compactness, connectedness, constant dimension, coherence or global d-bar solvability. Every non-elementary fact in the assembly has a cited node. All steps are below 2000 characters, and no new input is a clause of the item transferred without its coefficient or category argument.

I corrected an initial temptation to cite the scheme-only cohomology definition by using the general site definition, and explicitly separated abelian acyclicity from the required complex-linear derived functor. Searches were executed with msearch.py and read before recording: holomorphic primitives in HasPrimitives.lean:115,290 solve a different equation; Smooth.lean defines a sheaf and supplies evaluation statements but no acyclicity. The exterior-square search, in contrast, gives an exact Mathlib specialization and is recorded as a leaf. No fabricated searches, SGA sources, Lean files, compilers, or repository writes are involved.

## Unfinished work

The new unsplit nodes intentionally have no proofs: they are the next stage-1 items. The present item has a complete one-level assembly. Server dry run and push results are recorded below after the required commands finish.

## Dry-run repairs

The first server preflight requested explicit notion citations in the two analysis nodes and a machine-readable Mathlib line field. I opened def-weil-field (it defines fields, exactly the scalar notion used), cited it in both new statements and stmt_deps, and added mathlib_match.line = 229 after reading that declaration in the pinned Mathlib. Refreshed the verbatim citation quotes. No mathematical assertion or proof route changed.
