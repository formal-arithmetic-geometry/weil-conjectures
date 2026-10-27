# Q55 repair: lem-sfb-fermat-kummer-relative-curve

## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-fermat-kummer-relative-curve.json`: statement and statement dependencies unchanged; the nine-step argument is now assembled in five steps, totalling 1953 characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-binomial-chart-smooth-relative-dimension.json`: statement, unsplit, no Mathlib match after actual logged searches. Standard smooth atlas for a diagonal plane hypersurface.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fermat-finite-chart-cover.json`: statement, unsplit, no Mathlib match after actual logged searches. Finite two-root charts of the relative Fermat hypersurface.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-plane-hypersurface-geometric-genus.json`: statement, unsplit, no Mathlib match after actual logged searches. Geometric integrality and genus of a smooth plane hypersurface.
- `dag/nodes/sec-six-functors-basics/lem-sfb-two-root-normal-model-function-field.json`: statement, unsplit, no Mathlib match after actual logged searches. Function field and normalization of a normal two-root chart model.
- `citations.json`: verbatim statement quotations for every citation of every assembly step.
- `searches.jsonl` and saved search outputs: genuine commands and returned hits for all four new nodes. Earlier inherited searches remain in the item unchanged.

Four new nodes, zero Mathlib leaves. Nothing was written in the repository or launcher, and no Lean, compiler, Lake or build command was used. The unit/chapter records are unchanged.

Attachments: none. Searching all project WeilConjectures sources for the exact blueprint tag and for Fermat/Kummer found no completed declaration of this result. The stage-2 theorem `AlgebraicGeometry.RelativeFermatCurve.exists_finite_kummer_cover` in `lean/Sheaf/AlgebraicGeometry/RelativeFermatKummerCurve.lean`, lines 215--284, states the item but ends with `sorry`. It is not an attachment. The existing helpers construct actual equation data and do not prove the four new lemmas.

WANTED: de Jong, *Families of curves and alterations* (1997), §3.5, printed p.607, for lem-sfb-fermat-kummer-relative-curve. This PDF is absent locally. I retain the previous worker's source record and report, but do not claim to have read its publisher copy. The present explicit argument is marked agent-written and follows the available Stacks passages.

The returned fault was excessive proof size, not a false statement. No STATEMENT-DISPUTED correction was needed, and no hypothesis, conclusion, equation, genus or function-field embedding of the item changed. The sandbox initially contained only dispatcher marker files: there was no prior local item/report/search log to resume. I copied the current repository item, whose nine proof steps match the return description, and retained the earlier NH report below. Stage-2 Lean and review metadata were preserved. The delivery tool rebases only the authorized split fields on current server main.

## Repair of the return

The human requested that the old 7776-character proof become a short assembly with at least two comparable, independently startable statement-only nodes. This delivery creates four, rather than moving the proof into one replacement theorem. Their responsibilities partition the work as follows:

| New task | Original work retained |
| --- | --- |
| lem-sfb-fermat-finite-chart-cover | Steps 1--3: degree-zero Proj chart rings; the two charts cover; overlap substitutions and map gluing over base opens; two monic module bases; finiteness local on the target; lifting arbitrary residue-field points and infinity. Also the coefficient base-change/fibre-identification part of step 5. |
| lem-sfb-binomial-chart-smooth-relative-dimension | Step 4: localized presentations with an inverse variable, the two explicit Jacobian determinants, affine scheme smoothness, open-local assembly, persistence after field extension, dimension 3-2, and the specified H-projective embedding. The statement allows arbitrary unit coefficients and positive invertible n. |
| lem-sfb-smooth-plane-hypersurface-geometric-genus | Step 5's H0/idempotent argument over every field extension, step 6's field-base normal-integral argument, and step 7's genus interpretation and formula. The statement concerns any nonzero smooth plane equation, rather than just the item's Fermat equation. |
| lem-sfb-two-root-normal-model-function-field | Steps 8--9: fraction fields and localization to K; injection and transcendence of x; generation and finiteness of K(x)(a,b); target integrality; Noetherian normal affine sections; both integral-closure inclusions; localization and overlap compatibility. Normal integrality of a general finite two-root model is a hypothesis, independently of how that model was produced. |

The total-space application in old step 6 remains a short direct invocation of the already existing family core. The numerical genus bound remains in the assembly. Thus none of the old argument disappears: the complete original text, sources and dependency lists are transcribed below, labelled with the receiving tasks, so their future workers have the actual argument rather than a vague summary. All four new JSON files have `status: unsplit`, empty `proof` and `proof_deps`, and null `proof_origin`; the retained arguments are in this report, not illicit proof sketches in their statements.

## Mathlib, DAG and blueprint searches

For each new node I ran LeanFinder with two distinct semantic phrasings, Loogle, grep through the named AlgebraicGeometry Mathlib subtree, and LeanSearch, using only the required msearch.py command. All these calls returned successfully. Every exact query and full response is in the node's mathlib_searches and the sandbox outputs, and each query appears in searches.jsonl. I read all returned signatures. The item retains its already completed searches, which already concern exactly this unchanged statement.

For the finite-chart task the hits concern affine-space surjectivity, Weierstrass coordinate-ring power bases or abstract monic-root rings. None constructs these two compatible charts and the finite surjective relative map. For the smooth atlas task the second phrasing returned `Algebra.SubmersivePresentation.isStandardSmooth` and general standard-smooth/relative-dimension constructors. They require the explicit presentations and determinant units to be supplied: the task is not a one-line specialization. I read `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:84` and its surrounding atlas/base-change criteria. For the plane-geometry task the hits concern Weierstrass integrality and general scheme geometric-integrality definitions, not the general degree-genus theorem. For the normal-model task the extra Loogle and grep found `IsIntegralClosure.of_isIntegrallyClosed`, `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean:272`; I opened lines 258--280. It supplies the final ring-theoretic inclusion once a suitable normal domain and fraction field are established. It does not construct the specified K(x) embedding, compute the two-root function field, prove the target integral, or glue the scheme normalization. I therefore did not mislabel the whole node as a Mathlib leaf. The earlier Loogle query for Scheme.normalizationIn returned an unknown-identifier diagnostic; it was retained exactly, and the subsequent valid integral-closure pattern replaced it as the useful search.

Before making the nodes I searched whole-DAG titles and statements for Fermat, plane curve/hypersurface, diagonal hypersurface, two-root charts/models and finite normal models, and the source tags 0BYA, 0BYD, 00T7, 0358 and 01RV. I opened the statements of all same-tag candidates. The existing general cohomology, standard-smooth, affine function-field and normal-sections nodes are reused as intended inputs, not recreated. The quadratic formal-series node concerns a completed local plane singularity and its total quotient ring; the perfect-closure finite-normal-model node changes a ground field purely inseparably; neither supplies these chart/field statements.

Whole-blueprint searches using blueprint_refs.py for `Fermat`, `plane curve`, `standard smooth`, `normalization finite`, `two-root`, `diagonal plane`, and `normal model` found no blueprint duplicates of these new statements. The ancestor command returns None for this already live-created chain. Each new node therefore retains the null from.node and extends the actual via chain by the item; its exact source work is recorded in from.place. No invented imported ancestor is substituted. The blueprint place is the constructible-direct-image alteration reduction through ILO X Lemma 2.2, as inherited by the item; the current direct-images proof (3), chapter record and unit record were read. No route or coefficient category was changed, and no SGA source is used.

## Review by Q55

I read Stacks curves.tex Tag 0BYA (section-plane-curves), including the Fermat example, and the whole statement and proof of Tag 0BYD (lemma-genus-plane-curve); algebra.tex Tag 00T7 (lemma-standard-smooth), in particular parts (1), (5), (7); properties.tex Tag 0358 (lemma-normal-integral-sections). I opened the existing affine function-field statement (01RV), all original cited statements, the current stage-2 Fermat module/docstring, and the old NH report. The relative chart formulas and normalization equality are the old explicit agent argument; Stacks does not state this entire relative package verbatim. Each new node's source says exactly which original steps are generalized.

Assembly step 1 uses only the new finite-chart-cover statement. I read it and checked that it gives the formula, exact inverse-image opens, both monic rings, overlap substitutions, finite surjectivity, and base-change hypersurface identification, not merely abstract existence of some cover. Its sole input n>=1 follows from ell>=5. No normality or root-of-unity hypothesis is silently used.

Assembly step 2 uses the new diagonal-atlas statement with coefficients 1,-1,-1, which are units in every characteristic. It gives smoothness of the actual zero scheme, relative dimension one and H-projectivity; it also specifies the localized presentations and their base-change behaviour. I recomputed the determinants as lambda*n*s^n and mu*n*t^n, using variables (s,z) and (t,z). Since the constant coefficient is a unit, s and t generate the unit ideal modulo the equation, so these principal opens cover. The hypothesis that ell is invertible is precisely the needed determinant hypothesis, and no regularity of U over the ground field is assumed. The earlier C4 repair (passing from ring smoothness to affine schemes, then restricting base opens and using source-local smoothness) remains in the retained original step, with its actual cited statements, for the new task to implement.

Assembly step 3 cites the finite-chart-cover for the fibre identification and the smooth-plane-hypersurface node for geometric integrality, connectedness over all extensions, and genus. These clauses are explicit in both cited statements. The degree stays ell and the polynomial is nonzero even in characteristic 2 because its A^ell coefficient is 1. Smooth relative dimension one comes from step 2, before the plane-geometry theorem is applied. Its field-extension quantifier is arbitrary, not just algebraic closures. The scalar H0 statement rules out an empty hypersurface, so the general task needs no rational point. In the original Fermat instance [1:0:1] still supplies one. Connectedness uses the existing idempotent equivalence, and field-base normal integrality uses the already present smooth-family core, not merely the definition of geometric integrality. The arithmetic ell>=5 estimate is written in the assembly.

Assembly step 4 cites lem-sbc-smooth-connected-generic-geometry-core. I opened its full statement: integral base with integrally closed local rings, smooth map with geometrically connected fibres and nonempty source imply integral total space with integrally closed local rings. U satisfies exactly its base conditions, step 2 supplies smoothness, step 3 supplies geometric connectedness of every fibre, and [1:0:1] with U nonempty supplies a nonempty source. No Noetherian or separatedness condition has been inferred from a definition that does not supply it. This is the only off-unit proof tool left directly in the parent assembly, and is declared in split_report.tool_uses for maintainer review.

Assembly step 5 uses the new two-root normal-model theorem. Its hypotheses are all available: U integral finite type over the given field, q finite surjective with both compatible chart presentations from step 1, and normal integral source from step 4. The new statement pins down the inclusion K(x)->k(Y) via q, its coordinate generators, its finite field extension and the normalization isomorphism over the specified P1, not a bare abstract field or scheme isomorphism. I checked the retained argument: choose a nonempty affine base open, pass to its fraction field K, use the monic basis to make K[x] inject, and take the common fraction field of the integral source chart. For the target, polynomial chart rings are domains; surjectivity plus source irreducibility gives target irreducibility. The section-ring normality argument applies to Noetherian affine opens coming from finite-type base charts and their finite presentations. A nonzero domain can be a finite product of nonzero domains only with one factor. Every z integral over B is integral over S by the same monic polynomial, giving the reverse integral-closure inclusion. This is why normality of Y is a hypothesis in the new task and is proved before invoking it. The new theorem does not depend on the parent and no cycle is introduced.

B1--B7 checks were mathematical as well as structural: all objects of each new statement are locally introduced; normality and module basis have literal meanings in the statement; scheme, polynomial, geometric, smooth, projective, cohomology and normalization notions have their actual definition dependencies. The new statements contain conclusions and presentations, with no proof sketches. All proper Stacks tags and labels were checked against the local tag table. I kept the source's unit-coefficient conditions in the diagonal theorem and its degree positivity; I did not assert smoothness for a coefficient or degree that could vanish. C1/C4 were checked by reading the actual statements used above; citations.json copies those statements verbatim. The original proof dependencies are preserved in the task allocation below, including the affine-chart base-change and smooth-affine bridges added at the earlier maintainer review. None of the five assembly steps is longer than 2000 characters or conceals a further independent comparison argument.

Small cases: the chart theorem works at n=1, when both monic bases have one element and the line maps isomorphically to P1; at x=0 the equations force a=0 and b^n=-1, at x=1 they force b=0 and a^n=1; infinity has [1:1:0]. The theorem deliberately allows inseparable n in characteristic dividing n, because it claims no smoothness or normality. Empty base and zero chart rings cause no failure. For the diagonal atlas n=1 gives a relative line; over characteristic 2 the coefficients +/-1 remain units; if the characteristic divides n the determinant fails, and that case is explicitly excluded. For the smooth plane theorem d=1,2 give genus 0 and d=3 gives genus 1; a double line F=A^2 is excluded by the smoothness hypothesis, although the reused cohomology input legitimately includes it. The zero polynomial and d=0 are excluded. For the normal-model theorem n=1 reduces to K(x), while characteristic-dividing-n two-root rings need not be domains/normal and are therefore not silently covered without its supplied Y hypotheses. Singular normal U and positive-dimensional U are allowed throughout. The primitive-root and prime hypotheses of the parent remain unchanged even though these four geometric inputs need less.

The correction made during this reading was to define module basis inline instead of citing a nonexistent definition id, and to restrict dependency extraction to actual node references rather than polynomial-variable brackets. This changed no mathematical assertion. Definition references for connectedness, H-projectivity and integral closure were made explicit. Searches were retained with their actual responses, including the unsuccessful identifier pattern; nothing is recorded as a match or as a service outage contrary to the response.

## Not duplicates

lem-sfb-binomial-chart-smooth-relative-dimension vs sbc-lem-affine-space-smooth: the existing statement, titled 'Affine space is smooth', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-zl-bertini-singular-first-order-model: the existing statement, titled 'First-order linear kernel containing a Bertini singular fibre', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-zl-hypersurface-nonzero-relative-differential: the existing statement, titled 'Nonzero relative differential gives a smooth hypersurface point', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-trf-smooth-local-tangent-cone-extension: the existing statement, titled 'Tangent cone and minimal-prime dimensions of an essentially smooth local extension', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-pd-relative-smooth-dimension-codescent: the existing statement, titled 'Fixed relative smooth dimension descends under faithfully flat ring base change', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-pc-smooth-characterization: the existing statement, titled 'Smoothness versus flatness', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-sfb-plane-hypersurface-cohomology: the existing node computes coherent H0 and H1 for arbitrary possibly nonreduced plane equations; it does not construct a relative map/atlas or prove geometric integrality. Its cohomology result is an intended reused input, not recreated as the same theorem.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-sfb-fermat-kummer-relative-curve: the item combines relative finite cover, smooth normal integral family, high-genus fibres and normalization for prime ell>=5; this new task is a strictly smaller chart/atlas/field-geometry/normal-model input with its own weaker hypotheses and no dependence on the item.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-standard-smooth-base-change: the existing statement, titled 'Base change of a standard smooth presentation', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-standard-smooth-conormal-basis: the existing statement, titled 'The conormal module of a standard smooth presentation is free on the equations', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-standard-smooth-over-field-dimension-at-points: the existing statement, titled 'A standard smooth algebra over a field has dimension n-c at every point', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-smooth-locally-standard-smooth: the existing statement, titled 'Smooth morphisms are locally standard smooth', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-smooth-over-product-ring: the existing statement, titled 'Smoothness over a product ring is checked factorwise', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-standard-smooth-is-smooth: the existing statement, titled 'A standard smooth algebra is smooth', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-polynomial-ring-smooth: the existing statement, titled 'A polynomial ring in finitely many variables is smooth over its coefficient ring', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound: the existing statement, titled 'Over an algebraically closed field, few differentials at a closed point imply smoothness there', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-weil-pbc-standard-smooth-kahler-basis: the existing statement, titled 'Differentials of a standard smooth algebra are free of rank n-c', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-binomial-chart-smooth-relative-dimension vs lem-pur-etale-at-point-from-differentials: the existing statement, titled 'Differential criterion for an etale coordinate map', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-fermat-finite-chart-cover vs lem-sfb-plane-hypersurface-cohomology: the existing node computes coherent H0 and H1 for arbitrary possibly nonreduced plane equations; it does not construct a relative map/atlas or prove geometric integrality. Its cohomology result is an intended reused input, not recreated as the same theorem.

lem-sfb-fermat-finite-chart-cover vs lem-sfb-fermat-kummer-relative-curve: the item combines relative finite cover, smooth normal integral family, high-genus fibres and normalization for prime ell>=5; this new task is a strictly smaller chart/atlas/field-geometry/normal-model input with its own weaker hypotheses and no dependence on the item.

lem-sfb-smooth-plane-hypersurface-geometric-genus vs lem-sfb-plane-hypersurface-cohomology: the existing node computes coherent H0 and H1 for arbitrary possibly nonreduced plane equations; it does not construct a relative map/atlas or prove geometric integrality. Its cohomology result is an intended reused input, not recreated as the same theorem.

lem-sfb-smooth-plane-hypersurface-geometric-genus vs lem-sfb-fermat-kummer-relative-curve: the item combines relative finite cover, smooth normal integral family, high-genus fibres and normalization for prime ell>=5; this new task is a strictly smaller chart/atlas/field-geometry/normal-model input with its own weaker hypotheses and no dependence on the item.

lem-sfb-two-root-normal-model-function-field vs lem-sbc-normal-sections-finite-product: the existing node gives a finite product description of normal section rings; the new task computes the specified K(x) two-root function field and identifies a finite model with normalization over P1, using that section-ring input.

lem-sfb-two-root-normal-model-function-field vs lem-sbc-relative-normalization-normal-stalks: the existing statement, titled 'Normal stalks of relative normalization in a locally Noetherian normal source', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-two-root-normal-model-function-field vs def-sc-rational-functions: the existing statement, titled 'The ring of rational functions of a scheme', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-two-root-normal-model-function-field vs lem-sc-integral-function-field-affine-fraction: the existing statement, titled 'Function field of an integral scheme is the fraction field of an affine open', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-two-root-normal-model-function-field vs lem-sc-rational-functions-generic-stalks: the existing statement, titled 'Rational functions are the product of the generic local rings', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-two-root-normal-model-function-field vs lem-weil-pbc-normalization-normal-stalks: the existing statement, titled 'The normalization of a scheme in a normal integral scheme has integrally closed local rings', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

lem-sfb-two-root-normal-model-function-field vs lem-sc-integral-scheme-stalks-in-function-field: the existing statement, titled 'Integral schemes: sections and stalks inject into the function field', concerns its own general smoothness/normality/rational-functions assertion; it does not provide the new task's explicit diagonal atlas, two-root field presentation or geometric-plane-curve conclusion. Its statement was read in the same-tag comparison.

## Retained original arguments and source citations

These are the complete nine proof texts from the current returned head, not a shortened reconstruction. The four new statement-only nodes queue these arguments for separate workers. No proof below is claimed as an additional split of a new node.

### Original step 1 -> lem-sfb-fermat-finite-chart-cover

Over an affine base open $V=\operatorname{Spec}R$, use the standard Proj opens: a homogeneous degree-zero fraction with denominator a power of $C$ is a polynomial in $A/C,B/C$. The same calculation applies with denominator $A$. The affine base-change identification transports these charts from $\mathbf Z$ to $R$, by tensoring their polynomial presentations. Thus $D_+(C)\cap C_\ell=\operatorname{Spec}R[a,b]/(a^\ell-b^\ell-1)$ and $D_+(A)\cap C_\ell=\operatorname{Spec}R[u,v]/(u^\ell+v^\ell-1)$, where $(a,b)=(A/C,B/C)$ and $(u,v)=(B/A,C/A)$. They cover: a homogeneous prime containing $A,C$ also contains $B$ by the equation, hence is irrelevant. Map the first chart to the $x$-chart by $x=a^\ell$, and the second to the $y$-chart by $y=v^\ell$. On the overlap $v=a^{-1}$ and $u=b/a$, so $y=x^{-1}$. The morphism-gluing lemma, also on overlaps of base opens, gives $\rho$ with precisely the stated formula.

Inputs: def-pc-proj, lem-weil-pbc-affine-chart-base-change-iso, lem-weil-pbc-scheme-morphism-gluing

Source: {"document": "literature/stacks-project/curves.tex", "place": "Section 0BYA, section-plane-curves: standard affine pieces; explicit relative coordinate calculation and gluing."}

### Original step 2 -> lem-sfb-fermat-finite-chart-cover

The inverse image of the $x$-chart is exactly the $C$-chart, and its algebra has the presentation $R[x,a,b]/(a^\ell-x,b^\ell-(x-1))$. Apply the monic-quotient power-basis lemma first to $a^\ell-x$ and then over that quotient to $b^\ell-(x-1)$. It is free over $R[x]$ with basis $a^i b^j$, $0\leq i,j<\ell$, in particular finite. The other chart similarly has presentation $R[y,u,v]/(v^\ell-y,u^\ell-(1-y))$ and basis $u^i v^j$. These are affine inverse images of an affine cover of $\mathbf P^1_U$, so finiteness local on the target proves that $\rho$ is finite.

Inputs: lem-weil-pbc-monic-quotient-free, lem-weil-pbc-finite-local-on-target

Source: {"document": "literature/stacks-project/curves.tex", "place": "Section 0BYA; two monic equations on each target chart."}

### Original step 3 -> lem-sfb-fermat-finite-chart-cover

For a point of $\mathbf P^1_U$ with finite coordinate $x=t$ in its residue field, choose an algebraic closure $\Omega$ of that field. The polynomials $T^\ell-t$ and $T^\ell-(t-1)$ have roots $a,b$ in $\Omega$, giving the point $[a:b:1]$ of $C_\ell$ mapping to the chosen point. Above infinity use $[1:1:0]$. This proves surjectivity on all points, including points over nonclosed points of $U$. Existence of the closure and its root property are exactly the algebraic-closure node.

Inputs: def-weil-algebraic-closure

Source: {"document": "literature/stacks-project/curves.tex", "place": "Section 0BYA; direct geometric-point calculation."}

### Original step 4 -> lem-sfb-binomial-chart-smooth-relative-dimension

Both chart equations have the form $f=s^\ell+\epsilon t^\ell-1$, where $\epsilon=\pm1$. The opens $D(s),D(t)$ cover, since $(s,t)$ contains $1$ in the quotient. On $D(s)$ write its ring as $R[s,z,t]/(f,sz-1)$; the Jacobian determinant for the first two variables $(s,z)$ is $\ell s^\ell$, a unit. On $D(t)$, using variables $(t,z,s)$ and relation $tz-1$, the determinant is $\epsilon\ell t^\ell$, also a unit. These are standard smooth presentations with $n=3,c=2$. Standard smooth algebras are smooth ring maps, so each $\operatorname{Spec}$ of these localized chart rings is smooth over $\operatorname{Spec}R$ by the ring-map/affine-morphism equivalence. Composing with the open immersion $\operatorname{Spec}R=V\subseteq U$ keeps it smooth (open-subscheme lemma, part (b)), and these opens, over all $V$, cover $C_\ell$; smoothness is local on the source, so $C_\ell\to U$ is smooth. For a field $L$ with a map $R\to L$, the base-change lemma for standard smooth presentations gives the same presentations with coefficients in $L$, and the standard-smooth dimension theorem gives dimension $3-2=1$ at every point of each fibre. The given closed embedding into $\mathbf P^2_U$ makes the morphism H-projective by definition.

Inputs: def-weil-pbc-standard-smooth-algebra, lem-weil-pbc-standard-smooth-is-smooth, lem-weil-pbc-smooth-ring-map-iff-smooth-affine, lem-weil-pbc-smooth-restrict-open-subschemes, lem-weil-pbc-smooth-local-on-source, def-sbc-smooth-morphisms, lem-weil-pbc-standard-smooth-base-change, lem-weil-pbc-standard-smooth-over-field-dimension-at-points, def-kun-projective

Source: {"document": "literature/stacks-project/curves.tex", "place": "Section 0BYA, Fermat example; Tag 00T7, algebra-lemma-standard-smooth, parts (1),(7)."}

### Original step 5 -> lem-sfb-fermat-finite-chart-cover (fibre identification) and lem-sfb-smooth-plane-hypersurface-geometric-genus (cohomology and connectedness)

Let $L$ be any field equipped with a point $\operatorname{Spec}L\to U$. The fibre after this extension is the plane hypersurface $A^\ell-B^\ell-C^\ell=0$ over $L$: if $\operatorname{Spec}L\to U$ lands in the base open $V=\operatorname{Spec}R$, the affine base-change identification gives the charts $\operatorname{Spec}(L\otimes_R R[a,b]/(a^\ell-b^\ell-1))=\operatorname{Spec}L[a,b]/(a^\ell-b^\ell-1)$ and likewise for the $A$-chart, with the same gluing as in step 1, and these are the standard Proj charts of $\operatorname{Proj}(L[A,B,C]/(A^\ell-B^\ell-C^\ell))$. Its equation remains nonzero homogeneous of degree $\ell$. The plane-hypersurface cohomology lemma gives $\Gamma(C_{\ell,L},\mathcal O)=L$. It is nonempty because $[1:0:1]$ is an $L$-point. In a field an idempotent satisfies $e(e-1)=0$, hence is $0$ or $1$; the connectedness/idempotents lemma therefore proves connectedness. The identical argument over every further field extension proves that every fibre is geometrically connected.

Inputs: lem-weil-pbc-affine-chart-base-change-iso, def-pc-proj, lem-sfb-plane-hypersurface-cohomology, lem-pc-scheme-connected-iff-idempotents

Source: {"document": "literature/stacks-project/curves.tex", "place": "Tag 0BYD, lemma-genus-plane-curve: H0 calculation; connectedness via idempotents."}

### Original step 6 -> parent assembly step 4 (total family) and lem-sfb-smooth-plane-hypersurface-geometric-genus (field-base case)

Apply the normal-integral smooth-family geometry core to $C_\ell\to U$: the base is integral with integrally closed local rings by hypothesis, the map is smooth by step 4, its fibres are geometrically connected by step 5, and its source is nonempty by $[1:0:1]$. It follows that $C_\ell$ is integral and all its local rings are integrally closed. For each $L$ as in step 5, apply the same core to $C_{\ell,L}\to\operatorname{Spec}L$. A field is an integrally closed domain, and smoothness and geometric connectedness for this map were proved directly over $L$ and its extensions. Thus $C_{\ell,L}$ is integral for every such $L$. This is geometric integrality of every fibre. Step 4 supplies their dimension one.

Inputs: lem-sbc-smooth-connected-generic-geometry-core, def-pc-geometrically-irreducible

Source: {"document": "literature/stacks-project/curves.tex", "place": "Normal-family facts: Tags 034F, 056T and 01UA, as in the cited core; Section 0BYA supplies the smooth Fermat charts."}

### Original step 7 -> lem-sfb-smooth-plane-hypersurface-geometric-genus (formula), parent assembly step 3 (numeric bound)

For a geometric fibre over an algebraically closed field $\Omega$, steps 4 and 6 give a smooth projective geometrically integral curve. By the definition of genus its genus is $\dim_\Omega H^1(C_{\ell,\Omega},\mathcal O)$. Substituting $d=\ell$ into the plane-hypersurface cohomology lemma gives $(\ell-1)(\ell-2)/2$. Since $\ell\geq5$, the product is at least $4\cdot3$, and the genus is at least $6$, hence at least $2$.

Inputs: lem-sfb-plane-hypersurface-cohomology, def-pc-genus

Source: {"document": "literature/stacks-project/curves.tex", "place": "Tag 0BYD, lemma-genus-plane-curve."}

### Original step 8 -> lem-sfb-two-root-normal-model-function-field

Choose a nonempty affine base open $\operatorname{Spec}R\subset U$, and put $K=k(U)=\operatorname{Frac}R$ using the affine function-field theorem. The corresponding $C$-chart is nonempty (it contains $[1:0:1]$), hence is an affine open of the integral scheme $C_\ell$. Its fraction field is $k(C_\ell)$ by the same theorem. Localizing its ring at $R\setminus\{0\}$ identifies that fraction field with $\operatorname{Frac}(K[a,b]/(a^\ell-b^\ell-1))$. The free basis from step 2 proves that $K[x]$ injects in this ring under $x=a^\ell$, so $x$ is transcendental over $K$. Its fraction field is generated over $K(x)$ by $a,b$, and the defining equations are exactly $a^\ell=x$, $b^\ell=x-1$. The monic equations show that this extension is finite. Thus this is the field in the assertion, with its specified embedding of $K(x)$.

Inputs: lem-sc-integral-function-field-affine-fraction, lem-weil-pbc-monic-quotient-free

Source: {"document": "literature/stacks-project/curves.tex", "place": "Section 0BYA; affine fraction-field calculation for the displayed equation."}

### Original step 9 -> lem-sfb-two-root-normal-model-function-field

First check that the normalization base $\mathbf P^1_U$ is integral. Its affine chart rings $R[x]$ and $R[y]$ are domains, since $R$ is a domain and leading coefficients multiply; thus it is reduced. Two nonempty target opens have nonempty inverse images by step 3, and these intersect because $C_\ell$ is irreducible by step 6. Thus the target is nonempty and irreducible, hence integral. Its affine-chart fraction field is $K(x)$ by the affine function-field theorem. Work on a cover of $U$ by affine opens whose rings are finitely generated over the ground field, as provided by finite type. Each inverse-image ring $S$ of a target chart in step 2 is also a finitely generated algebra over that field, so is Noetherian by the affine-Noetherian lemma. Its spectrum is an open of the normal integral scheme $C_\ell$. The normal-sections lemma makes $S$ a finite product of integrally closed domains. Since $S$ is a nonzero domain, a product decomposition has exactly one factor, so $S$ itself is integrally closed. Its fraction field is the field $L=k(C_\ell)$ by the affine function-field theorem. If $B$ is the corresponding ring $R[x]$ or $R[y]$, step 2 makes $S$ integral over $B$, and $B\subset S\subset L$. Conversely, an element $z\in L$ integral over $B$ satisfies the same monic equation over $S$, so belongs to $S$ by its integral closedness. Thus $S$ is precisely the integral closure of $B$ in $L$. On overlaps these equalities are compatible with localization and the coordinate substitutions of step 1. The affine definition of normalization therefore identifies $\rho:C_\ell\to\mathbf P^1_U$ with the normalization in $L$.

Inputs: def-weil-finite-type-morphism, lem-wf-affine-noetherian-components, lem-sbc-normal-sections-finite-product, lem-sc-integral-function-field-affine-fraction, def-fin-normalization-extension, def-pc-integral-scheme

Source: {"document": "literature/stacks-project/curves.tex", "place": "Tag 0358, properties-lemma-normal-integral-sections, via the cited normal-sections lemma; normalization is integral closure chartwise."}

## Prior NH report, retained verbatim

The following historical report describes the old split and its original searches, not new Q55 search calls. Its earlier nine-step organization and claim that no task exceeds 2000 characters are superseded by the human's present spreading-of-work requirement. The retained report is not presented as an independent Q55 review.

# NH: lem-sfb-fermat-kummer-relative-curve

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fermat-kummer-relative-curve.json`: item, split into nine proof steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-plane-hypersurface-cohomology.json`: new statement-only node, unsplit; not in Mathlib after the logged searches. It computes H0 and the dimension of H1 for an arbitrary nonzero positive-degree plane equation, including nonreduced equations. It is not a Fermat-curve smoothness or genus clause repackaged under another name.
- `citations.json`: every step/dependency pair, with a verbatim quotation from the cited statement.
- `searches.jsonl`: genuine search-command log; retained with the search results summarized in the nodes.

One new node, zero new Mathlib leaves. No Lean written or compiled. No unit or chapter records changed: this auxiliary node is not its unit's key statement.

## Attachments

None. Searching the project for the exact item id, Fermat, and the plane-cohomology/genus concepts found no declaration stating the item or the new node. The only project file matching Fermat is `WeilConjectures/RingTheory/SubsingletonH1CotangentOfCharP.lean`, whose occurrence is the finite-field Fermat identity in a different commutative-algebra argument. It does not construct a Fermat curve. Mathlib's projective Weierstrass constructions concern cubic elliptic curves; polynomial FLT is an assertion about polynomial solutions. Neither states this item.

## Literature

WANTED: de Jong, *Families of curves and alterations* (1997), §3.5, printed p.607, for lem-sfb-fermat-kummer-relative-curve. The local PDF named in the inherited source record is absent. The inherited reference to a publisher-PDF reading belongs to the creator's record, not to NH's checks.

I read `literature/stacks-project/curves.tex`, Section 0BYA (`section-plane-curves`), including its Fermat example, and the whole statement and proof of 0BYD (`lemma-genus-plane-curve`). I also read Algebra 00T7 (`lemma-standard-smooth`) with its determinant definition, and Properties 0358 (`lemma-normal-integral-sections`). The relative coordinate, map, and normalization arguments are written out in the item and marked agent-written; no missing de Jong argument is silently cited as a proof. No SGA source is used.

## What changed and what was wrong

The imported item had no proof. Its statement is consistent: the equation, coordinate x, two radical equations, and genus all agree. No statement dispute or correction is needed. I retained its hypotheses, including primitivity of the root of unity, although this particular geometric construction needs only that ell is invertible (and the numerical lower bound for genus).

I supplied an actual chart proof rather than creating a node for each conclusion. The new node is the independent structure-sheaf cohomology calculation for all plane hypersurfaces. H0 is needed before integrality is known, so a genus lemma assuming an integral curve would not suffice. The proof of 0BYD applies here without presupposing integrality of Z: nonzero F acts injectively on the polynomial ring, giving the exact sheaf sequence used in its proof. The source's equidimensional/no-embedded-point framework is not being used as an extra hypothesis without proof. The exact-sequence calculation itself works for every nonzero homogeneous F of positive degree.

I avoided using `lem-sc-smooth-normal`, which concerns curves over a field, to claim normality of the total space over a possibly singular higher-dimensional base. I also avoided taking a definition of normalization as a theorem that every normal finite cover is that normalization: step 9 proves the two inclusions of coordinate rings.

No previous sandbox split, report, citations, or searches existed when I began; the sandbox held dispatcher marker files only. The item's inherited Mathlib searches remain in it, and the searches performed by this worker are recorded separately in its search fields and in the log.

## Mathlib and blueprint searches

I ran the required leanfinder, loogle, grep and leansearch commands for both subjects. For the new node I also tried the second semantic phrasing about the structure sheaf of a degree-d hypersurface and a broader grep for cohomology/genus in AlgebraicGeometry. I read the returned signatures: they construct Proj/its structure sheaf or concern group, cotangent, etale, or elliptic-curve cohomology; none computes these coherent groups. The broader grep's actual source hits in `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean` define pro-etale ell-adic cohomology, which is a different coefficient sheaf and topology. There is no candidate that specializes in one line.

Whole-DAG searches included titles/statements for plane curves and hypersurfaces, genus, normality of smooth families, normal global sections, monic quotients, standard smoothness and function fields. Blueprint-reference searches for `plane curve`, `plane hypersurface`, `hypersurface`, `genus`, and `0BYD` found no blueprint node stating the new cohomology result. Existing monic-quotient, smooth-family, connectedness, function-field, and normal-sections nodes were reused. The ancestor tool returns `None` for this live-created chain; I retained the item's inherited null ancestor and extended its via chain exactly for the new node rather than inventing an imported ancestor.

## Not duplicates

lem-sfb-plane-hypersurface-cohomology vs lem-sfb-fermat-kummer-relative-curve: the former computes coherent H0 and H1 for every nonzero homogeneous plane equation, including singular and nonreduced ones, over any field; the item constructs a relative finite morphism and proves smoothness, integral fibre geometry and normalization for a specific Fermat equation. The cohomology lemma supplies an input to the proof, not its entire conclusion.

lem-sfb-plane-hypersurface-cohomology vs new-picard-residue-homology-naturality-fixed-positive: the existing node chooses comparisons in a residue-homology naturality problem; its 0BYD reference is a counterexample involving a cubic, not a plane-hypersurface cohomology theorem.

lem-sfb-plane-hypersurface-cohomology vs new-picard-residue-homology-geometric-naturality-fixed-per-index: the existing node chooses per-index comparisons and derived arrows for residue naturality; its 0BYD reference does not assert H0 or H1 for a plane equation.

lem-sfb-plane-hypersurface-cohomology vs new-picard-residue-homology-naturality-fixed: this is another residue-comparison existence assertion, including an empty family, and cites the cubic example only in its source-error discussion. It does not compute plane-hypersurface cohomology.

These are all existing nodes found by the shared 0BYA/0BYD tag search.

## Review by NH

I read the source passages listed above for the item and the one new node, and opened every cited node's actual statement. The following are the checks on the mathematical inferences, not just their dependency fields.

1. The Proj node really identifies standard opens with degree-zero localizations. The affine base-change node really identifies their pullbacks with tensor-product spectra and specifies both projections; tensoring the displayed integer polynomial presentations gives the rings over R. The scheme-morphism gluing node supplies gluing and uniqueness. I checked the ratios u=b/a and v=1/a and both target coordinates, so the overlap identity is y=1/x. There are no base points, since A=C=0 implies B=0 at a homogeneous prime.
2. The monic-quotient node supplies the actual power basis, not just integrality. Applying it twice gives ell-squared basis vectors on each target chart, so those rings are finite modules. The finite-local-on-target node states precisely that affine inverse images and finite ring maps on a cover suffice; I checked that these inverse images are exactly the two source opens.
3. The algebraic-closure node includes both existence of a closure and roots of nonconstant polynomials. Its hypotheses apply to the residue field of every target point. The point with finite coordinate t has the explicitly specified preimage, and infinity has [1:1:0]. This does not assume that target points are rational over the original ground field.
4. The standard-smooth definition requires a unit determinant for the first c variables. Reordering the variables as written makes the determinants ell*s^ell and epsilon*ell*t^ell. Both are units on their respective opens because ell is invertible and the inverted variable has an explicit inverse. The standard-smooth-is-smooth node supplies smoothness. The smooth-morphism node explicitly identifies the affine-local ring-map convention with scheme smoothness. The field dimension node states dimension at every point n-c, and here n=3,c=2. H-projectivity is the literal given closed immersion in the definition, not a claim that every projective morphism has a projective-space embedding under another convention.
5. The new cohomology statement applies before reducedness or integrality has been proved. For every residue-field extension the equation is still nonzero of the same positive degree, and [1:0:1] remains a point. Its H0 assertion and the existing connectedness/idempotents equivalence yield connectedness over every further extension; the field idempotent calculation is written explicitly.
6. The smooth-connected-family core gives integral total space with integrally closed local rings, exactly what the step uses. Its base hypotheses hold for U by assumption, and separately for each field L. Smoothness and geometrically connected fibres were established by the same explicit formulas over every L, so using the core over Spec L is legitimate. The geometric-integrality definition quantifies over all extensions; the argument indeed covers all of them, not just the original residue fields.
7. Genus is defined as the dimension of structure-sheaf H1 for a smooth projective geometrically irreducible curve. Those conditions are already available from steps 4 and 6. The new lemma computes that dimension. The estimate at ell=5 is 6, so the asserted lower bound 2 holds.
8. The affine function-field theorem explicitly covers any integral scheme, not only curves, and says the generic stalk is the fraction field of each nonempty affine open. It applies to U and to the source chart. The monic basis proves the injection of K[x]; hence the use of a rational function variable is justified. Localization at R minus zero does not change the fraction field. The two monic equations and the displayed coordinate generators give exactly K(x)(a,b), without replacing the field by an unspecified component.
9. I also checked the hypothesis that the normalization target is integral: its polynomial coordinate rings are domains, and any two nonempty target opens have nonempty, intersecting inverse images in the integral source. This gives reducedness and irreducibility explicitly and identifies the target function field with K(x) by the affine function-field theorem. The affine-Noetherian node applies to the chosen finite-type affine base charts and their finitely generated hypersurface algebras. The normal-sections node needs a locally Noetherian normal scheme and a quasi-compact open: the spectrum of each chart ring is Noetherian and normal by step 6 and is affine, so these hypotheses hold. It gives a product of normal domains; since the chart ring itself is a nonzero domain, the product has one factor. I checked both integral-closure inclusions: finite implies integral for these explicit monic algebras, and an element integral over the target ring is integral over the larger source ring via the same polynomial, so normality puts it in the source ring. The normalization definition includes affine integral closures and their localization compatibility, which makes the chart identifications glue.

I checked B--E of delivery-errors against these files. The new node is self-contained and statement-only, with actual searches and explicit definition dependencies. No argument is transferred wholesale into a node restating a Fermat conclusion. Every non-elementary invocation is a node citation; every citation quote is verbatim. The elementary parts are the displayed coordinate, determinant, idempotent and integral-equation calculations inside steps that also cite the non-elementary tools. All nine steps are shorter than 2000 characters, and none hides a separate unstated comparison lemma. Off-unit statements are declared as generic tools in split_report.tool_uses for the maintainer's review.

Small-case checks: for the new cohomology node, d=1 and d=2 give H1=0, d=3 gives dimension 1; nonreduced forms such as A^2 are intentionally included, and F=0 and d=0 are excluded. For the item, ell=5 gives genus 6, while characteristic dividing ell would kill the determinant and is explicitly excluded. Characteristic 2 with ell odd causes no issue because both signs are units. I tested x=0, x=1, infinity, and the global nonemptiness point. The argument allows singular normal U and does not require U to be affine globally or smooth over its ground field. The primitive-root hypothesis is preserved without strengthening it.

## Unfinished work

The initial full delivery dry run passed at 6139836bcdd. A subsequent self-check made explicit the integrality and function field of the normalization target, and the final dry run is rerun on that complete version.

No clause of the item's natural-language split remains open. The general cohomology lemma is deliberately a new unsplit node for the next stage-1 worker. There is no Lean-proof completion claim. Validation and delivery are performed with the required server tools.

## Unfinished work and validation

The only intentionally unfinished work is the four new unsplit task proofs. The parent now contains their short assembly. I make no Lean-proof completion claim. The required final dry run and push follow this report; their output is the delivery evidence.
