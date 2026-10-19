# Worker report: def-trf-adic-system

## Files written

- `dag/nodes/sec-trace-formula/def-trf-adic-system.json`: existing definition item, marked `split`; no new nodes.
- `citations.json`: empty list because the item is a definition and has no proof steps.

## Attachments

None. The source search found no declaration tagged `(blueprint: def-trf-adic-system)`, no declaration named after the item, and no sorry-free declaration in `WeilConjectures/` stating this definition.

## WANTED

None.

## What I checked

I copied the item from the shared DAG and read the item source
`literature/blueprint/master/blueprint/sec-trace-formula/sk-prop-trace-adic/def-trf-adic-system.md`, the unit record
`dag/units/sk-prop-trace-adic.json`, and the chapter record
`dag/chapters/sec-trace-formula.json`. I also read the corresponding current blueprint search results in
`literature/blueprint/main-20261015/`. The imported statement agrees with the master node: it fixes the finite-field/coefficient conventions, defines an $A_\bullet$-system and its normalization, forms
$K_{\mathcal O_E}=R\!\varprojlim_n\operatorname{Res}_{n,X}K_n$, and names the compatible strict-Weil category and its reconstruction characterization.

The five statement dependencies are present and are the notions actually used by the definition: `def-trf-coefficient-conventions` supplies $A_n=A_{E,n}$ and the finite-level constructible category; `def-weil-finite-field-fiber` supplies the global field datum and coefficient rings; `def-weil-pbc-adic-coefficient-datum` supplies the tower, restriction, quotient transitions, and normalization convention; `def-weil-pbc-derived-inverse-limit` supplies the derived inverse-limit construction; and `def-weil-derived-complete-integral-detailed` supplies the target derived-complete bounded constructible integral category. I opened each cited node and verified that the statement uses the cited notion rather than material from its proof.

No proof step is required for a definition. Creating child nodes for the $A_\bullet$-system, normalization, realization, or strict-Weil category would only restate clauses of this item (the D1/D2 split errors), so I created no new nodes and left `stmt_deps` unchanged. The item is project-specific and is not a Mathlib leaf. As a diligence check I ran the required searches in the sandbox: LeanFinder for “normalized adic system of bounded constructible complexes with transition morphisms” (hits only generic `AdicCompletion`/adic-completion declarations, no match), Loogle for “CategoryTheory, DerivedCategory, inverse limit, perfect complex” (unavailable because the query identifier was unknown), and Mathlib grep for `normalized|derivedComplete|inverse.?limit|Res_` (no hits). These searches do not alter the conclusion that the item is a project definition built from its existing dependencies.

For edge cases, the definition permits $n=1$ and $j=n$ (where normalization is the identity reduction), allows the zero system and an empty $X$, and imposes no Weil structure on a bare normalized system: the strict Weil compatibility is required only for membership in
$\mathcal D^b_{ctf,\mathrm W,adic}$. The derived limit is taken after restriction to the completed coefficient sheaf, exactly as stated.

## Review by Q75

I re-read the item and every dependency against the blueprint source. The finite-field and coefficient hypotheses are supplied by the two convention nodes, the finite-level objects and transition/normalization data by the adic coefficient-datum node, and the target realization category and inverse-limit operation by the integral-category and derived-limit nodes. The statement does not use any stronger claim from those nodes: in particular, it does not assert realization or perfectness for an arbitrary tower beyond the reconstruction characterization already written in the source definition. I checked the transition direction $A_{n+1}\twoheadrightarrow A_n$, the derived tensor normalization for all $j\le n$, and the restriction `Res_{n,X}` in the displayed inverse limit. The small cases $n=1$, $j=n$, zero systems, and empty $X$ remain included. No statement correction, duplicate, source error, attachment, or missing source was found. The server-side `check_dag` preflight passed before this report was written.


## Second reading by Q75

This is an independent reading of the first worker's files. The earlier
sections are retained as the history of that worker's reading; the corrections
below supersede their verdict that no correction or dependency was needed.

- Item statement: checked the complete master node (order 2385), the complete current `main-20261015` node (order 2729), current `sk-prop-trace-adic/_section.md` (order 2728), and current `def-trf-strict-weil-complex.md` (order 2509); the two snapshots have the same definition text, and the system, normalization, realization notation and Weil-pair clauses are preserved with the type and dependency repairs below.
- Proof steps: there are none, because this item defines data and categories; no theorem is established by declaring the item split. `proof`, `proof_deps`, and `citations.json` remain empty. C1–C4 and E1/E5 were checked clause by clause rather than against nonexistent proof steps.
- New nodes: none; no elementary observation, clause of the item, or restatement of reconstruction was made into a child. B1–B7 introduce no new-node obligations.
- Coefficient and geometric clause: checked `def-trf-coefficient-conventions`, `def-weil-finite-field-fiber` and `def-weil-pbc-adic-coefficient-datum` verbatim; they supply respectively separated finite-type geometric fibers and finite constructible finite-Tor complexes, the finite-field and coefficient data, and the quotient coefficient sheaves. All primes, fields, rings, the scheme and positive indices are now explicit; verdict: faithful.
- Transition and normalization clause: checked `def-pc-sheaf-restrict-scalars`, `lem-sf-exact-functor-derived-triangulated`, `lem-pur-derived-change-of-rings`, and `def-sfb-derived-extend-restrict-adjunction` against their statements (and the latter's current blueprint source, order 1627). Restriction leaves underlying abelian sheaves unchanged, hence preserves kernels and cokernels; termwise restriction therefore descends. Derived scalar extension and its adjunction give the induced normalization maps. Their composite is the adjunct of the composite transition, so the displayed quotient cocycle has no independent choices. Verdict: types corrected without changing the intended data or adding uniformity hypotheses.
- Realization clause: checked `def-weil-integral-derived-restriction-of-scalars` and its exact target category, `def-weil-pbc-derived-inverse-limit` and its strict-derived-tower input, and `def-weil-derived-limit` against Stacks `derived.tex`, Tag 08TC, label `definition-derived-limit`, lines 10442ff. Also read Tag 015F, label `lemma-right-derived-exact-functor`, lines 5884ff for termwise exact functors. Verdict: the completed coefficient category and the object-with-Roos-triangle meaning are now explicit; a functor or strict lift is not supplied by a family in varying derived categories.
- Strict Weil category clause: checked `def-trf-strict-weil-complex` and `def-trf-scheme-frobenius`, and the compatibility equation in current `sk-prop-trace-adic`. The structure is an isomorphism for geometric Galois Frobenius, not an arbitrary coefficient morphism. Morphisms commute with transitions and with this structure, and composition is levelwise. Verdict: missing definition dependency and morphism data repaired.
- Reconstruction sentence: opened `lem-weil-pbc-reconstruction-uniform-tower`, `def-weil-pbc-bounded-constructible-tower`, `lem-weil-pbc-normalized-constructible-local-effectivity`, and `lem-weil-pbc-integral-stratified-perfect-characterization`. The first requires a strict derived tower with common local models; the effectivity statement additionally assumes a common interval; the characterization separately compares the integral categories. Verdict: these existing theorem interfaces carry the reconstruction assertions, which cannot simply be asserted as part of this definition.
- Small cases: on a point the free tower $A_n^r[0]$ with quotient transitions is normalized, including $r=0$; at $n=j=1$ normalization is the identity; $n=0$ is outside both source definitions. On the empty scheme every level and realization is zero. A tower supported on a geometric point not fixed by Frobenius is a valid bare normalized system but cannot be a strict Weil system. Verdict: all intended cases retained.
- Existing-node and source-Lean checks: searched the whole DAG for normalized systems, strict Weil complexes, restriction of scalars, derived limits and reconstruction, and read the reused nodes. Searched `dag/lean_names_upstream.json` and the read-only slopmaster2 `WeilConjectures/` and `Comparator/` trees by item id and the alternative names `AdicSystem`, `adicSystem`, `IsNormalizedTower`, and normalized-system/Weil vocabulary. `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Adic.lean:198` defines `AdicRealization.IsNormalizedTower`, but this is a predicate on a diagram over the discrete constant coefficient ring, not the completed-coefficient category of normalized strict Weil systems and its morphisms defined here. Its realization theorem at line 225 ends in `sorry`. Verdict: no exact closed attachment, and no duplicate node created.
- Independent Mathlib checks: ran LeanFinder for “inverse system in derived categories of quotient rings with scalar extension isomorphisms and Frobenius descent data” (8 hits: local cohomology and module adic completion), Loogle for `"DerivedCategory"` (12 hits: ambient category and general infrastructure), grep for `IsNormalizedTower|WeilComplex|AdicSystem|adicSystem|Frobenius.*[Tt]ower` (0 hits), and LeanSearch for “A category of compatible Frobenius equivariant normalized systems of constructible complexes over quotient rings” (8 hits: field/Witt Frobenius, monoidal normalization and Dold–Kan). Read the returned types; none defines this category. Results are recorded as returned in `searches.jsonl` and accurately summarized in the item's `mathlib_searches`. The first worker's Loogle query was an unknown-identifier error, not evidence of absence; the independent valid query replaces it for this decision.

### Statement/type correction and source issue

STATEMENT-DISPUTED: the imported text has no typed coefficient-transition
arrows, no definition of morphisms of its system category, and applies the
strict-tower notation of `def-weil-pbc-derived-inverse-limit` to a family
in varying derived categories without a supplied object of
$D(\operatorname{Tow}_{\mathcal O_E}(X))$. That is a domain mismatch with the
cited statement. The repaired definition uses the general object-only Roos
triangle definition (08TC), after restricting every level into the same
completed-coefficient derived category. It chooses no representative, functor,
or unjustified canonical isomorphism.

Normalization must refer to the maps induced by the transitions. For example,
the levels $K_n=A_n[0]$ admit abstract isomorphisms
$K_n\otimes^L_{A_n}A_j\cong K_j$ even when all adjacent transitions are zero.
For that zero-transition tower, $1-s=1$ and its Roos limit is zero, not
$\mathcal O_E$. Thus unrelated isomorphisms cannot suffice. The correction
spells out the transition-induced maps and their composite convention, which
is the intent of the source and of the downstream coefficient-morphism node.

The final source sentence is a reconstruction assertion, not definitional
data. It is separated from the definition and remains assigned to the
existing reconstruction/effectivity/characterization nodes named above;
there is no new node and no discarded theorem obligation. If “the resulting
realizations are the ... complexes” is read as an identification with *all*
underlying integral complexes, forgetting Weil structures, that reading is
false: take $X_0=\mathbf A^1_{\mathbf F_q}$ and a geometric closed point
$y\in\mathbf F_{q^2}\setminus\mathbf F_q$. The integral skyscraper
$i_*\mathcal O_E$ at $y$ has bounded constructible finite-Tor reductions
$i_*A_n$, but their support moves under $g_\gamma$, so they admit no
isomorphism $Lg_\gamma^*i_*A_n\cong i_*A_n$. Such an object cannot come from
a strict Weil system. The actual definitional category is a category of
compatible pairs; the separate reconstruction theorem concerns underlying
objects under its own hypotheses.

No extra common-bound hypothesis was imposed on normalized systems. In this
DVR setting one must not justify such an addition by an alleged counterexample
with unbounded perfect levels: reduction to the field $A_1$ fixes a range,
and filtering an $A_n$-module by powers of $\varpi_E$ reduces its Tor test to
$A_1$-modules. The same observation is written out in the existing
`sk-thm-trace-transport` proof step 1. Over a point, Stacks
`more-algebra.tex`, Tag 09AW, label `lemma-Rlim-perfect-gives-complete`,
lines 28447ff explicitly reconstructs a normalized perfect tower without
adding uniformity. I read that statement and the preceding perfect-limit
lemma; neither was misapplied as a sheaf reconstruction theorem here.

The five current citers were opened: `prop-trf-adic-coefficient-morphism-systems`
uses the bare system and induced normalization; `rem-trf-classical-framework`
uses the ordinary pair/category convention; the integral coefficient-morphism
trace theorem and the $E$ trace theorem use the reduction-tower special case;
`sk-thm-trace-transport` uses levelwise finite-Tor objects and compatible Weil
pairs. These clauses remain unchanged in meaning. None uses an automatic
equivalence with all integral complexes from this definition. No citer was
edited.

Changes: explicitly introduced the geometry and coefficients; typed the
quotient restrictions and transitions; made normalization transition-induced;
defined levelwise morphisms; added the actual strict-Weil, restriction,
change-of-rings and adjunction dependencies; replaced the strict-tower-only
limit citation by the general Roos definition; separated the reconstruction
assertion onto existing theorem interfaces; removed the now-unused integral
category dependency; recorded independent successful searches and corrected
the split summary. The first worker's report and review remain in place.

Maintainer metadata request: preserve the reconstruction cross-reference as a forward pointer to `lem-weil-pbc-reconstruction-uniform-tower` and `lem-weil-pbc-integral-stratified-perfect-characterization`, under their stated hypotheses. `pointers` is maintainer-owned, so this delivery does not edit it or introduce a dependency cycle.
