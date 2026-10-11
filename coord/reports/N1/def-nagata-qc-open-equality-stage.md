## Worker report

Repair of R-qoe. The module defines `AlgebraicGeometry.nagataQCOpenEqualityStage`
from its geometric setting, not from free witness-stage families. The full
chartwise coefficient/identity construction was not completed. Instead this is
the explicit statement-correction proposal authorized by the final sentence of
the return, using the proved geometric theorem for Stacks 01Z4(2).
It contains no `sorry`, no witness structure with unconstrained Prop fields,
and no private copy of any dependency notion. No theorem is proved.

Hypothesis-by-hypothesis and clause-by-clause for the corrected node:

- Nonempty directed preorder: `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`.
- Inverse system and its given limit: `D : Iᵒᵖ ⥤ Scheme.{u}`, `c : Cone D`,
  `hc : IsLimit c`. The shared universe is the recorded scheme-limit convention.
- Affine transitions: the instance quantifying `IsAffineHom (D.map f)`.
- Base stage, qcqs base-changed scheme, and structure map: `i₀ : I`,
  `{Y₀ : Scheme.{u}}`, `p : Y₀ ⟶ D.obj (Opposite.op i₀)`,
  `[CompactSpace Y₀] [QuasiSeparatedSpace Y₀]`.
- Two compact opens: `W₁ W₂ : Y₀.Opens`, `hW₁`, `hW₂` explicitly assert
  `IsCompact` on their underlying sets.
- Equality in the actual limit base change: `hEq` is equality of their inverse
  images under `pullback.fst p (c.π.app (Opposite.op i₀))`. There is no free
  replacement Y or free map q.
- The recorded base-changed system/cone are `B := baseChangeDiagram D p` and
  `b := baseChangeCone D c p`. `isLimitBaseChangeCone D c p hc` supplies the
  limit proof; its transition affineness is the proved recorded instance.
- `j₀ := Over.mk (𝟙 (Opposite.op i₀))` is the base object of the tail;
  `f₀ := pullback.fst p (D.map j₀.hom)` is its canonical projection to Y₀.
  This is an isomorphism because D.map(identity) is an isomorphism; the
  quasi-compact instance and `QuasiCompact.isCompact_preimage` transport both
  compactness proofs to B(j₀).
- `e` is the proved `exists_map_preimage_eq_map_preimage` applied to B, b,
  their IsLimit proof, the two preimage opens, compactness and hEq (rewritten
  by the pullback projection identities). It supplies an object j, a map
  j → j₀, and equality there. Thus its stage τ is ≥ i₀ and tied to the geometry.
- `(Classical.choose e).left.unop` selects τ from that proved result. It never
  chooses from `CommRingCat.exists_finite_data_stage`, which still has sorry.
- `F = {i₀, τ}` and the output is `directedFiniteUpperBound i₀ d r F`.
  d and r are exactly the recorded upper-bound definition's explicit choice
  data. Its order-bound property is a hypothesis of the separate eventual
  lemma, not proof data this definition consumes.
- Eventual equality is not proved here. The selected witness gives equality
  at τ; pulling it back preserves equality at every later stage. With valid d,
  the recorded upper-bound theorem makes the returned stage ≥ τ and ≥ i₀.
  There are no output affine covers, coefficients, powers, or ν families in
  the corrected statement.

Dependency declarations used:

- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `AlgebraicGeometry.baseChangeDiagram`, `baseChangeCone`,
  `isLimitBaseChangeCone`, and the affine-transition instance for base change.
  Read full signatures, docstrings and bodies at lines 2181–2256.
- `Sheaf.Order.DirectedFiniteUpperBound`: `directedFiniteUpperBound`, whose
  full module and bound theorem were read; it is used without a private copy.
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `AlgebraicGeometry.exists_map_preimage_eq_map_preimage`, read at lines 294–307,
  including its proved body (two inclusions followed by a cofiltered cospan).
- `QuasiCompact.isCompact_preimage` transports the compact opens along f₀.

The old dependencies were inspected: `CommRingCat.exists_finite_data_stage`
(`Sheaf.RingTheory.FilteredColimitFiniteData`, sorry),
`AlgebraicGeometry.exists_limit_affine_transition`
(`Sheaf.AlgebraicGeometry.LimitAffineTransition`, sorry), and the Mathlib
`nonempty_isColimit_Γ_mapCocone`, `exists_appTop_π_eq_of_isLimit`, and
`exists_appTop_map_eq_zero_of_isLimit` (proved). They are not used by the new
selection procedure and their node ids are removed only under the recorded
statement correction.

Edge cases checked: I cannot be empty because a base stage is fixed. Empty
Y₀ and empty opens are allowed; no nonempty-scheme hypothesis is introduced.
Identical opens, zero-ring affine charts, and equality of two empty preimages
on an empty limit are covered by the proved theorem. If τ = i₀ the finset
removes the duplicate. No characteristic restriction or positivity condition
is introduced. All universes and variables are explicitly bound. The qcqs
instances retain the original geometric setting, although the chosen Mathlib
result is more general and does not require them.

Searches in this repair:

- msearch LeanFinder: “two quasi compact opens equal inverse images in inverse
  limit schemes equal finite stage”; 8 hits, first the exact existence theorem
  `AlgebraicGeometry.exists_map_preimage_eq_map_preimage`, also the section
  lift and equality lemmas. No selected-stage definition was found.
- msearch Loogle: `exists_map_preimage_eq_map_preimage`; 0 hits (unqualified
  identifier unknown to service).
- msearch grep: `exists_map_preimage_eq_map_preimage` in AlgebraicGeometry;
  one hit, Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean:294.
- rg of WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for the
  node id and selected declaration name: no existing selected definition.
  The upstream base-change construction and M1's `nagataSeparatedStage`
  were read rather than copied.

Sources: read the original blueprint node order 349 and its unit _section.md
on the server by read-only ssh (the literature is absent from this machine).
Read [Stacks Tag 01Z4(2)](https://stacks.math.columbia.edu/tag/01Z4) online:
the source supplies equality at some later stage; later pullbacks preserve it.
The original blueprint specifies chartwise radical witnesses, so this delivery
is explicitly a proposed change of selection procedure, not an assertion that
the original chartwise construction has been formalized. The unit's absolute
approximation/descent proposition is unchanged.

Return points:

1. All geometry, limit, affine transitions, qcqs instances, compact opens and
   equal inverse images now occur as the actual binders and choice input.
2. μ, ν, K and J are gone; the only selected stage comes from the proved
   geometric theorem and its finite-set upper bound is constructed internally.
3. Citers apply the function directly to their geometric setting and compact
   opens. No coefficient/witness hypotheses must be supplied. The old
   chartwise-data eventual lemma is explicitly flagged below for review.

Validation: final module compiled on the server with no errors or warnings.
Dry-run result recorded after running deliver2.py --no-push. Independent second
reading is left to the dispatcher; the previous version's second reading has
been removed because it approved the returned data-only wrapper.

## Statement corrected

This is the alternative proposal explicitly requested in R-qoe when the full
chartwise construction is out of reach: choose a genuine equality stage from
the proved Mathlib result for Stacks 01Z4(2), then fold the recorded finite bound
over the base and that stage. The old geometric construction is not false,
but its arbitrary choices were unspecified and the old implementation did not
perform them. We replace that selection procedure transparently, retaining the
geometric hypotheses and intended eventual equality. No unit statement changes.

The old statement, verbatim:

Fix the base-changed system of [def-nagata-basechanged-system] with $\lambda_0\in I$. Assume that $I$ is directed, $S=\varprojlim_\lambda S_\lambda$, every transition $S_\mu\to S_\lambda$ is affine, and $Y_{\lambda_0}$ is quasi-compact and quasi-separated (as a scheme; this holds when $S_{\lambda_0}$ is quasi-compact and quasi-separated and $Y_{\lambda_0}\to S_{\lambda_0}$ is quasi-compact and quasi-separated, e.g. $S_{\lambda_0}$ of finite type over $\mathbf Z$). Let $W_{1,\lambda_0},W_{2,\lambda_0}\subseteq Y_{\lambda_0}$ be quasi-compact opens whose inverse images in $Y$ agree. Choose a finite affine cover $Y_{\lambda_0}=\bigcup_k U_k$ and write $U_{k,\lambda}$ for its inverse image in $Y_\lambda$ and $U_k^\infty$ for its inverse image in $Y$. Using quasi-separatedness, choose finite presentations $W_{i,\lambda_0}\cap U_k=\bigcup_jD(f_{ijk})$ with $f_{ijk}\in\Gamma(U_k,\mathcal O)$, and denote their pullbacks to $\Gamma(U_k^\infty,\mathcal O)$ by $\bar f_{ijk}$. Equality of the two inverse-image opens gives the radical containments $\bar f_{1jk}\in\sqrt{(\bar f_{2\ell k})_\ell}$ and $\bar f_{2jk}\in\sqrt{(\bar f_{1\ell k})_\ell}$ in the limit ring. Choose witnessing identities $\bar f_{1jk}^{n_{1jk}}=\sum_\ell a_{1jk\ell}\bar f_{2\ell k}$ and $\bar f_{2jk}^{n_{2jk}}=\sum_\ell a_{2jk\ell}\bar f_{1\ell k}$, with finitely many coefficients. By [lem-weil-pbc-limit-affine-transition] and [lem-weil-pbc-limit-global-sections-colimit] (Stacks Tags 01YW/01Z0), $\Gamma(U_k^\infty,\mathcal O)\cong\varinjlim_{\lambda\geq\lambda_0}\Gamma(U_{k,\lambda},\mathcal O)$. Write $f_{ijk,\lambda}\in\Gamma(U_{k,\lambda},\mathcal O)$ for the pullback of $f_{ijk}$ (so its image in $\Gamma(U_k^\infty,\mathcal O)$ is $\bar f_{ijk}$). For each $k$, apply [lemma-nagata-filtered-colimit-finite-data] to the directed system $(\Gamma(U_{k,\lambda},\mathcal O))_{\lambda\geq\lambda_0}$ and the finitely many coefficients $a_{ijk\ell}$ (no equalities) to select a stage $\mu_k\geq\lambda_0$ and lifts $a_{ijk\ell,\mu_k}\in\Gamma(U_{k,\mu_k},\mathcal O)$. For each witnessing identity, the element $f_{1jk,\mu_k}^{n_{1jk}}-\sum_\ell a_{1jk\ell,\mu_k}f_{2\ell k,\mu_k}$ (resp. $f_{2jk,\mu_k}^{n_{2jk}}-\sum_\ell a_{2jk\ell,\mu_k}f_{1\ell k,\mu_k}$) maps to $0$ in $\Gamma(U_k^\infty,\mathcal O)$, so by the injectivity clause of [lem-weil-pbc-limit-global-sections-colimit] select a stage $\nu\geq\mu_k$ at which its image in $\Gamma(U_{k,\nu},\mathcal O)$ is $0$, i.e. the identity holds there with the actual pullbacks $f_{ijk,\nu}$ and the transported coefficients. Let $F$ be the finite set consisting of $\lambda_0$, the $\mu_k$ and these finitely many witness stages $\nu$, and define $\lambda_{W_1=W_2}:=u(F)$ using [def-nagata-directed-finite-upper-bound]. (At any $\lambda$ above every element of $F$ the transported identities give $D(f_{1jk,\lambda})\subseteq\bigcup_\ell D(f_{2\ell k,\lambda})$ and conversely in $U_{k,\lambda}$, which is what the eventual-equality lemma for these opens uses.)

The new statement, verbatim:

Let $I$ be a nonempty directed preorder, let $D:I^{\mathrm{op}}\to\mathrm{Sch}$ be an inverse system with affine transitions, and let $c$ be a limit cone with vertex $S$ and projections $p_\lambda$. Fix $\lambda_0\in I$, a quasi-compact and quasi-separated scheme $Y_{\lambda_0}$, and a morphism $p:Y_{\lambda_0}\to S_{\lambda_0}$. Form the base-changed diagram $B$ and cone $b$ of [def-nagata-basechanged-system]; thus $B$ is indexed by $\operatorname{Over}(\lambda_0)$ in $I^{\mathrm{op}}$, its object at $j=(\lambda\to\lambda_0)$ is $Y_\lambda=Y_{\lambda_0}\times_{S_{\lambda_0}}S_\lambda$, and its cone vertex is $Y=Y_{\lambda_0}\times_{S_{\lambda_0}}S$. Let $W_1,W_2\subseteq Y_{\lambda_0}$ be quasi-compact opens whose inverse images under $Y\to Y_{\lambda_0}$ agree. Put $j_0=(\lambda_0,\mathrm{id})$ and $f_0:B(j_0)\to Y_{\lambda_0}$ the first pullback projection. Apply the proved compact-open equality descent theorem (Stacks Tag 01Z4(2), Mathlib `AlgebraicGeometry.exists_map_preimage_eq_map_preimage`) to the limit cone $b$, the compact opens $f_0^{-1}(W_1),f_0^{-1}(W_2)$, and their equal inverse images. Select one resulting witness $j$ with a morphism $j\to j_0$ and equality of the transported opens, using classical choice on this proved existence result. Write $\tau$ for the underlying index of $j$, so $\tau\geq\lambda_0$. Fix the base point $i_\varnothing=\lambda_0$, selected binary upper bounds $d$, and auxiliary linear order $r$ of [def-nagata-directed-finite-upper-bound]. Set $F=\{\lambda_0,\tau\}$ and define $\lambda_{W_1=W_2}:=\operatorname{directedFiniteUpperBound}(\lambda_0,d,r,F)$. The property that the two opens agree at this stage and every later stage is left to the eventual-equality lemma; the upper-bound property of $d$ is used in that lemma as in the recorded upper-bound definition. No chartwise coefficient or radical-identity data are outputs of this definition.

Every citer (none edited):

- `def-nagata-morphism-descent`: holds true. Uses the equality stage only to make two compact opens equal at all later stages; the new selection supports that use.
- `def-nagata-morphism-equality-stage`: holds true. The same geometric inputs yield an index above the base; subsequent eventual open equality is unchanged.
- `def-nagata-relative-gluing-valid-stage`: holds true. Uses only equality stages and transport of open equalities to a common upper bound.
- `lemma-nagata-qc-open-eq-eventually`: holds false. The eventual-equality conclusion remains true, but its statement imports chart presentations and power identities that this corrected definition does not construct; its chartwise proof must instead use the chosen equality witness and transport.

The eventual lemma’s mathematical conclusion survives, but its old statement
and proof import auxiliary chart data absent from this corrected definition.
That is why it is marked holds:false rather than silently treated as compatible.


## Second reading by N1

I did not write this module. I read the corrected statement first, then the
Lean, against Stacks `limits.tex`, `lemma-descend-opens` (Tag 01Z4), lines
553–623, and its ambient `situation-descent`, lines 384–395, obtained by
read-only ssh from the server. I also read the original blueprint definition
(order 349) and its unit `_section.md` (order 326). The original definition
specifies chartwise radical witnesses; this delivery instead proposes the
geometric choice procedure explicitly suggested by return R-qoe. It does not
claim to implement that original procedure. The corrected procedure chooses
exactly the equality witness asserted in 01Z4(2), retaining the original
geometric inputs and the finite-bound operation. The unit asserts absolute
approximation and descent of separated finitely presented schemes; it does
not specify this intermediate choice rule, so its statement is unchanged.

Object/hypothesis/conclusion checklist for the corrected node:

1. Nonempty directed preorder I: `{I : Type u} [Preorder I]
   [IsDirected I (· ≤ ·)] [Nonempty I]`. Matches; a poset is included, and
   the preorder formulation is the approved scheme-limit convention.
2. Inverse system, limit S, projections and affine transitions:
   `D : Iᵒᵖ ⥤ Scheme.{u}`, `c : Cone D`, `hc : IsLimit c`, and
   `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]`.
   Matches: S is c.pt and its projections are c.π.app; no arbitrary
   replacement object or unconnected comparison morphism occurs.
3. Base stage and scheme over it: `i₀ : I`, `{Y₀ : Scheme.{u}}`,
   `p : Y₀ ⟶ D.obj (Opposite.op i₀)`, `[CompactSpace Y₀]`
   and `[QuasiSeparatedSpace Y₀]`. Matches absolute qcqs, not just
   relative qcqs. Stacks assumes every scheme of its system is qcqs;
   here each B(j) is affine over qcqs Y₀ and hence qcqs. Thus the source's
   ambient hypotheses hold on the system to which the theorem is applied,
   without imposing qcqs on unrelated S stages.
4. Base-changed system and limit: body `B := baseChangeDiagram D p` and
   `b := baseChangeCone D c p`, with `isLimitBaseChangeCone D c p hc`.
   Matches def-nagata-basechanged-system's recorded declarations. I opened
   their signatures and bodies in the upstream AffineTransitionLimit file,
   lines 2175–2256. Over(op i₀) is the tail: j.hom represents i₀ ≤ j.left.unop.
   Objects are pullback p (D.map j.hom); maps and cone legs are pullback.map
   with identity on Y₀. Their affine-transition instance is proved upstream.
5. Quasi-compact opens and equality at Y: `W₁ W₂ : Y₀.Opens`, `hW₁`,
   `hW₂ : IsCompact ...`, and `hEq` under the actual first projection
   `pullback.fst p (c.π.app (Opposite.op i₀))`. Matches every clause.
6. Initial tail object and compact opens there: body `j₀ := Over.mk (𝟙 ...)`,
   `f₀ := pullback.fst p (D.map j₀.hom)`, and opens `f₀ ⁻¹ᵁ W₁`,
   `f₀ ⁻¹ᵁ W₂`. Matches. D.map(identity) is an isomorphism, hence f₀ is
   quasi-compact; `QuasiCompact.isCompact_preimage` supplies compactness.
   The `simpa` proof transports hEq using the existing pullback projection
   identities and comp_preimage; it asserts no new geometric theorem.
7. Genuine equality witness j and its stage τ: body `e :=
   exists_map_preimage_eq_map_preimage B b ...` and
   `(Classical.choose e).left.unop`. Matches. I read Mathlib's theorem at
   lines 294–307, including its proved body: two inclusion witnesses and
   a cofiltered cospan give equality. Its existential includes j → j₀,
   so τ ≥ i₀. The input proof refers to the specified geometry. There is
   no choice from a sorry finite-data theorem and no free witness-stage input.
8. Base point, binary choice data and auxiliary order: `i₀`, `d : I → I → I`,
   `r : LinearOrder I`. Matches the recorded DirectedFiniteUpperBound module,
   which I read in full: the definition sorts F by r and folds d from i₀.
   As explicitly stated in the corrected node, validity of d as an upper
   bound is deferred to the eventual lemma, whose theorem uses
   `hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j`. This definition returns an index
   for arbitrary d; eventual equality is asserted only with valid bound data.
9. Finite witness set and selected index: body
   `directedFiniteUpperBound i₀ d r {i₀, (Classical.choose e).left.unop}`,
   result `: I`. Exactly F = {i₀, τ} and the specified fold. No charts,
   coefficients, exponents or witness identities are promised by the corrected
   node. No eventual-equality theorem is proved in this stage-2 module.

Edge cases: fixing i₀ already excludes empty I, so Nonempty adds no excluded
case. Empty Y₀, empty limit, empty opens, identical opens and zero-ring affine
charts remain permitted. An empty limit need not give equality at i₀, but the
proved existence theorem still supplies a later witness. If τ = i₀ the finset
has one element; the recorded fold handles duplicates. No characteristic,
field, Noetherian, positive-dimension or nonempty-scheme assumption is added.
The shared universe u matches the recorded base-change construction and the
project's scheme-limit convention; no independent smaller universe can make
an existential or test-family hypothesis vacuous. All binders are explicit.

Independent one-definition searches (different phrasing from the worker):

- msearch LeanFinder, “select an index where two compact open subsets have
  equal pullbacks along an inverse system of schemes”: 8 hits. Exact existence
  theorem exists_map_preimage_eq_map_preimage and the corresponding inclusion
  and open-descent theorems; no definition of this selected finite-bound index.
- msearch Loogle, `AlgebraicGeometry.exists_map_preimage_eq_map_preimage`:
  1 hit, the same Mathlib theorem, whose full local declaration I opened.
- rg on Mathlib AlgebraicGeometry, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for EqualityStage, equalityStage,
  preimage_eq_map_preimage, descend.*opens and opens.*descend. Mathlib has
  the existence theorem; upstream has users of it. The project's spectral
  open descent and NagataQCOpenDescent are different notions. I opened the
  latter: it constructs a descended open from chart/lift data, not an equality
  stage for two given opens. No existing selected-index definition was found.

Correction/citers: I opened lemma-nagata-qc-open-eq-eventually and
 def-nagata-morphism-equality-stage in full. The former explicitly asks for
chart presentations and identities constructed by this node, so holds:false
is correct: its statement and proof need revision before reuse. The latter
uses only the selected equality index for the given pair of inverse-image
opens and then does its own affine/ring-map work; holds:true is correct.
The four citer IDs in statement_change are exactly the nodes with this item
in stmt_deps or proof_deps (checked by rg). Citers are not edited. The worker's
other two holds:true verdicts concern only the equality-stage interface;
use of the broken eventual lemma remains visibly pending through holds:false.

No new definition nodes or dependency modules are delivered. Both recorded
notions are used, without private copies. The module has no sorry, axiom,
new theorem, local notation, local instance or hidden/unbound variable.
The definition's only proof block is routine transport of hEq by existing
identities, not postponed data or a new asserted statement. The node's proof
list is empty because this is a definition. The declaration docstring names
01Z4(2) and the blueprint marker.

Mismatch repaired: the module header lacked the literal
`(blueprint: def-nagata-qc-open-equality-stage)` marker required by H8.
I added it. The definition, its signature, and the correction record were
already right and are unchanged; lean.statement remains verbatim the signature
from `def` through the result type. Validation results are recorded below.

Validation: scompile.py compiled the sole module cleanly on the server in
1.9 seconds (exit 0, no warnings). deliver2.py --no-push printed OK: the
second-reading delivery passes preflight and compilation.
