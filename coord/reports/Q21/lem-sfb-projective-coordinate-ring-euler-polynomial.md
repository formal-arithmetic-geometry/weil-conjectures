## Worker report

Stage 2, Q21, 2026-10-22. This is a statement delivery, not a re-split of Q22's
reviewed stage-1 proof. The live node has status split and no lean binding or
reviewed_lean. Its six proof steps are retained verbatim. The statement now specifies the Proj twist
on the absolute ambient model, as required by the independent return. The previous
worker's conclusion that the stage-1 landing made this assignment stale was mistaken.

The main module is Sheaf.AlgebraicGeometry.ProjectiveCoordinateRingEulerPolynomial.
It states existence of a common eventual bound and rational polynomial, the equality
of coordinate dimensions with the Euler characteristic of the pulled-back twist,
vanishing for empty Proj, and independence under isomorphisms of embedded closed
subschemes. Both theorem proofs are sorry. The auxiliary quotient-grading module has
one further named sorry, existence and uniqueness of the induced grading. No theorem
proof is supplied in this stage.

Clause-by-clause correspondence:

| Node clause or hypothesis | Lean rendering |
| --- | --- |
| k a field | Explicit section variable `{k : Type u} [Field k]`; autoImplicit is false. |
| N >= 0 and N+1 homogeneous variables | `{N : ℕ}` and `ULift.{u} (Fin (N + 1))`. The lift preserves the finite set of variables and accommodates any coefficient universe. |
| B=k[z_0,...,z_N], total-degree grading | `MvPolynomial (ULift.{u} (Fin (N + 1))) k` and `MvPolynomial.homogeneousSubmodule`; the existing `MvPolynomial.gradedAlgebra` is activated locally in each delivered module; it does not alter the global instance environment. |
| J a homogeneous ideal | `J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule ... k)`. |
| A=B/J with its induced grading | The actual `MvPolynomial ... k ⧸ J.toIdeal`; `coordinateQuotientPiece J m` is the image of the degree-m polynomial submodule under `Ideal.Quotient.mkₐ`, and `coordinateQuotientGrading J` supplies the uniquely determined direct-sum decomposition. |
| Z=Proj(A) | `Proj (coordinateQuotientPiece J)`. |
| The indicated embedding into the fixed Proj(B) | `coordinateQuotientImmersion J` is `Proj.map` of `coordinateQuotientGradedMap J`, whose underlying ring map is exactly `Ideal.Quotient.mk J.toIdeal`. Its irrelevant-ideal condition is obtained from surjectivity of this quotient. `Proj.isClosedImmersion_map` already proves that this actual map is a closed immersion; this is not an additional assumption. |
| O_Z(m)=i^*O_Proj(B)(m) | Inside `coordinateQuotientEuler`, `(Scheme.Modules.tensorPullback (coordinateQuotientImmersion J)).obj (Proj.twist (MvPolynomial.homogeneousSubmodule ... k) m)`. The twist is on the absolute Proj model actually named by the node. |
| Euler characteristic over k | The existing `Scheme.Modules.eulerChar`, with `OverClass.ofHom (coordinateQuotientImmersion J ≫ Proj.projectiveSpaceOverAffineToSpec ... k)`. Thus the k-action is the canonical structure map, not an arbitrary Over instance. |
| There is m_0 >= 0, with dim A_m = chi for every m >= m_0 | `∃ (m₀ : ℕ) ...`, then `∀ m : ℕ, m₀ ≤ m → (Module.finrank k (coordinateQuotientPiece J m) : ℤ) = coordinateQuotientEuler J m`. |
| The polynomial eventually equal to the dimensions | In the same existential, `P : Polynomial ℚ` and `P.eval (m : ℚ) = (Module.finrank k (coordinateQuotientPiece J m) : ℚ)` above the common bound. |
| Polynomial depends only on the closed subscheme, not its defining ideal | `coordinateQuotient_polynomial_independent`: two ideals J,K; an isomorphism `e` of their Proj schemes with `e.hom ≫ coordinateQuotientImmersion K = coordinateQuotientImmersion J`; and arbitrary polynomials P,Q eventually equal to the respective coordinate dimensions imply `P = Q`. This is the invariant of the embedded closed subscheme, exactly as the node's sixth proof step specifies. |
| J need not be saturated | Neither theorem nor any definition has a saturation condition, nor replaces J by a saturation. |
| Z may be empty, and both sides vanish eventually | No nonemptiness binder. The main conclusion explicitly includes `IsEmpty (Proj ...) → P = 0 ∧ ∀ m, m₀ ≤ m → Module.finrank ... = 0 ∧ coordinateQuotientEuler J m = 0`. |

Dependency declarations read and used:

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-pc-proj: Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme,
  `AlgebraicGeometry.Proj` and `projIsoSpec`; the canonical quotient morphism uses
  Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor, `Proj.map`.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `IsClosedImmersion`; the already proved quotient-map criterion is
  `Proj.isClosedImmersion_map` in
  WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor.
- def-pc-projective-space-twist: the base binding remains unchanged:
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist, `ProjectiveSpace.twist`,
  on the relative projective-space model. Its module is publicly imported.
- def-weil-pbc-proj-twisting-sheaf: the existing binding
  WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules, `Proj.twist`,
  is specialized to the polynomial grading on the stated ambient Proj(B). Its
  locally homogeneous fractions give the degree-one-chart trivializations.
- def-pc-module-pullback: Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
  publicly imports the actual `Scheme.Modules.tensorPullback` of
  WeilConjectures.AlgebraicGeometry.TensorPullback. The object is inverse image
  followed by extension of scalars and sheafification, not a chosen adjoint.
- def-pc-euler-characteristic:
  WeilConjectures.AlgebraicGeometry.Cohomology.Defs, `Scheme.Modules.eulerChar`:
  its existing integer finsum of `(-1)^q * finrankH k q` is used unchanged.
- def-sfb-coordinate-quotient-grading: the new module described below.

Proof imports are plain imports of the recorded
Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing and
Sheaf.RingTheory.StandardGradedHilbertFunction. The section-tail prerequisite
lem-sfb-finite-graded-module-section-tail currently has no Lean record, so no
nonexistent import is inserted. It is used only in the postponed natural-language
proof, not to define any object or to type the statement. All already stated
proof-dependency modules are imported publicly when they also supply statement
objects. The Proj twist uses the recorded def-weil-pbc-proj-twisting-sheaf module.

Sources opened: Stacks coherent.tex, lemma-recover-tail-graded-module (0AG7),
lemma-coherent-projective (01YS), varieties.tex lemma-hilbert-polynomial-H0 (08AE),
and algebra.tex section-graded (00JL), especially its graded quotient paragraph.
The quotient-Proj closed immersion is the existing theorem in the upstream
Mathlib extension, agreeing with constructions.tex
lemma-surjective-graded-rings-map-proj. The main docstring follows all six existing
proof steps, including the transition-function identification of the actual twist.

Edge cases checked mathematically before the statement:

- N=0: there is one homogeneous variable. J=0 gives the point and constant Hilbert
  polynomial 1. No positive-dimensional or two-variable hypothesis was added.
- J=B: the quotient ring and every displayed piece are zero. Graded algebra, Proj,
  tensor pullback and eulerChar all accept this case; no Nontrivial quotient assumption.
- J=(z_0^r) for N=0 and r>0: Proj is empty although finitely many graded pieces survive.
  The statement only asserts their vanishing above a bound, not in every degree.
- Unsaturated J=(x^2,xy) in k[x,y], compared with its saturation (x): the finite low-degree
  discrepancy is permitted, and both eventual polynomials are 1. No finite-degree
  equality between the two coordinate rings is asserted.
- J=0 for general N: usual projective-space polynomial and twists.
- All field characteristics and arbitrary universe u are allowed; no CharZero,
  algebraic closure, smoothness, reducedness or nonemptiness hypothesis occurs.

Searches made for an existing statement:

- msearch.py leanfinder, "The homogeneous coordinate ring Hilbert polynomial equals
  the Euler characteristic of twists on the projective scheme": returned
  Polynomial.hilbertPoly and related purely polynomial identities, and Proj itself;
  no comparison with scheme Euler characteristics.
- msearch.py loogle, "AlgebraicGeometry.Proj, Module.finrank": zero hits.
- msearch.py grep, "hilbertPoly|eulerChar", AlgebraicGeometry: zero hits.
- rg of WeilConjectures and Sheaf for coordinate/Hilbert/Euler combinations: found
  the Euler-characteristic definition, Hilbert-function results and the citation in
  ProjectiveCurveIsomGraphs; no existing declaration of this comparison.
- The exact node id has no declaration in WeilConjectures. The library's unrelated
  graded kernel and filtration quotients are not homogeneous ring quotient gradings.

The statement correction is recorded below; there is no STATEMENT-DISPUTED issue. The earlier
stage-1 split and its review are preserved. Every variable and universe is explicitly
bound; both delivered modules have `set_option autoImplicit false`. All delivered
files were checked separately through scompile.py in dependency order, clean except
for the expected sorry declarations. No global or local direct Lean build was run.

## New nodes

`def-sfb-coordinate-quotient-grading`, in the item's chapter and unit, owns
Sheaf.RingTheory.CoordinateQuotientGrading. It defines the actual homogeneous images
in the actual polynomial quotient and equips them with their unique induced grading.
It cites the field, multivariate-polynomial-ring and standard-graded-algebra nodes.
The source is Stacks Algebra, Tag 00JL, section-graded, the paragraph introducing
graded ideals and graded quotient rings. Its auxiliary theorem states existence AND
uniqueness with the projection formula, rather than a bare Nonempty choice. The
submodules and quotient ring have fully explicit data. The decomposition is uniquely
determined as the inverse of their fixed summation map. This meets AGENTS §5's
permission to postpone an inverse/universal-property proof for a uniquely determined
object; it is not arbitrary data from an uncharacterized existence theorem.

For this notion, msearch.py LeanSearch queried "The quotient of a graded algebra by a
homogeneous ideal has the induced grading whose degree components are images of the
original components". Its eight results give only the ordinary quotient-algebra
instance and homogeneous ideal operations. Loogle "GradedAlgebra, Ideal.Quotient.mk"
returned zero hits. The recorded Mathlib grep for
"quotientGrading|gradedQuotient|quotient.*GradedAlgebra|GradedAlgebra.*quotient" in
RingTheory returned zero hits. The same local rg in WeilConjectures and Sheaf found
only unrelated sheaf/tensor-graded action records. A scan of definition-node
statements for homogeneous ideals and quotient gradings found no such notion;
`tools/blueprint_refs.py search 'homogeneous quotient grading'` returned zero nodes.
The ancestor command reported blueprint.from.node=None, which is retained exactly.
Raw search records are embedded in the new node's mathlib_searches.

## Statement corrected

The returned immutable head was 1f29bf1379b0. H13/H4: the previous packet changed
`def-pc-projective-space-twist` from `ProjectiveSpace.twist` to `Proj.twist`, although
these are deliberately distinct records (lead decision 2026-10-11). That dependency
node is removed from this packet, preserving its landed record exactly.

Old statement (verbatim):

Let $k$ be a field [def-weil-field], let $N\ge0$, let $B=k[z_0,\ldots,z_N]$ be graded by total degree, and let $J\subseteq B$ be a homogeneous ideal. Put $A=B/J=\bigoplus_{m\ge0}A_m$ with the induced grading, and let $i:Z=\operatorname{Proj}(A)\hookrightarrow\mathbf P^N_k=\operatorname{Proj}(B)$ be the closed subscheme defined by $J$ [def-pc-proj, def-weil-closed-immersion]. Put $\mathcal O_Z(m)=i^*\mathcal O_{\mathbf P^N_k}(m)$ [def-pc-projective-space-twist, def-pc-module-pullback]. Then there is $m_0\ge0$ such that $\dim_kA_m=\chi(Z,\mathcal O_Z(m))$ [def-pc-euler-characteristic] for every $m\ge m_0$. In particular the polynomial eventually equal to $m\mapsto\dim_kA_m$ depends only on the closed subscheme $Z$, not on the homogeneous ideal $J$ defining it. The ideal $J$ need not be saturated, and $Z$ may be empty, in which case both sides vanish for $m\gg0$.

The old O_Z(m) clause referred to the absolute scheme Proj(B) but cited only the
relative-model projective-space twist. `ProjectiveSpace.twist` is a module on
ℙ(n; Spec k), a distinct Lean scheme; the upstream TODO explicitly leaves comparison
with Proj(k[z_i]) unimplemented. The corrected clause specifies
O_Proj(B)(m) = B(m)~ and adds [def-weil-pbc-proj-twisting-sheaf] to that clause and
to stmt_deps. It follows Stacks constructions.tex, 01MN definition-twist (1), and
01MT lemma-apply-modules, opened for this repair. The existing def-pc-projective-space-twist
citation and its base record are retained; no definition or mathematical hypothesis
is changed. The original six proof steps and proof_deps remain byte-for-byte unchanged.
The new grading dependency from the saved packet also remains in stmt_deps.

Complete citer audit (rg of the exact quoted item id, filtered to stmt_deps/proof_deps):

- `lem-sfb-flat-graded-tail-proj`: holds true. Its field assertion still identifies the eventual quotient dimensions with Euler characteristics of the twists on the indicated polynomial Proj, including unsaturated and unit ideals.
- `lem-sfb-flat-projective-hilbert-polynomial-locality`: holds true. The field-valued comparison and independence of coordinate presentation still hold for the indicated projective embedding and its Proj twists.
- `lem-sfb-projective-curve-isom-graphs`: holds true. The graph in its fixed Segre projective embedding still has the same eventual coordinate and Euler polynomial; the specified Proj twist is exactly the polarization used in the chart calculation.

No citer is edited. The finite-graded-module-section-tail node mentions this id only
in provenance; it is not a statement/proof dependency citer.

Advisory H9: `MvPolynomial.gradedAlgebra` is now activated with
`attribute [local instance]` in each delivered module. Public declarations retain
fully elaborated instance arguments; importing these modules does not install this
instance globally. No new definition or theorem was added for this advisory.

## Repair self-check by Q21

Re-read the two saved modules against the item and new grading node. Field, N+1
variables, arbitrary homogeneous ideal, actual quotient pieces and quotient map,
canonical Proj closed immersion, tensor pullback, canonical k-structure, eventual
Euler and polynomial equalities, empty-Proj vanishing and embedded-isomorphism
independence all remain as in the reviewed packet. Each correspondence is in the
Worker report table above. All three sorry proofs remain named with source and proof
docstrings; the grading data is uniquely characterized. Checked the correction
against the two twist declarations and Stacks 01MN/01MT: no relative/absolute-model
identification is asserted or assumed. N=0, J=0, J=B, (z_0^r), and unsaturated ideals
retain exactly their prior coverage. This is the worker's repair self-check; the
maintainer performs the independent reading, as specified by the dispatcher.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
