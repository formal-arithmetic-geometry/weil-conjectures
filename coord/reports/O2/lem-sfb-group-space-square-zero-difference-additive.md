## Worker report

The module `Sheaf.AlgebraicGeometry.GroupSpaceSquareZeroDifferenceAdditive` states
`AlgebraicGeometry.AlgebraicSpace.groupSpace_squareZero_difference_additive`.
Its sole theorem has proof `sorry`; all definitions contain real data. The node's
mathematical statement, proof, and proof dependencies are unchanged. Its `stmt_deps`
only gains the two presentation definitions below and existing landed definitions
that supply the notions explicitly used by the statement. There are no dependency
module repairs and no statement correction.

Clause-by-clause reading:

- The base scheme is `{S : Scheme.{u}}` and the space is `G : AlgebraicSpace S`.
  `H : SpaceGroup G` specifies a `Group` on every actual `G(T)` with restrictions
  preserving multiplication and identity. Thus it gives the natural identity,
  multiplication, inverse and group identities. There is no `CommGroup`, smoothness,
  finite presentation or separation hypothesis. The existing
  `CommutativeSpaceGroup` would incorrectly add commutativity, so it is not used.
- The affine schemes over S are `{T₀ T : Over S}` with `IsAffine T.left` and
  `IsAffine T₀.left`. Their arrow is `j : T₀ ⟶ T`; its over-base equation is part
  of `Over.Hom`, and `hj : IsFirstOrderThickening j.left` is precisely a closed
  immersion with square-zero canonical defining ideal. This is the coordinate-free
  spelling of the node's Spec(A/I) → Spec(A), I²=0: the affine closed-immersion
  equivalence supplies A and I. No choice of A or of an isomorphism to its spectrum
  is imposed, and the zero ring/empty affine scheme remains allowed.
- The underlying functor-of-points type is `G.obj.obj.obj (op T)`.
  `H.onePoint T` is e_T, `H.onePoint T₀` is e₀, and `H.mulPoint T x y` is xy.
  `squareZeroPointMap` is the actual Yoneda map of a point, not an arbitrary map.
  `squareZeroGroupKernel H j` is the subtype whose equation is restriction along
  `j.op` equal to `H.onePoint T₀`; this is exactly the kernel K.
- `W : ThickeningSiteModel (groupSchemeMap j)` is the already defined normalized
  identification of the two small étale sites. Its reduction maps are actual scheme
  arrows with cartesian squares, and its quotient is their regular-function pullback.
  `J : SquareZeroIdeal W` is the actual ideal sheaf: its additive inclusion is natural,
  injective on sections, has image exactly the kernel of W's quotient, and has the
  prescribed quotient scalar action. Thus on this affine thickening it is Ĩ, not an
  arbitrary module assumed isomorphic to Ĩ. All choices of presentations are permitted.
- `D : SpaceRelativeDifferentialsModel (groupSpaceProjection G)` is precisely Ω¹_G/S
  with universal S-derivation, on the existing small étale site and in section universe u.
  Its universal property quantifies over EVERY module sheaf on that site. The ring
  map is the existing `cotangentFullRingMap`, canonically normalized by regular-function
  pullback on scheme charts. A universal differential presentation is the source's
  specification of the object up to its unique d-preserving isomorphism; it is not
  an additional geometric assumption. No Nonempty choice or new Ω construction is made.
- `(moduleTensorPullback (squareZeroPointMap (H.onePoint T₀))).obj D.omega` is e₀*Ω¹,
  using the existing tensor-pullback adjunction and its actual local tensor sections.
  The codomain of δ is its module-sheaf Hom to `J.obj`, exactly the Hom in the node.
- The first conclusion supplies δ for every b in K and requires
  `IsGroupSquareZeroDifference H W J D b (δ b)`. For EVERY target étale chart V,
  EVERY compatible reduced chart q, EVERY pair of scheme lifts r,s of that chart
  along b and e_T, and EVERY local function z on V, it asserts
  `inclusion (δ(b)(1 ⊗ dz)) = r♯(z) - s♯(z)`.
  Both ring maps on the right are literally `Scheme.Γ.map` of those scheme lifts.
  Formal étaleness of V → G supplies the lifts through a square-zero thickening;
  this is not an arbitrary unnormalized map or a coordinate on an unrelated module.
  These chart formulas specify b♯−e_T♯ on e₀⁻¹ O_G. Because D.derivation is an
  S-derivation and δ(b) is a module map, they also express exactly the node's assertion
  that the difference is an S-derivation. Universality and tensor generation make
  this the corresponding Hom coordinate, uniquely, without assuming its additivity.
- The next clause is `∀ b : K, b.val = H.onePoint T → δ b = 0`, exactly δ(e_T)=0.
  Naturality of the group identity ensures e_T belongs to K. Quantifying a kernel
  element equal to e_T avoids burying a proof of membership inside its constructor.
- The last clause is `∀ x y z : K, z.val = H.mulPoint T x.val y.val → δ z = δ x + δ y`.
  This is exactly δ(xy)=δ(x)+δ(y). Restriction preserves multiplication, so for every
  x,y their actual product is a member z of K. The additional z and its equality
  only spell out that product without an auxiliary closure theorem in a subtype
  constructor; they neither restrict the pairs nor replace multiplication by a free map.

Recorded dependency declarations read and used (full signatures and docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its `EtaleSite`,
  `structureSheaf` and `Modules`.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules` and its linear morphisms.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`.
- `Sheaf.AlgebraicGeometry.RegularGroupSpace`: only the existing `groupSchemeMap`
  and `groupSpaceProjection` (and their represented base); no geometric predicate
  of this module is assumed. Its owning node is added as a statement dependency.
- `Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData`: `ThickeningSiteModel`,
  its actual reductions, quotient, and `rings`.
- `Sheaf.AlgebraicGeometry.SpaceSquareZeroStalkData`: `SquareZeroIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleTensorPullback`, and the normalized `moduleTensorSection`.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `cotangentFullRingMap` and
  its normalized inverse-image structural map; its owning enlarged-ringed-site node
  is a dependency of the new differential-presentation node.
- `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`: the existing generic
  sheafified differential construction and derivation, owned by
  `def-sfb-sheaf-differentials`. It assumes essential smallness in the section universe;
  the new record presents the same universal object on the original full étale site
  without adding that size hypothesis or changing coefficients.
- Mathlib `PresheafOfModules.Derivation'` and `Derivation.postcomp`: the actual
  additive, Leibniz, relative-vanishing and restriction identities, reused directly.

The proof dependency `lem-sfb-space-square-zero-lift-linearization` was read in full.
It currently has neither a Lean record nor Mathlib match, so there is no module to
import for it yet. It is a proof dependency, not an unstated notion needed by this
signature; the proof docstring records all three accepted proof steps, to be implemented
with that dependency when it is stated. No additional postponed theorem was introduced.

Edge cases checked mathematically: I=0 gives the singleton kernel and zero Hom;
A=0 allows the empty affine scheme and zero coefficients; noncommutative GL_n gives
(1+X)(1+Y)=1+X+Y because I²=0; G_a gives the identity coordinate; G_m gives 1+i ↦ i;
μ_p in characteristic p remains allowed, with no reducedness or smoothness assumption.
All test schemes, their rings and module sections use the same explicit universe u;
there is no independent smaller test universe making the assertion vacuous. The chart
formula is local on arbitrary charts and includes zero sections and empty charts.

Searches (the raw service records are preserved in the new nodes' mathlib_searches):

- msearch leanfinder, “For a group algebraic space the difference from the identity on
  a square-zero thickening sends multiplication to addition of derivations”: 8 hits,
  principally `derivationToSquareZeroEquivLift` and its formulas and H1Cotangent.δAux_mul;
  these are ring lifts, not this geometric multiplication statement.
- msearch loogle `KaehlerDifferential, Derivation`: 12 ring-level hits, including
  `linearMapEquivDerivation`; no group-space statement.
- msearch grep `square.?zero.*(group|mul).*(deriv|add)|deriv.*square.?zero.*mul`: 0 hits.
- msearch leansearch “Universal sheaf of relative differentials for an algebraic space
  on its small etale site”: 8 hits, the presheaf differential APIs and scheme étale site.
- msearch leanfinder “sheaf of relative differentials for a morphism of algebraic
  spaces representing relative derivations”: 8 presheaf-differential hits.
- msearch leansearch “Group structure on an algebraic space functor of points natural
  in the test scheme without commutativity”: 8 generic commutative group-object and
  section-group hits; leanfinder on the noncommutative natural group structure: 8
  manifold/abstract presheaf hits. Loogle `GrpObj` returned unknown identifier; the
  actual Mathlib Cartesian/Grp.lean group-object API was therefore opened manually.
- msearch grep `SpaceGroup|GroupAlgebraicSpace|SpaceRelativeDifferentialsModel|
  AlgebraicSpace.*[Dd]ifferential`, Mathlib/AlgebraicGeometry: 0 hits.
- rg of live `lean/WeilConjectures` and `lean/Sheaf` for the node id, square-zero
  differences, SpaceGroup, derivations, relative differentials, Yoneda point maps:
  no exact statement or general group record. `RegularGroupSpace` has only the
  commutative record; scheme tangent statements have field/scheme hypotheses.
  Read the generic differential construction and the current small-ringed-site and
  cotangent interfaces rather than duplicating them.
- Whole-DAG definition searches found and read `def-sfb-sheaf-differentials`, the
  commutative group node, ringed module operations and normalized thickening data.
  None is the general group or full-site universal presentation record. Blueprint
  searches: no “group algebraic space” match; “relative differentials” gives only
  an unrelated projective-space unit. `blueprint_refs.py ancestor` returns None.

Sources opened locally: spaces-groupoids.tex definition-group-space (043H);
spaces-more-morphisms.tex definition-sheaf-differentials (04CT), difference-derivation
(0618), equation-D (0619), action-by-derivations (04D0); sites-modules.tex definitions
04BN/04BQ; groupoids.tex group-scheme-addition-tangent-vectors (0BF5).
No STATEMENT-DISPUTED issue or source correction was found.

## New nodes

`def-sfb-space-group` has the general natural group law of Stacks 043H: a Mathlib
Group structure on each actual functor-of-points type, with restriction homomorphisms.
Its module is `Sheaf.AlgebraicGeometry.SpaceGroup`. Existing commutative group data
would add a forbidden assumption. Mathlib has generic categorical group objects,
but no specialization carrying these actual pointwise structures; this record uses
Mathlib Group rather than copying group axioms. Its two projection helpers just
expose identity and multiplication of those same structures. No theorem or choice.

`def-sfb-space-relative-differentials-model` has the universal presentation of 04CT,
04BN and 04BQ. Its module is `Sheaf.AlgebraicGeometry.SpaceRelativeDifferentialsModel`.
It reuses the existing canonical `cotangentFullRingMap` and Mathlib Derivation';
it is a normalized presentation record, not another construction of sheaf differentials.
The existing `def-sfb-sheaf-differentials` is cited and its module imported. That
construction has an EssentiallySmall hypothesis in the section universe. On the
original full algebraic-space small étale site this size bound is unavailable in u;
requiring it or enlarging coefficients would change the statement. The presentation
record expresses the same full sheaf universal property without either change.
Its data are explicitly omega, d and the universal bijections, with no sorry or choice.
The resulting differential object is unique up to its unique d-preserving isomorphism.

## Validation

All three delivered modules compiled separately with scompile.py in dependency order,
under the prescribed server 60-second per-file limit, with no errors or unexpected
warnings. The exact final sources are validated again by the delivery preflight.

## Second reading by O2

Written by the maintainer's second reader (cc review service), because the delivered section only
recorded that no second worker reading took place. The Lean files and records are unchanged.

Node clauses and the Lean that renders them:

- Scheme S: `{S : Scheme.{u}}`. Correct.
- Group algebraic space G over S, with no commutativity or smoothness: `G : AlgebraicSpace S`,
  `H : SpaceGroup G` (a Mathlib `Group` on each `G(T)`, restrictions preserve `*` and `1`; Stacks
  043H). Inverse naturality follows from these. No `CommGroup`, no smoothness. Correct.
- Affine first-order thickening j : T₀ → T = Spec A, I² = 0: `{T₀ T : Over S} (j : T₀ ⟶ T)`,
  `[IsAffine T.left] [IsAffine T₀.left]`, `hj : IsFirstOrderThickening j.left`. A closed immersion
  with square-zero ideal into an affine scheme is the same as Spec(A/I) → Spec A, I² = 0.
  `IsAffine T₀.left` follows from the other hypotheses, so it adds no assumption. Correct.
- G(T), the product xy, e_T, e₀ and K: `H.mulPoint T`, `H.onePoint T`, `H.onePoint T₀` (equal to
  e∘(T₀→S) by `map_one`). `squareZeroGroupKernel H j` is the subtype where restriction along j
  equals e₀. This is K. Correct.
- Identification of the two small étale sites, and Ĩ: `W : ThickeningSiteModel (groupSchemeMap j)`
  (equivalence with cartesian reduction squares and quotient = Γ(reduction); Stacks 05ZS) and
  `J : SquareZeroIdeal W`. The inclusion of J is injective with image = ker(quotient), and its
  scalar action is the quotient action. On an affine thickening this is Ĩ. These are normalized
  presentations that exist and are unique up to unique isomorphism, so they are not free choices.
- Ω¹_{G/S} as the representing object of S-derivations into module sheaves:
  `D : SpaceRelativeDifferentialsModel (groupSpaceProjection G)`. Its derivation is relative to
  `cotangentFullRingMap` (p⁻¹O_S → O_G, pinned through ∃!), and composition with d is bijective
  for EVERY module sheaf N. This is Stacks 04CT/04BN/04BQ. Ω exists (quasi-coherent, glued from
  Ω_{U/S} on charts), so the hypothesis is not vacuous. Correct.
- e₀*Ω¹ and Hom_{O_{T₀}}(e₀*Ω¹, Ĩ): `(moduleTensorPullback (squareZeroPointMap e₀)).obj D.omega ⟶ J.obj`
  in `(schemeSpace T₀).Modules`. `squareZeroPointMap` is the Yoneda map of a point. Correct.
- δ(b) is the homomorphism corresponding to b♯ − e_T♯: `IsGroupSquareZeroDifference`. For every
  chart V of G, every chart q of T₀ over V, and every lift r (along b) and s (along e_T) of q to
  the thickened chart, `inclusion(δ(b)(1 ⊗ dz)) = Γ(r)z − Γ(s)z`. These lifts exist and are unique,
  because V → G is étale (formally étale) and the reduction arrow is a first-order thickening, so
  the condition is not vacuous. The right side lies in ker(quotient), because both lifts restrict
  to q. The sections 1 ⊗ dz generate e₀*Ω¹ locally, so δ(b) is uniquely determined. The sign is
  b♯ − e_T♯, as in the node. The ∃ δ is therefore pinned and not arbitrary.
- δ(e_T) = 0: `∀ b, b.val = H.onePoint T → δ b = 0`. e_T ∈ K by `map_one`. Correct.
- δ(xy) = δ(x) + δ(y) for all x, y ∈ K: `∀ x y z, z.val = H.mulPoint T x.val y.val → δ z = δ x + δ y`.
  For every x, y the product lies in K by `map_mul` and `map_one`, so no pair is excluded.
  Correct.

Edge cases: I = 0 (K is trivial, J = 0); A = 0 (both schemes empty, everything is zero); trivial G;
G_a, G_m; noncommutative GL_n; μ_p in characteristic p (non-smooth, still allowed). There is one
universe u for S, the test schemes and the sections, so no smaller test universe makes the
statement vacuous.

Records: the statement fields of the item and both new nodes are verbatim substrings of their
files. The item record differs from side-live only in `lean` and in the added definition
stmt_deps. All other dependency records in the snapshot are byte-identical to side-live. The only
proof is `sorry` (theorem). Every declaration has a source and blueprint docstring. The theorem
docstring carries the three proof steps of the node. Hollow definitions: none.

Searches: rg in side-live lean/Sheaf and lean/WeilConjectures for general group-space records and
algebraic-space differential records. Only `CommutativeSpaceGroup` was found, which is stronger.
No landed algebraic-space Ω record was found. Maintainer note: NP's FIX of
lem-sfb-group-space-square-zero-kernel-module (696454075c15, not yet landed) introduces
def-sfb-space-relative-differentials (`relativeOmega`, a construction on the small model) and
another group-functor encoding. These have no declaration-name clash with this delivery, but once
both land, the two Ω nodes should be related or merged (one definition per notion).

No mismatch found in the Lean; only this section was rewritten.
