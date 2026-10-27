## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusInfinitesimalConjugacy`
states `AlgebraicGeometry.splitTorus_infinitesimal_conjugacy`, with its sole proof
`sorry`. It introduces no definitions. The node's natural-language statement,
proof and proof dependencies are unchanged. Its statement dependencies gain the
already landed `def-sfb-split-torus-over-ring`, whose canonical construction is
used directly rather than duplicated.

Source read: Conrad, Reductive group schemes, online at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed p.287,
Corollary B.2.6 and its proof, and printed p.285, Remark B.2.4. The former
identifies conjugacy classes of supplied lifts under the congruence kernel with
a torsor under degree-one Hochschild cohomology; the latter gives its vanishing
for multiplicative-type groups. Thus the supplied split-torus lifts are conjugate
without injectivity, noetherianity or reductivity. Only conjugacy of already given
lifts is stated, not existence of a new lift. The declaration docstring records
the node's four-step Laurent-coefficient argument, including both unstated
proof prerequisites by their exact node IDs.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary commutative ring A is `(A : Type u) [CommRing A]`. There is no
  nontriviality, field, noetherianity or characteristic restriction.
- The ideal and square-zero condition are `(J : Ideal A)` and
  `(_hJ : J ^ 2 = ⊥)`. The underscore only avoids an unused-variable warning;
  the hypothesis remains in the theorem's type.
- S is `Spec (.of A)`. The map from S0 is
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))`, with domain
  `Spec (.of (A ⧸ J))` and codomain S.
- A group scheme G over S is `(G : Over (Spec (.of A))) [GrpObj G]`.
  Its multiplication, inverse and identity, and all their diagrams, come from
  the recorded `CategoryTheory.GrpObj` interface, which works over arbitrary
  bases and is not specialized to fields.
- Smooth, affine and finite presentation are `[Smooth G.hom]`,
  `[IsAffineHom G.hom]`, and `[LocallyOfFinitePresentation G.hom]`.
  For an affine morphism, quasi-compactness and quasi-separatedness are
  automatic, so the last condition is precisely finite presentation here.
- The nonnegative rank is `(r : ℕ)`. The source group is
  `(RingGroupSchemes.splitTorus A r).X`, the landed product of r Laurent-Hopf
  multiplicative groups. It is canonically Spec of the r-variable Laurent
  algebra with multiplication of units, and the empty product is the trivial
  group over S. No chosen arbitrary group structure is substituted.
- The two S-group homomorphisms are `(f₁ f₂ : ... ⟶ G)` with
  `[IsMonHom f₁] [IsMonHom f₂]`. No mono, subgroup or injectivity condition occurs.
- Equality after scalar extension to A/J is `hmod`: the two scheme maps agree
  after precomposition with `pullback.fst T.hom (Spec.map ... quotient ...)`.
  This is exactly equality on T0. Maps from T0 to G0 over S0 are determined by
  their projections to G, since their other projection is the fixed structural
  morphism. Thus this form is equivalent to equality of the base-changed
  homomorphisms, with no extra condition or weakening.
- The section u in G(A) is `∃ u : Over.mk (𝟙 (Spec (.of A))) ⟶ G`.
- Reduction of u to the identity is the first conjunct: the `Over.homMk`
  represented by Spec(A/J) → Spec A, followed by u, equals `1`. This is an
  equality in the actual Hom group of points on S0, not an arbitrary predicate.
- The second conjunct is `(T→S ≫ u) * f₁ * (T→S ≫ u)⁻¹ = f₂` in the
  Hom group `T ⟶ G`. Its multiplication and inverse come from `GrpObj G`.
  Precomposing with any test point gives u f₁(t) u⁻¹ = f₂(t); equality of
  morphisms also ensures this on test algebras in larger universes. The order
  agrees with Int(u) ∘ f₁ = f₂, including the inverse placement.
- No connectedness, reductivity, field or noetherian condition is imposed.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`
  (def-weil-affine-spectrum); their definitions and documentation were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth` (def-sbc-smooth-morphisms), the affine-local smooth
  ring-map predicate; its class and docstring were read.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`
  (def-sbc-locally-finite-presentation), its affine-local class and docstring.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`
  (def-sc-group-scheme). Also read its existing application in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. The latter file's field
  binders do not restrict the generic Mathlib class, so no dependency repair is
  needed. Read `IsMonHom` in Monoidal.Mon and Hom.group in
  Monoidal.Cartesian.Grp for the homomorphism laws and pointwise operations.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `AlgebraicGeometry.RingGroupSchemes.multiplicative` and `splitTorus`
  (def-sfb-split-torus-over-ring). Both full definitions and docstrings were
  read; this dependency was added to stmt_deps under the landed-node rule.

The first two proof dependencies, lem-sfb-group-space-square-zero-kernel-module
and lem-sfb-smooth-group-congruence-flat-scalar-extension, have no recorded Lean
interface or Mathlib match in the read repository. They are not needed to TYPE
this statement; no interface is invented for them and no unavailable proof
module is imported. The third proof dependency is Spec, already imported through
the public statement imports. The maintainer can add the two proof imports when
their statements land.

Edge cases checked before writing: r=0 has terminal source and both homomorphisms
are identity-valued; take u=1. J=0 makes the two homomorphisms equal and again
u=1 works. If J is the unit ideal and J²=0, A is the zero ring, already allowed
by `[CommRing A]`; the empty base causes no excluded case. No finite-generation
condition on J is used. Noninjective, including trivial, homomorphisms are
allowed. Disconnected G and positive or mixed characteristic are allowed.
Arbitrary rings and schemes are accommodated by the explicit universe u; no
quantification over an independently smaller universe of algebras occurs.

Searches made with the prescribed msearch.py (all succeeded):

- LeanFinder query: "Two homomorphisms from a split torus into a smooth affine
  group scheme agreeing modulo a square zero ideal are conjugate by a point
  reducing to the identity". Eight hits, including formally smooth lifts and
  formally unramified uniqueness; none is this group-scheme conjugacy theorem.
- Loogle query: `"torus", "conjug"`. Zero hits.
- Mathlib grep query: `torus|diagonalizable|infinitesimal.*conjug`, restricted
  to AlgebraicGeometry. Zero hits.
- LeanSearch query: "homomorphisms from split torus to smooth group scheme
  infinitesimal conjugacy". Eight hits, including Scheme.Hom, extension
  splittings, MulAut.conj; none gives this theorem.
- Direct rg over the source library and Sheaf for torus, splitTorus,
  diagonalizable and conjugacy found the already landed split-torus definitions
  over fields, rings and general bases. The ring construction is used. Direct
  search for the item's blueprint ID in WeilConjectures found no declaration.
  Searching the proposed theorem name and infinitesimal-conjugacy patterns
  throughout both library roots found no existing theorem. DAG searches located
  def-sfb-split-torus-over-ring and def-sfb-relative-split-torus and both records
  were read. No new definition node is necessary.

Compilation: the first attempt requested an explicit target for Over.homMk;
adding `(V := Over.mk (𝟙 (Spec (.of A))))` to the canonical restriction maps
resolved it without changing the mathematical statement. The final scompile.py
run compiled the sandbox and library module separately, in about two seconds
each, with no errors or warnings. All variables and universes are explicit.
No theorem was proved, and no definition uses sorry. No statement dispute or
correction is necessary.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
