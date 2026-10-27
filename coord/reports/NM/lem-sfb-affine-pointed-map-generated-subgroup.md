## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.AffinePointedMapGeneratedSubgroup states
AlgebraicGeometry.affinePointedMap_generated_subgroup, with one postponed proof. Four real
helper constructions belong to the same node and are listed in lean.declarations: the word
map, the intersection ideal, the quotient spectrum over k, and its canonical inclusion.
No independent notion, new node, dependency repair, or statement correction is needed.

Source read: Milne, Algebraic Groups (2017), section 2h, affine case, printed pp.54--55:
the paragraph preceding Proposition 2.46, Proposition 2.46, and Proposition 2.48. The source
explicitly quantifies over small k-algebras. Its pointed affine construction is precisely
the construction formalized here; no smoothness, reducedness, or characteristic assumption
is imposed. The theorem docstring carries all seven steps of the node's natural-language
proof, with the named intermediate results, including the universal-ring inversion argument
and the two tensor zero-detection applications.

Hypothesis and clause correspondence:

- Field k: `{k : Type u} [Field k]`. The universe is explicit and autoImplicit is disabled.
- A k-group scheme G: `G : Over (Spec (.of k))` with `[GrpObj G]`, using the dependency's
  recorded category-theoretic group-object interface.
- G affine and finite type: `[IsAffine G.left]`, `[LocallyOfFiniteType G.hom]`, and
  `[QuasiCompact G.hom]`. The last two are exactly the finite-type convention of
  def-weil-finite-type-morphism, rather than a finite or smooth group hypothesis.
- X an affine finite-type k-scheme: `X : Over (Spec (.of k))` with the same three
  structure-morphism predicates, without a group structure on X.
- A k-point o: `o : 𝟙_ (Over (Spec (.of k))) ⟶ X`. The tensor unit in this over-category
  is Spec k with its identity structure morphism, so an over-morphism is exactly a
  section. This is the rational-point notion used by Scheme.Hom.baseChangeFieldPoint;
  the base-change construction itself is not required by this statement.
- A k-morphism φ: `φ : X ⟶ G`; it is not required to be a homomorphism.
- Pointedness φ(o) = e: `hφ : o ≫ φ = 1`, where the standard MonObj morphism-group
  operation makes 1 the identity section of G.
- Inversion stability: `hinv` quantifies over every `R : Type u`, `[CommRing R]`,
  `[Algebra k R]` and every R-point x of X, and requires an R-point y with
  `y ≫ φ = (x ≫ φ)⁻¹`. This says exactly that the image subset is stable under inversion;
  it does not posit an involution on X or natural choices of inverse lifts.
- For n ≥ 1 the word morphism is `affinePointedWordMap φ (n-1)`: its domain is the
  categorical product of n copies of X in Over (Spec k). The definition uses
  `List.ofFn` followed by `.prod`, so factors are ordered, allowing noncommutative G.
  In code the nonempty lengths are enumerated bijectively as n+1 for n : ℕ.
- A = k[G] is `Γ(G.left, ⊤)`. Pullback on coordinates is `.left.appTop.hom` and
  `affinePointedWordIdeal φ` is `⨅ n : ℕ, RingHom.ker ...`. This is precisely the
  intersection over positive lengths, with no radical, stabilization, or reduction.
- L = Spec(A/I) is the underlying scheme of `affinePointedGeneratedScheme φ`.
  Its structure morphism is the actual composite `Spec.map (Ideal.Quotient.mk I)`,
  `G.left.isoSpec.inv`, and `G.hom`. The same first two arrows give the underlying
  map of `affinePointedGeneratedInclusion φ`. Thus no arbitrary closed image or
  existential replacement of the specified scheme or inclusion is used.
- L is a closed subgroup: the conclusion supplies `∃ hL : GrpObj ...` and
  `@IsClosedSubgroupScheme ... hL ... (affinePointedGeneratedInclusion φ)`.
  This recorded class includes the homomorphism property, injectivity on every
  R-point set, and closed immersion of the underlying map.
- Factorization of φ: `∃ ψ : X ⟶ L, ψ ≫ affinePointedGeneratedInclusion φ = φ`.
- Minimality: for every k-group scheme K and `i : K ⟶ G` with
  `IsClosedSubgroupScheme i`, any factorization of φ through i gives
  `∃ j : L ⟶ K, j ≫ i = affinePointedGeneratedInclusion φ`. This is inclusion
  as subschemes of G, not merely containment of field-valued points. Since i is
  a monomorphism, such a factorization is automatically the subgroup inclusion.
- L affine and finite type: `IsAffine L.left ∧ LocallyOfFiniteType L.hom ∧
  QuasiCompact L.hom`, with the conjunction right-associated in the signature.
- Geometric reducedness: `GeometricallyReduced X.hom → GeometricallyReduced L.hom`.
- Geometric connectedness: `GeometricallyConnected X.hom → GeometricallyConnected L.hom`.
  These are the dependency's Mathlib predicates, quantified over field extensions,
  and are separate implications without assuming either property of X initially.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, with the standard
  CategoryTheory.MonObj scope for the group structure on morphisms into G.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom, Spec, Spec.map.
- Mathlib.AlgebraicGeometry.AffineScheme: IsAffine, Scheme.isoSpec, the canonical
  isomorphism from an affine scheme to the spectrum of its global sections.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType; the recorded
  finite-type convention also uses QuasiCompact from Morphisms.QuasiCompact.
- WeilConjectures.AlgebraicGeometry.DensePoints: Scheme.Hom.baseChangeFieldPoint;
  its full signature and docstring describe rational points as sections. Here the
  section is expressed directly as an over-category morphism from Spec k.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, pullback.fst,
  pullback.snd, pullback.lift. Finite products in the over-category are iterated
  fibre products over k, implemented using Mathlib's chosen finite products.
- Mathlib.Algebra.Algebra.Hom: AlgHom; Mathlib.RingTheory.Ideal.Quotient.Operations:
  Ideal.Quotient.algebra and Ideal.Quotient.mkₐ. The underlying ring quotient map
  Ideal.Quotient.mk defines the same canonical quotient spectrum without choosing
  a second algebra structure on Γ(G, ⊤).
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: IsSubgroupScheme and
  IsClosedSubgroupScheme (including their R-point quantifiers and group structure
  parameters). This is the dependency's existing closed subgroup notion.
- Mathlib.AlgebraicGeometry.Geometrically.Integral imports GeometricallyReduced
  and GeometricallyIrreducible; GeometricallyConnected is imported explicitly from
  Mathlib.AlgebraicGeometry.Geometrically.Connected. All four recorded geometric
  predicates were read; only reducedness and connectedness occur in this theorem.

Proof dependencies are imported with ordinary imports where already stated: tensor
zero detection uses TensorProduct.eq_zero_of_forall_rTensor_eq_zero from
WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis (recorded in the dependency's
closed upstream audit); affine pullbacks use Mathlib.AlgebraicGeometry.Pullbacks;
flatness uses Morphisms.Flat; Noetherianity uses AlgebraicGeometry.Noetherian,
RingTheory.FiniteType and Spectrum.Prime.Noetherian; the clopen-idempotent criterion
uses Spectrum.Prime.Topology. Closed immersion, reducedness, geometric pullback,
connected components and locally-finite-type affine pairs are in the already imported
modules. No new proof dependency statement is introduced.

Edge cases checked before writing:

- X empty is ruled out by its supplied section, not by an extra nonemptiness hypothesis.
- The trivial group and constant identity morphism are allowed: every positive word
  is the identity, and L is the identity subgroup with both geometric properties.
- The minimal length is one, including the original morphism (up to the canonical
  singleton-product isomorphism); no length-zero word is substituted for it.
- Noncommutative groups are allowed: List.ofFn retains the order of factors.
- Nonreduced X and nonreduced finite group schemes are allowed; I is not radicalized.
- The zero k-algebra R is included: no Nontrivial R hypothesis is imposed. Its point
  functor is evaluated on the empty spectrum exactly as in the recorded subgroup class.
- Positive and zero characteristic and imperfect fields are all admitted.
- The tests R, field k, and schemes use the same ambient universe u, as in the source's
  small-algebra convention and the recorded IsClosedSubgroupScheme interface. No
  independent lower test universe or algebraic-closedness hypothesis is introduced.

Searches for an existing statement (msearch.py, NM, this item):

- LeanFinder: "An inverse stable pointed morphism from an affine finite type scheme to
  an affine algebraic group generates the closed subgroup defined by the intersection
  of kernels of all word maps". Eight results, including abstract subgroup-closure
  facts and a Galois automorphism closed-image theorem; none states this construction.
- LeanSearch: "An inverse stable pointed morphism to an affine group scheme generates
  a smallest closed subgroup given by intersection of word map kernels". Eight
  results about abstract or topological subgroups; none is a scheme statement.
- Loogle: "IsClosedSubgroupScheme, GrpObj, Scheme.Hom.appTop". No results; the service
  does not know the upstream-only identifier IsClosedSubgroupScheme.
- Loogle: "RingHom.ker, Ideal". Twelve results, identifying RingHom.ker and its basic
  properties, but no word-map subgroup theorem.
- Mathlib grep via msearch.py: "generatedSubgroup|wordMap|word_map|inverse.stable",
  subdirectory AlgebraicGeometry. Zero hits.
- rg over WeilConjectures and Sheaf/AlgebraicGeometry and Sheaf/GroupTheory for
  "generatedSubgroup|generated_subgroup|wordMap|word_map|inverse.stable|inverse-stable|pointed.map":
  unrelated pointed-etale morphisms and complex-comparison word maps; the downstream
  SmoothConnectedDerivedSubgroup docstring cites this node but does not state it.
- rg for this exact node ID in WeilConjectures: no declaration or duplicate construction.

Validation: scompile.py compiled the module in sandbox and library mode. The initial
probe needed the standard `open scoped MonObj` for morphism-group operations; this was
fixed without changing the mathematical statement. The final dry run compiles the
complete delivered module again with its proof-dependency import. All definitions
have concrete data, and the sole theorem proof is sorry. No disputed statement or
node fault was found.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
