## Worker report

This repair supplies the stage-2 statement missing from returned head 2825961839c6:
`Sheaf.Algebra.Homology.FunctorialBoundedAboveClassResolution`, declaration
`CochainComplex.exists_functorial_boundedAbove_class_resolution`. The sandbox supplied
for this retry was empty, so there was no retained Lean statement to repair. The node
was copied from the current read-only base; only its `lean` field is changed. In
particular its complete two-step `proof`, `proof_deps`, `statement`, and `stmt_deps`
are unchanged. The theorem has exactly one `sorry`, and no definition is introduced.

The source is the first three sentences of the current blueprint's
`sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`.
I read that proof, Stacks `derived.tex`, Lemma `lemma-subcategory-left-resolution`
(Tag 05T7), Mathlib `LeftResolution/Reduced.lean`, and FromJoel
`LeftResolution/CochainComplexMinus.lean`. Stacks is only the objectwise counterpart;
the all-bounds functorial construction is the FromJoel totalization and augmentation,
preceded by Mathlib's zero-preserving reduction. Both steps of the node's proof are
included in the theorem docstring, with their dependency node IDs. Module and theorem
docstrings both give the source and blueprint ID.

Hypothesis and conclusion correspondence:

| Node | Lean |
| --- | --- |
| An arbitrary abelian category A | `{A : Type u} [Category.{v} A] [Abelian A]`, with independent explicitly declared object and morphism universes. |
| A class of its objects | `F : ObjectProperty A`, Mathlib's object predicate. |
| Contains zero | `[F.ContainsZero]`; its definition asserts an object Z with `IsZero Z ∧ F Z`. Together with iso-closure this includes every zero object. |
| Closed under isomorphisms | `[F.IsClosedUnderIsomorphisms]`, the existing Mathlib class transporting F along every isomorphism. |
| Closed under finite biproducts | `h_biproduct : ∀ U V, F U → F V → F (U ⊞ V)` together with `F.ContainsZero`. Binary sums and the nullary sum are equivalent to all finite sums by induction and iso-closure. No infinite closure is assumed. |
| Closed under direct summands, explicitly U and V of U ⊕ V | `h_summand : ∀ U V, F (U ⊞ V) → F U ∧ F V`; iso-closure transports this to any biproduct decomposition. |
| A functor P on A | `P : A ⥤ A`. No `P.Additive`, `PreservesZeroMorphisms`, or `P.obj 0 = 0` is assumed. |
| Values of P belong to F | `hP : ∀ M, F (P.obj M)`. |
| Natural epsilon from P to the identity | `ε : P ⟶ 𝟭 A`. |
| Every component is epic | `hε : ∀ M, Epi (ε.app M)`. |
| Full bounded-above category, without a chosen bound | Upstream `CochainComplex.Minus A`: its property is `∃ n : ℤ, K.IsStrictlyLE n`, an existential proposition, and its category is the full subcategory. |
| A single functor S into all cochain complexes | `∃ S : CochainComplex.Minus A ⥤ CochainComplex A ℤ`. |
| Natural augmentation to the inclusion | `∃ a : S ⟶ CochainComplex.Minus.ι A`. |
| Every component is a quasi-isomorphism | `∀ L, QuasiIso (a.app L)`. |
| Every term lies in F | `∀ L i, F ((S.obj L).X i)`. |
| Every strict upper bound is preserved | `∀ L b, L.obj.IsStrictlyLE b → (S.obj L).IsStrictlyLE b`. Mathlib's `isStrictlyLE_iff` says exactly `∀ i, b < i → IsZero (K.X i)`, so this concerns terms, not just cohomology. |
| All morphisms, including different bounds | S is on the full category Minus A, with no fixed integer in its domain and no condition relating bounds of a morphism's endpoints. Functor laws and naturality are part of S and a. |

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`; the node is a Mathlib leaf, so its
  `mathlib_match` is its interface, not a missing `lean` record.
- `def-weil-abstract-derived-category` records
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`. I read their signatures and docstrings. The present statement
  uses its underlying `CochainComplex A ℤ` and `QuasiIso` notions; it does not form
  D(A), so no `HasDerivedCategory` hypothesis is needed. The recorded module is imported.
- `WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus`:
  `CochainComplex.minus`, `CochainComplex.Minus`, and `CochainComplex.Minus.ι` were read
  in full and used directly. There is no duplicate bounded-above definition.
- `Mathlib.CategoryTheory.ObjectProperty.ContainsZero`:
  `ObjectProperty.ContainsZero`, and through its imports
  `ObjectProperty.IsClosedUnderIsomorphisms`; binary biproducts are Mathlib's `⊞`.
- The two nontrivial proof nodes, `lem-sfb-left-resolution-reduced-class` and
  `lem-sfb-left-resolution-bounded-minus`, currently have neither a `lean` record nor
  `mathlib_match`. They are not needed to type this theorem, so this delivery does not
  introduce their statements merely to import them. Their exact roles are recorded in
  the proof docstring. The abelian proof dependency is already publicly imported.

Edge cases checked before writing:

- The nullary finite biproduct is covered by `ContainsZero`; arbitrary finite sums
  reduce to binary sums. No universe of finite indexing sets is restricted.
- L = 0 has every integer as an upper bound. The universally quantified bound clause
  therefore forces S(0) to vanish in every degree, as the reduced construction does.
- A complex concentrated in degree n preserves exactly that upper bound, including
  negative n; all indices and bounds are integers, with no nonnegativity condition.
- A map between bounded-above complexes with unequal upper bounds is an ordinary
  Minus morphism, so S acts on it. The statement does not choose a common bound.
- The free abelian-group functor P(M) = Z[M] has an epimorphic augmentation but P(0)
  is not zero and P is not additive. The hypotheses permit this example; the reduction
  splits off the distinguished zero generator. A requirement that P preserve zero
  would have excluded it, and is deliberately absent.
- The zero category and the class of all objects are allowed; iso-closure and the
  summand condition use categorical objects, not representatives chosen as equalities.

Searches made through `msearch.py` with this group and item:

- LeanFinder: `Functorial resolutions of all bounded above cochain complexes from a
  nonadditive functor with epimorphic covers in a summand closed class`. Eight hits
  included `Functor.mapProjectiveResolution`, `Abelian.LeftResolution`, and
  `Abelian.LeftResolution.chainComplexFunctor`; none states the class-valued,
  all-bounds conclusion from an arbitrary cover functor.
- Loogle: `"LeftResolution"`. Twelve hits gave the object-resolution datum and its
  chain-complex functor; none states the theorem here.
- Mathlib grep: `minusResolutionFunctor|minusResolutionNatTrans|bounded.*resolution`
  in `Algebra/Homology`: zero hits.
- LeanSearch: `Functorial bounded above resolution from epimorphic covers by a class
  closed under summands`. Eight hits concerned projective/injective resolutions and
  left-resolution data, with no exact match.
- `rg` in the upstream WeilConjectures tree and the side `lean/Sheaf` tree for this
  node ID, `minusResolutionFunctor`, `minusResolutionNatTrans`, and functorial
  bounded-above resolutions found the FromJoel construction and a ringed-site
  `exists_functorial_boundedAbove_flat_replacement`. I read the latter signature:
  it is specialized to sheaves of modules and one fixed bound N, hence cannot supply
  this theorem for arbitrary abelian A and all bounds simultaneously.
- Name searches for `exists_functorial_boundedAbove_class_resolution` and
  `FunctorialBoundedAboveClassResolution` in Mathlib, upstream and side Lean found
  no existing declaration.

No new nodes, dependency repairs, statement correction, or disputed statement.
All variables and both universes are explicitly bound. The node's `lean.statement`
is extracted verbatim from the theorem signature; lines are at most 100 characters.

Return points repaired: H1 is addressed by the new module, lean record, and this
report with both required sections. H2 is addressed by retaining the current base's
proof field verbatim (a JSON comparison found only `lean` changed). H3/H8/H10 are
addressed by the full-general statement, source/proof docstrings, and the prescribed
single-file compile and delivery preflight.

## Second reading by Q27

No second reading by another worker: this dispatcher brief forbids starting other
agents, and the worker delivers directly for the maintainer's independent review.
This section records the final self-check, without claiming an independent review.

I reopened the node and Lean statement together. The category and F are unrestricted
apart from the stated abelian and closure assumptions; the zero-plus-binary encoding
is equivalent to finite biproduct closure, including the empty sum. The summand
hypothesis returns both U and V. The cover functor carries no additive or
zero-preserving structure. The two component predicates retain every object M.
The conclusion has the exact source and target categories, the augmentation has the
correct direction, and all three output clauses quantify over every L. The bound
clause quantifies over every integer b after S has been chosen and uses termwise
vanishing, rather than cohomological vanishing or a chosen bound. All morphisms in
Minus are available. No mathematical mismatch or node fault was found; no correction
to statement or proof is required. The only postponed proof is the named theorem
corresponding to this item.

Validation: `scompile.py Q27 lem-sfb-functorial-bounded-above-class-resolution`
on the delivered module completed with exit code 0 and no errors or warnings.
Both the sandbox check and the library-path check succeeded. The JSON comparison
against the current shared node reports exactly one changed field: `lean`.
