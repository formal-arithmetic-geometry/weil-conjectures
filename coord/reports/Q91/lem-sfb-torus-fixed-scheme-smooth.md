## Worker report

The module `Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth` states
`AlgebraicGeometry.torus_fixed_scheme_smooth`, with its sole proof `sorry`.
The source is Milne, Algebraic Groups (2017), Theorem 13.1 (printed p.254),
with Lemma 13.6 and Theorem 13.7 (printed p.256). I opened those pages in
`literature/milne-algebraic-groups_iAG2017.pdf`, including the chapter convention
that schemes are algebraic over the base field. The docstring transcribes the
accepted node's eight-step finite-jet/weight-space proof and names its inputs.
The accepted statement and split are preserved.

Hypotheses and conclusion, matched to the node:

- The field k is `{k : Type u} [Field k]`.
- The k-group scheme T is `T : Grp (Over (Spec (.of k)))`. Its bundled
  `GrpObj T.X` supplies multiplication, identity, inverse and all group laws.
- T is affine by `[IsAffine T.X.left]` and finite type by
  `[LocallyOfFiniteType T.X.hom] [QuasiCompact T.X.hom]`.
- The geometric splitting of T as a finite product of G_m is
  `hT : MultiplicativeType.IsTorus T`. Its actual definition quantifies over
  `n : ℕ` and an isomorphism of group objects between the pullback to
  `AlgebraicClosure k` and `splitTorus (AlgebraicClosure k) n`.
  The latter is the recursive finite product of the recorded G_m, with the
  tensor unit for rank zero. There is no split-over-k hypothesis.
- The affine finite-type k-scheme X is `X : Over (Spec (.of k))`,
  `[IsAffine X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- Its smoothness is `[Smooth X.hom]`, the recorded scheme smoothness predicate.
- The action morphism and precisely its associativity and identity laws are
  `[action : ModObj T.X X]`. The data field is the morphism from the cartesian
  tensor product in `Over (Spec k)`; its two proof fields are the two action
  laws. Thus the product is the scheme fibre product over k, not a product of
  topological points. Mathlib's `CategoryTheory.Hom.smul` evaluates this map
  on pairs of test-scheme points by `lift t x ≫ ModObj.smul`.
- The given closed subscheme is `F : Over (Spec (.of k))` together with
  `i : F ⟶ X` and `[IsClosedImmersion i.left]`. This keeps its specified map
  and its compatibility with the k-structure.
- For every k-algebra A, `x : (algSpec (.of k)).obj (op A) ⟶ X` is an A-point.
  The left side of `hfixed` is `∃ z, z ≫ i = x`, its membership in the image
  of F(A). The right side quantifies over **every** `A' : CommAlgCat.{u} k`,
  **every** `f : A ⟶ A'`, and **every** A'-point `t` of T. The point
  `(algSpec (.of k)).map f.op ≫ x` is exactly x after scalar extension.
  The equation `t • (...) = ...` is the displayed fixedness condition.
  An A-algebra is equivalently a k-algebra A' with such a k-algebra map f;
  its k-structure is the composite through A. No injectivity, field condition,
  finite generation or nontriviality is imposed on these test algebras.
  Since a closed immersion is mono, a lift z is unique. Therefore image
  equality is precisely the representing condition, with its canonical
  natural bijection, not just the existence of some unrelated bijections.
- The conclusion is exactly `Smooth F.hom`: smoothness of F over k.

Dependency declarations used (signatures and docstrings read):

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and its bundled `Grp`,
  Mathlib.CategoryTheory.Monoidal.Grp; its specialization to schemes over
  a field is documented in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, as their recorded conjunction.
- `def-weil-algebraic-closure`: `AlgebraicClosure` and `IsAlgClosure`,
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure and Basic, used by `IsTorus`.
- `def-sc-gm-ga`: `StandardGroupSchemes.multiplicative` and its canonical
  `multiplicativeGroup`, Sheaf.AlgebraicGeometry.StandardGroupSchemes;
  the torus's recursive product uses these exact declarations.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` and `IsAffine`,
  Mathlib.AlgebraicGeometry.Scheme and AffineScheme.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections
  and universal map, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback;
  the `Over` cartesian monoidal structure uses these scheme pullbacks.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- The already landed definition node `def-sfb-tori-multiplicative-type` is
  added to `stmt_deps` for the reused `MultiplicativeType.IsTorus`,
  `baseChange`, and `splitTorus` in Sheaf.AlgebraicGeometry.ToriMultiplicativeType.
  This is the same geometric splitting already spelled out by the item.
- The action notion is Mathlib's `CategoryTheory.ModObj`,
  Mathlib.CategoryTheory.Monoidal.Mod; its action on Hom types is in
  Mathlib.CategoryTheory.Monoidal.Cartesian.Mod. No duplicate action or
  fixed-subfunctor definition was introduced.

Proof-only imports include the recorded modules for finite presentation,
field-extension flatness, surjective base change, smooth flat base change,
and regularity of smooth schemes: Mathlib.RingTheory.FinitePresentation,
Mathlib.AlgebraicGeometry.Morphisms.Flat,
Mathlib.AlgebraicGeometry.PullbackCarrier,
Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange, and
WeilConjectures.AlgebraicGeometry.Regular. Smooth local-on-source is already
available from the public Smooth import. At the read base the following proof
inputs have no recorded declaration/module and hence cannot yet be imported:
lem-sfb-scheme-large-algclosed-jacobson,
lem-sfb-torus-fixed-local-ideal-jets,
lem-sfb-gm-representation-weight-basis,
lem-sfb-regular-quotient-parameter-approximation,
lem-sfb-regular-separable-affine-smooth-neighbourhood,
lem-sfb-space-maximal-smooth-open. They are not needed to type this statement.

Edge cases checked: rank zero is admitted by the tensor-unit split torus;
there is no nonemptiness or connectedness assumption on X or F, so empty
schemes are included. All field characteristics, imperfect fields and nonsplit
tori over k remain allowed. Test algebras include the zero ring and nilpotent
thickenings, and f includes identities and arbitrary algebra extensions. The
same universe u is used for k, schemes and test algebras; there is no independent
smaller universe making the fixedness hypothesis vacuous. Closed-immersion
monicity makes the image condition a genuine representing condition, and
precomposition supplies its naturality. No statement fault or dispute found.

Searches made for an existing statement:

- `msearch.py`, LeanFinder: "The fixed subscheme of a smooth affine scheme
  under a torus action is smooth": 8 hits, basic scheme smoothness and smooth
  locus results; none states torus fixed-scheme smoothness.
- `msearch.py`, LeanSearch: "Fixed locus of a torus acting on a smooth scheme
  is smooth": 8 hits, including `MulAction.fixedPoints`, `fixedBy`,
  `Algebra.smoothLocus` and scheme smoothness recursors; no matching theorem.
- `msearch.py`, Loogle: `"fixed", "Smooth"`: 0 hits.
- `msearch.py`, grep: `fixedSubscheme|linearlyReductive|torus` in
  Mathlib/AlgebraicGeometry: 0 hits.
- `rg` over lean/WeilConjectures and lean/Sheaf for torus/Torus,
  fixedSubscheme/fixedScheme, scheme actions, and subsequently
  fixedFunctor/IsFixed/fixedPoints/FixedScheme/fixedSubfunctor. The project
  has ToriMultiplicativeType and several special torus constructions, and
  SchemeActionTorsorGroupoids uses the existing Mathlib ModObj action;
  no existing fixed-scheme smoothness theorem was found. Matches for
  Artin-Schreier Frobenius fixed points and algebra fixed subrings are unrelated.
- Exact node-id search in lean/WeilConjectures and in
  dag/lean_names_upstream.json: no matches. The geometric torus definition
  was found and reused instead of restated.

Validation: the prescribed `scompile.py Q91 lem-sfb-torus-fixed-scheme-smooth`
compiled both the sandbox and library forms cleanly (6.5 s and 4.4 s).
`set_option autoImplicit false` enforces explicit variable/universe binding.
No proofs beyond `sorry`, new data definitions or new nodes are delivered.
The earlier stage-1 already-reviewed rejection is superseded by the explicit
stage-2 handoff in coord/brief-stage2.md §0; this packet records the Lean
statement without reopening the accepted split.

## Second reading by Q91

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
