## Worker report

The module `Sheaf.AlgebraicGeometry.NormalVarietyAffineParameterPicard` states
`AlgebraicGeometry.nonempty_iso_tensorPullback_lift_of_normal_variety`, with its entire
proof `sorry`. It introduces no definitions. The node changes only in `lean`.
Source read: `literature/stacks-project/varieties.tex`, Tag 0BEH,
`lemma-rational-equivalence-for-Pic`, statement and proof (lines 5867–5888).
The theorem docstring retains all five steps of the accepted DAG proof.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| X is an integral scheme | `(X : Scheme.{u}) [IsIntegral X]` |
| X is over k | `sX : X ⟶ Spec (CommRingCat.of k)`; the explicit structure map is used in the base change defining the product |
| X is of finite type over k | `[LocallyOfFiniteType sX] [QuasiCompact sX]`, exactly the conjunction prescribed by the recorded dependency |
| X is separated over k, meaning its diagonal is a closed immersion | `[IsClosedImmersion (pullback.diagonal sX)]` |
| Every local ring is an integrally closed domain | `hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)` |
| n ≥ 0 | `n : ℕ`; no positivity assumption |
| U is an open subscheme of affine n-space over k | `(U : Scheme.{u}) (j : U ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k))) [IsOpenImmersion j]` |
| The structure map of U | `j ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)`, where C is the coefficient inclusion k → k[t₁,…,tₙ] |
| p,q belong to U(k) | Morphisms `p q : Spec (CommRingCat.of k) ⟶ U`, with hp and hq asserting that their composites with this structure map are the identity |
| N is an invertible module on X ×_k U | `N : (pullback sX (j ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C))).Modules` and `[N.IsInvertible]` |
| i_r(x) = (x,r) | `pullback.lift (𝟙 X) (sX ≫ r) (by simp [hr])`, separately for p and q; this is the universal-property pairing of the specified maps, not an arbitrary section |
| Pullback is tensor inverse image | `(Scheme.Modules.tensorPullback i_r).obj N` on both sides |
| There is an O_X-linear isomorphism between the two fibre modules | `Nonempty (... ≅ ...)` in `X.Modules` |

An open immersion is precisely the dependency node's equivalent presentation of an
open subscheme: its source is isomorphic to the corresponding restricted scheme.
Thus the U,j presentation imposes no affineness or principal-open restriction. The
section equations hp,hq express rationality over k, rather than introducing extra
conditions on rational points. The small `by simp` terms only establish the
commutativity required for these canonical pairings; no mathematical assertion of
the node is proved in this stage.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`; its docstring and full class fields were read.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (reexported by the finite-type import).
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed`, the recorded inline
  normal-domain conjunction, with the latter from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. No separate normal predicate.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, reexported by the scheme-property imports.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.lift`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies existence for schemes.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`. Its full definition requires
  local triviality near every point, so there is no new rank-one notion here.
- `def-pc-module-pullback`: public import of the recorded
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, whose reexported
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` is constructed in
  `WeilConjectures.AlgebraicGeometry.TensorPullback` by the sheaf tensor formula.
  Both the recorded section-normalized interface and the functor's full source were read.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and its coefficient inclusion
  `MvPolynomial.C`, `Mathlib.Algebra.MvPolynomial.Basic`.

For the statement's explicit diagonal, the definition of separatedness in
`Mathlib.AlgebraicGeometry.Morphisms.Separated` was also checked. Public imports
give the statement dependencies; plain imports give the already stated proof
inputs (Noetherian permanence, affine spectrum products, polynomial flatness and
factorization, and `Sheaf.AlgebraicGeometry.AffineSpaceOpenInvertibleTrivial`).
`lem-sfb-normal-noetherian-generic-line-pullback` has no recorded Lean declaration
in the read clone, so no speculative import of that proof-only input is added.
It is not needed to elaborate the present statement.

Edge cases checked before writing:

- n = 0 is retained by `Fin 0`; affine zero-space is Spec k and nothing requires n > 0.
- U need not be affine: an arbitrary open immersion is allowed, including the
  punctured affine plane. No principal-open or finite-cover hypothesis was introduced.
- The empty open has no k-rational point for a field. The formulation covers it
  vacuously through the specified p,q; it does not independently assume U nonempty.
- p = q is allowed; the conclusion then admits the identity isomorphism.
- k can be finite, imperfect, or of any characteristic. No algebraic-closure,
  characteristic-zero, smoothness, regularity, or factoriality assumption is present.
- Integral X is nonempty by its recorded definition, exactly as in the node.
  All schemes and the field have the explicit universe u, arbitrary throughout;
  no hidden universe binders or locally defined notation are used.

Searches actually run on 2026-10-24 (wrapper group Q01, this item):

- LeanFinder: “For a normal variety X, an invertible sheaf on X times an open of
  affine space has isomorphic pullbacks at any two rational points”. Eight hits,
  including affine-space parametrization and normalization facts, none the theorem.
- LeanSearch: “An invertible sheaf on a normal variety times an open of affine
  space has isomorphic restrictions at any two rational points”. Eight hits about
  restricted sheaves and stalks, none the theorem.
- Loogle: `"tensorPullback"`. Zero hits in Mathlib.
- Mathlib grep through msearch: `rational.*[Pp]ic|[Aa]ffine.*[Rr]igid|[Pp]icard`
  in AlgebraicGeometry. Three elliptic-curve documentation hits, no theorem.
- Local rg over `lean/WeilConjectures` and `lean/Sheaf`:
  `rational.*[Pp]ic|[Aa]ffine.*[Rr]igid|affine.*parameter`. Read
  `WeilConjectures.AlgebraicGeometry.Picard.AffineSpaceRigidity` and
  `WeilConjectures.AlgebraicGeometry.Picard.LocalizationAwayRigidity` in full
  through their relevant theorem signatures. Their rigidity theorems require
  algebraic closure and factorial local rings and use principal opens, so neither
  is the present theorem. Also read the existing translated Cartier parameter
  family statement to check compatibility of its rational-point/product encoding.
- Node-id rg over `lean/WeilConjectures`: no existing declaration for this item.
- Full-name rg over Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no collision for the new theorem name.

There are no statement disputes, corrections, new nodes, or dependency repairs.
The prescribed scompile.py compiled this file in both sandbox and library-module
modes with exit code 0, in 5.0 and 2.9 seconds, respectively, with no diagnostics.

## Second reading by Q01

This is the author's second reading; the maintainer supplies the independent
review under the dispatcher's direct-delivery instructions. I reopened the node,
the source statement at 0BEH, and the Lean signature together. The separate
locally-finite-type and quasi-compact instances give exactly finite type;
normality is the stated condition on all stalks, with no factoriality assumption.
The diagonal uses the same structure map sX as the product. The open immersion
lands in the spectrum of the n-variable polynomial ring, and hp,hq refer to its
coefficient projection, so these are genuine k-points. Each pairing has first
component id_X and second component sX followed by the specified point. Both
objects in the conclusion use the recorded tensor functor and are modules on X.
Every clause and hypothesis has the counterpart in the table above. No mismatch
was found and no source or node statement changed on this reading.
