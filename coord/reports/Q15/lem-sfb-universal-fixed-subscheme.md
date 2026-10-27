## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalFixedSubscheme` states
`AlgebraicGeometry.exists_universal_fixed_subscheme`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. The accepted
stage-1 statement, dependencies, and proof are preserved. The previous BLOCKED ending
confused the N6 stage-1 review with completion of stage 2: the current node has no
Lean record, and brief-stage2 §0 explicitly authorizes this handoff.

Source read: Milne, Algebraic Groups (2017), the beginning of Chapter 7 and Theorem
7.1 with its proof and preceding largest-fixed-closed-subscheme formulation, printed
pp.138–139, from the local PDF. It explicitly tests every algebra extension, uses
the closed diagonal, and does not assume reducedness. The node's four proof steps
are reproduced in the theorem's docstring. Its arbitrary-scheme clause is the same
representing property on affine charts, as specified by the node's source.

Hypothesis and clause correspondence:

- Field: `{k : Type u} [Field k]`. The explicit `universe u` and
  `set_option autoImplicit false` bind all sizes and variables.
- Group scheme and scheme over k: `(G Y : Over (Spec (.of k))) [GrpObj G]`.
  The multiplication, identity, inverse and their diagrams are the recorded
  internal group object, without a commutativity assumption.
- Separated finite-type G: `[IsSeparated G.hom]`,
  `[LocallyOfFiniteType G.hom]`, `[QuasiCompact G.hom]`.
  The same three instances on `Y.hom` give exactly the hypotheses on Y.
  `IsSeparated` means that the relative diagonal is a closed immersion.
- Action b and both laws: `[ModObj G Y]`; its action morphism is
  `ModObj.smul (M := G) (X := Y)`, and its two fields are the unit and
  associative action diagrams. The induced action on every test-point set is
  `CategoryTheory.Hom.smul`, written `g • y`. This is the existing Mathlib
  notion, not a private copy or an assumption of representability.
- A commutative k-algebra B and its point y: `(A : CommAlgCat.{u} k)` and
  `y : (algSpec (.of k)).obj (op A) ⟶ Y`. These are morphisms over k from
  Spec A, not arbitrary underlying maps of schemes.
- Every B-algebra B' and every g: `∀ (A' : CommAlgCat.{u} k) (f : A ⟶ A')
  (g : (algSpec (.of k)).obj (op A') ⟶ G)`. Giving this k-algebra
  homomorphism is exactly giving A' its compatible A-algebra structure; no
  injectivity, nonzeroness, finite generation or flatness is imposed.
- Scalar extension `y_{B'}` is the actual precomposition
  `(algSpec (.of k)).map f.op ≫ y`. The equation
  `g • ((algSpec (.of k)).map f.op ≫ y) = (algSpec (.of k)).map f.op ≫ y`
  is the defining universally fixed condition, including f the identity.
- Representing closed subscheme: `∃ (F : Over (Spec (.of k))) (i : F ⟶ Y),
  IsClosedImmersion i.left ∧ ...`. No arbitrary map substitutes for a closed
  immersion. For every A and y, `∃! z, z ≫ i = y` is equivalent to the
  fixedness condition. Unique lifts express identification by the inclusion,
  with no separate choice of bijection. Monicity of a closed immersion makes
  uniqueness equivalent to existence here. The identification is natural:
  for f, a lift z restricts to `algSpec.map f.op ≫ z`, whose composite with i
  is the restriction of y by associativity; uniqueness determines that lift.
- Restricted action equals projection: `(G ◁ i) ≫ ModObj.smul (M := G) (X := Y)
  = snd G F ≫ i`, an equality of scheme morphisms over k on G times F.
- Every k-scheme W and map u: `∀ (W : Over (Spec (.of k))) (v : W ⟶ Y)`.
  The equivalence `(∃ w : W ⟶ F, w ≫ i = v) ↔
  (G ◁ v) ≫ ModObj.smul (M := G) (X := Y) = snd G W ≫ v`
  is exactly factorization if and only if invariance as morphisms.
- Products are the existing cartesian products in `Over (Spec k)`, whose
  underlying schemes are the recorded `Limits.pullback`. `G ◁ v` is
  id_G times v and `snd` is the second projection. The formulas therefore
  retain the node's specified fibre products, not products over Spec Z.
- No smoothness or reducedness is assumed for G, Y, A, A', F or W. No
  finite-type or separatedness assumption is made on test schemes W or algebras.
  Algebras and schemes live in the same explicit universe u as the base, so
  quantification includes the identity algebra and is not vacuous for a large k.

Recorded statement dependencies used, with source declarations read:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, line 180.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp, lines 41–48. The recorded note and
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, module documentation,
  explicitly specialize this to `Over (Spec k)`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, lines 39–46, and
  `AlgebraicGeometry.QuasiCompact`, Morphisms.QuasiCompact, lines 37–46.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme, lines 35–49 and 72–75.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion, lines 42–46.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, lines 94–115;
  its `Over` cartesian realization is
  Mathlib.CategoryTheory.Monoidal.Cartesian.Over, `cartesianMonoidalCategory`,
  `tensorObj_left`, `snd_left` (lines 36–42, 66, 88).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, lines 469–480; the existing
  `AlgebraicGeometry.algSpec` in Mathlib.AlgebraicGeometry.Group.Affine,
  lines 71–74, is this same spectrum functor on algebras over k.
- `def-weil-pbc-algebra-hom-quotient`: its `mathlib_match` supplies `AlgHom`,
  Mathlib.Algebra.Algebra.Hom, lines 29–33. The `CommAlgCat` homs are precisely
  these algebra homomorphisms. The quotient-ideal clauses are not used here.

Other existing interfaces read: `ModObj` and both action laws in
Mathlib.CategoryTheory.Monoidal.Mod, lines 67–79; the induced action and
precomposition law in Monoidal.Cartesian.Mod, `Hom.smul`, `Hom.mulAction`,
`ModObj.comp_smul`; `IsSeparated` in Morphisms.Separated, lines 42–46.
All statement interfaces are public imports, directly or transitively.

Proof imports retain the staged plan: the recorded
`AlgebraicGeometry.existsUnique_constantSource_closedFactorizationLocus` from
Sheaf.AlgebraicGeometry.ConstantSourceClosedFactorizationLocus (full source and
signature read); `Scheme.isBasis_affineOpens` from
Mathlib.AlgebraicGeometry.AffineScheme; `Scheme.Cover.glueMorphisms` and
`Scheme.Cover.hom_ext` from Mathlib.AlgebraicGeometry.Gluing; and
`IsClosedImmersion.iff_isProper_and_mono` from
Mathlib.AlgebraicGeometry.ZariskisMainTheorem. The finite-type composition and
base-change instances and the closed-immersion base-change instance are in
the already imported Mathlib morphism modules. No proof dependency is restated.

Edge cases checked mathematically:

- The trivial group or trivial action gives F = Y and the identity inclusion.
- Empty Y gives empty F; the algebra and arbitrary-scheme tests agree. The
  zero algebra is allowed: its spectrum is empty, all point sets are singletons,
  and its unique point lifts, including when F is empty.
- Scaling of A1 by G_m gives the origin as a scheme: testing the universal
  invertible coordinate forces the coordinate of y to vanish.
- Scaling by nonreduced mu_p in characteristic p also gives the origin.
  Over B[epsilon]/(epsilon^p), the universal element 1+epsilon forces
  epsilon*y = 0, hence y = 0 coefficientwise. Testing only geometric points
  would miss this, and is explicitly avoided by the statement.
- Translation of A1 by alpha_p has empty fixed scheme: the universal nilpotent
  translation is nonzero over each nonzero test algebra. The zero algebra still
  has its required unique point of the empty scheme.
- Arbitrary, nonaffine, nonreduced and non-finite-type W are retained by the
  `Over` binder with no instances on W. The factorization statement is global
  equality of morphisms; affine-chart testing glues it as in proof steps 2–3.

Searches actually run using `batch2/msearch.py` for Q15 and this item:

- LeanFinder: "The fixed point functor of a finite type group scheme acting
  on a separated scheme is represented by a closed subscheme". Eight hits,
  including FintypeCat action Galois categories, `Rep.invariantsFunctor_obj_carrier`
  and `FixedPoints.isSeparable`; none is the claimed scheme representability.
- Loogle: `"fixed", "Scheme"`. Zero hits.
- Mathlib grep: `fixedSubscheme|universalFixed|fixedPoint` in AlgebraicGeometry.
  Zero hits.
- LeanSearch: "The universal fixed point functor for a group scheme action
  on a separated scheme is a closed subscheme". Eight hits, including
  `FixedPoints.subalgebra`, `FixedPoints.mem_subgroup`, `MulAction.fixedPoints`
  and variants; these define ordinary fixed sets, not universal scheme points.
- Direct rg searches of `lean/WeilConjectures` for the node id found no hit.
  Searches of Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`
  for the proposed theorem name found no duplicate.
- Searches of WeilConjectures/AlgebraicGeometry and Sheaf/AlgebraicGeometry
  for fixed-subscheme and universal-fixed-point terminology found
  `SchemeActionFixedIdeal` (an abstract subgroup of Aut X, not a group scheme),
  `TorusFixedSchemeSmooth` and `TorusFixedLocalIdealJets` (both assume a fixed
  representing scheme or concern special torus actions). Their signatures and
  documentation were read; none states general existence. Mathlib's `ModObj`
  already gives the action notion, so no new definition node is necessary.

There is no statement correction, disputed statement, new node or dependency repair.
The first compile exposed an inference ambiguity at an unqualified `ModObj.smul`;
both occurrences now specify `(M := G) (X := Y)` without changing the statement.
Validation uses scompile.py for this single module, followed by deliver2.py dry run.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
