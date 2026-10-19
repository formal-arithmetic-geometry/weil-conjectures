## Worker report

Item: `lem-a1-affine-groupoid-polynomial-norm-invariant`, group Q57, stage 2.
The module `Sheaf.AlgebraicGeometry.AffineGroupoidPolynomialNormInvariant` states
`AlgebraicGeometry.affine_groupoid_polynomial_norm_invariant`. Its only theorem proof
is `sorry`. There are no new definitions, new nodes, dependency repairs, or statement
corrections.

Source read: `literature/stacks-project/groupoids.tex`, section finite flat groupoids,
`lemma-determinant-trick` (Tag 03BH), its proof, and the second paragraph of
`lemma-integral-over-invariants`, which forms the polynomial-coordinate groupoid.
Also read `literature/stacks-project/exercises.tex`, `exercise-trace-det-rings`
(Tag 02DV), clauses (1) and (3), defining the local determinant norm and its base change.
The proposed statement agrees with these sources. No disputed statement was found.

Hypothesis and clause matching:

- The rings are `A B : CommRingCat.{u}`; the schemes are exactly `Spec A` and `Spec B`.
  No field, reducedness, nontriviality, or Noetherian assumption is imposed.
- The source and target are `s t : Spec B ⟶ Spec A`; the identity and inverse are
  `e : Spec A ⟶ Spec B` and `i : Spec B ⟶ Spec B`. The composition is precisely
  `c : pullback s t ⟶ Spec B`, with the order of the two factors in the node.
- `hgroupoid` quantifies over every `H : Scheme.{u}`. It supplies a Mathlib
  `Groupoid.{u} (H ⟶ Spec A)` and equivalences `φ x y` identifying its hom sets with
  `{r : H ⟶ Spec B // r ≫ s = x ∧ r ≫ t = y}`. These equivalences ensure that all
  scheme arrows, including all stabilizer arrows, occur, with exactly their given
  source and target. No equivalence-relation or monomorphism assumption is used.
- The first conjunct of `hgroupoid` identifies categorical identity with `x ≫ e`.
  The second identifies categorical inverse with postcomposition by `i`. The last
  identifies `f ≫ g` with `pullback.lift (φ y z g).val (φ x y f).val ... ≫ c`.
  This reversed order of the pair is required: `s(g) = y = t(f)`. The equality fed to
  `pullback.lift` comes directly from the two subtype properties. Associativity and
  the two identity and inverse laws are the actual laws of `Groupoid`, transported
  along `φ`. Conversely, a groupoid on the indicated arrows supplies these witnesses
  by using the displayed subtype as its hom type. Thus the existential structure does
  not impose a further mathematical assumption.
- Functoriality in test schemes is inherent in these operations: precomposition
  preserves source/target, commutes with `e` and `i`, and commutes with composition
  by the universal property of `pullback.lift`. Arbitrary choices of `φ` do not change
  the operations on the scheme arrows, which the three conjuncts prescribe.
- Finite local freeness of both maps is exactly `[s.IsFiniteLocallyFree]` and
  `[t.IsFiniteLocallyFree]`, using the recorded upstream definition. It means finite,
  flat, and locally of finite presentation, and supplies no fixed degree.
- `σ` and `τ` are `(Spec.homEquiv s).hom` and `(Spec.homEquiv t).hom`.
  The coefficient maps fixing the indeterminate are `Polynomial.mapRingHom` of
  those ring homomorphisms. The polynomial source morphism used in the chart formula
  is exactly `Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ))`.
- `F : Polynomial A` is arbitrary. `Q : Polynomial A` names the norm polynomial.
  Instead of choosing a norm function, `hQ` gives the defining local determinant
  formula for this particular `Q`. It says that every point of `Spec A[T]` has an
  affine open neighbourhood `V` on which the section algebra of the polynomial
  source map is finite free, and the restriction of `Q` equals `Algebra.norm` of
  the restriction of `Polynomial.map τ F`. `Scheme.ΓSpecIso.inv` is the canonical
  conversion from a polynomial to the corresponding global section. Restrictions
  are the actual structure-presheaf maps. Every chart uses the algebra induced by
  the polynomial source map's `app V`, including in the explicit `Module.Free`,
  `Module.Finite`, and `Algebra.norm` terms.
- This is the local norm characterization in the recorded norm-charts theorem with
  `W = ⊤`, expressed directly on global sections of spectra. Requiring it of `Q`
  introduces no global freeness or rank restriction. Existence follows from that
  dependency after polynomial base change of `s`; uniqueness follows by refining
  intersections of free affine charts and restricting their determinant formulas,
  then using separatedness of the structure sheaf. Hence universal quantification
  over `Q` satisfying `hQ` is exactly an assertion about the norm specified by the
  node. It does not substitute an arbitrary map for the canonical norm, nor choose
  data from an undetermined existence theorem. In particular `hQ` contains no
  invariance assertion.
- The conclusion is exactly `Polynomial.map σ Q = Polynomial.map τ Q`, the equivalent
  formulation explicitly offered in the node. By equality of coefficients this
  means each coefficient lies in the equalizer `C = {a | σ a = τ a}`; equivalently,
  `Q` belongs to the image of `C[T] → A[T]`. No definition of a second invariant
  subring is necessary.

Dependency declarations and interfaces read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`, and `Scheme.ΓSpecIso`; the full definitions
  and their docstrings were read.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.homEquiv`, the equivalence
  from affine scheme maps to coordinate ring maps; the signature and docstring
  were read, including its inverse `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, and `pullback.lift`; the full signatures and docstrings were read.
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies existence in schemes.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` (and the adjacent fixed-degree definition was
  inspected to ensure it is not assumed).
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, with coefficients stored as
  `AddMonoidAlgebra R ℕ`. `Mathlib.Algebra.Polynomial.Eval.Defs`: `Polynomial.map`
  and `Polynomial.mapRingHom`, with the fixed-variable coefficientwise formulas.
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeNormCharts`:
  `exists_finiteLocallyFree_norm_charts`; its complete signature and proof docstring
  were read. It gives local free charts and the glued norm without global freeness.
  The module is publicly imported because the statement uses its norm convention.
- `Mathlib.LinearAlgebra.Determinant`: `LinearMap.det`; its full definition and
  docstring explain the finite-basis determinant and the fallback for modules
  without finite bases. `Mathlib.RingTheory.Norm.Defs`: `Algebra.norm` and
  `Algebra.norm_apply` identify the chart norm with this determinant. The free
  and finite chart clauses prevent use of the fallback on a nonfree global module.
- `Mathlib.CategoryTheory.Groupoid`: `CategoryTheory.Groupoid`, including inherited
  category laws and inverse laws. Its operation signatures were inspected before
  writing the explicit-instance terms.

The proof dependency `lem-a1-affine-groupoid-invariant-norm` has neither a recorded
Lean declaration nor a Mathlib match in the shared DAG inspected for this delivery.
Its statement was read and the module docstring records its role in the proof plan.
It is not needed to type this statement and no unavailable module is imported.

Edge cases checked mathematically: the zero polynomial and constant polynomials
have no restrictions; empty spectra/zero rings are allowed and the chart condition
on an empty base is vacuous with a unique global section; a nonempty object scheme
has nonempty source fibres because `e` is a source section, but no such nonemptiness
is imposed as a binder; stabilizers are retained by the full arrow subtype; mixed
rank on disconnected bases is allowed by pointwise free charts; nilpotent elements
are retained in the coefficient ring and equality is ring equality, not equality
only on geometric points; `F` need not be monic or have positive degree. All
universes and theorem binders are explicit. Test schemes use the universe of the
spectra, which suffices for the groupoid laws by Yoneda and permits any universe
through `u`.

Searches performed before writing:

- `msearch.py ... leanfinder` with “In a finite locally free affine scheme groupoid
  the determinant norm along source of a target polynomial is invariant”: eight
  hits, including `Algebra.norm_eq_matrix_det` and norm transitivity calculations;
  no scheme-groupoid norm invariance statement.
- `msearch.py ... leansearch` with “Finite locally free algebra norm as a glued
  section, invariant under an affine groupoid”: eight hits, including
  `Algebra.norm_localization`, `Algebra.norm`, and group-action invariant algebra
  results. Localization of a globally free algebra and invariant group actions do
  not state this lemma.
- `msearch.py ... loogle` with `Algebra.norm, Polynomial.map, Groupoid` reported an
  unknown identifier for unqualified `Groupoid`; the corrected search
  `"norm", "invariant"` returned six unrelated analytic or modular-form norms.
- `msearch.py ... grep` with `groupoid.*norm|norm.*groupoid|structure.*Groupoid`
  found normal subgroupoid and differential geometry declarations, no affine
  scheme groupoid norm theorem.
- Direct `rg` on the upstream `WeilConjectures/AlgebraicGeometry` for groupoids
  and norm sections, direct grep of the item id throughout upstream
  `WeilConjectures/`, and `rg` of the chosen declaration name in Mathlib,
  upstream, and `lean/Sheaf/` found no existing declaration.
- `rg` of `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/Paper` found the recorded
  norm-charts theorem and the affine relation invariant-subring construction in
  `FiniteFlatAffineRelationQuotient`. The latter is unnecessary for the node's
  explicit equivalent conclusion and does not supply this theorem. A DAG scan of
  definition-node statements found no scheme-groupoid definition; using the actual
  Mathlib `Groupoid` with explicit hom equivalences avoids introducing a new notion.

## Second reading by Q57

This is the author's self-check under the dispatcher's direct-delivery instruction;
the maintainer supplies the independent review. I reopened the node and Lean file
and checked all five maps and their domains, the order of the composable pair,
finite local freeness of both maps, arbitrary polynomial `F`, source rather than
target algebra structure on every norm chart, target rather than source image of
`F`, the canonical global-sections identifications, and the source/target equality
of `Q`. The displayed conclusion is the node's explicitly equivalent conclusion.
The only interpretive detail is that the norm polynomial is an explicitly bound
`Q` with its full local determinant characterization; the existence and uniqueness
argument above explains why this is the specified norm, including variable-rank
cases. No source-statement correction was needed. The proof remains `sorry`.
