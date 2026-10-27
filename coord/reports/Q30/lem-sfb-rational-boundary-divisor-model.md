## Worker report

The delivery states `AlgebraicGeometry.exists_rational_boundary_divisor_model` in
`Sheaf.AlgebraicGeometry.RationalBoundaryDivisorModel`. Its only theorem has proof
`sorry`; it introduces no definitions, auxiliary theorems, or axioms. The node's
statement and dependencies are unchanged. The module docstring identifies the
source, and the theorem docstring includes all seven DAG proof steps and their
citations.

The statement uses ordinary Mathlib objects rather than a new rational-action
interface. `Over (Spec (.of k))` retains every scheme's specified k-structure.
The cartesian tensor on this category has underlying scheme
`pullback G.hom X.hom`; its projections and induced maps are the specified scheme
fibre-product constructions. No point-set product replaces a scheme product.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| k algebraically closed field | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Schemes and maps over k | Objects and arrows of `Over (Spec (.of k))` |
| G group scheme, with its actual unit, multiplication, inverse | `[GrpObj G]`; inversion is `(GrpObj.inv (X := G)).left` |
| G smooth integral separated of finite type | `[Smooth G.hom] [IsIntegral G.left] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| X₀ integral normal proper | `[IsIntegral X₀.left] [IsProper X₀.hom]` and `hX₀`, integrally closedness of every stalk; integrality supplies the domain instances |
| Y smooth separated finite type, with regular G-action | `[Smooth Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [ModObj G Y]`; the action object contains the morphism and unit/associativity laws |
| Y dense open in X₀ | `j : Y ⟶ X₀`, `[IsOpenImmersion j.left]`, `hj : DenseRange j.left` |
| E₀ nonempty | `hE : (Set.range j.left)ᶜ.Nonempty` |
| Every irreducible component of E₀ has codimension one | `hcodim` quantifies over `irreducibleComponents` of the boundary subtype and its ambient generic point η, requiring `ringKrullDim (X₀.left.presheaf.stalk η) = 1` |
| Existence of normal integral proper X | Existential `X` with `IsIntegral X.left`, `IsProper X.hom`, and integrally closedness of every stalk |
| Proper birational b, isomorphism over Y | `b : X ⟶ X₀`, `IsProper b.left`, and `IsPullback jX.left (𝟙 Y.left) b.left j.left`; `jX` is a dense open immersion, so this also explicitly supplies the dense isomorphism opens witnessing birationality |
| Identify Y with b⁻¹Y | The same pullback square, with the identity map on Y |
| Integral closed subscheme D of the boundary | `D : Over (Spec (.of k))`, `d : D ⟶ X`, `IsIntegral D.left`, `IsClosedImmersion d.left`, and the range inclusion in the complement of `jX` |
| dim D = dim X₀ − 1 | `topologicalKrullDim D.left + 1 = topologicalKrullDim X₀.left`; over a field finite-type integral schemes have finite nonnegative dimensions, so this is exactly the predecessor equation, avoiding truncated subtraction on extended dimensions |
| Rational extension α of the Y-action, on maximal domain U | `a : (G ⊗ X).left.PartialMap X.left`, `a.domain = a.toRationalMap.domain`; the equations for `v` identify the whole G×Y inside U and identify the restriction of `a.hom` with the specified action followed by jX |
| α is over k | `a.hom ≫ X.hom = a.domain.ι ≫ (G ⊗ X).hom` |
| U_D = U ∩ (G×D), dense open in G×D | `t.domain = (G ◁ d).left ⁻¹ᵁ a.domain`; `PartialMap.domain` is open and `PartialMap.dense_domain` supplies density |
| Restriction of α factors through D | `m` is the uniquely pinned morphism of domain opens, with `m ≫ a.domain.ι = t.domain.ι ≫ (G ◁ d).left`; the equation `t.hom ≫ (snd G D).left ≫ d.left = m ≫ a.hom` is the factorization, with factor map `t.hom ≫ (snd G D).left` |
| τ(g,x) = (g⁻¹, α(g,x)) | The previous equation specifies its second coordinate, and the first-projection equation specifies inversion of g, as equalities of scheme morphisms |
| τ rational birational involution | `t` is a partial self-map on exactly U_D; the subsequent nonempty open W and self-isomorphism f, agreeing with t and squaring to the identity, witness both birationality and the rational involution identity |
| Nonempty W contained in U_D, τ restricts to W ≅ W, τ² = id | `W`, `hW`, `f`, nonemptiness, the restriction equation for `f.hom`, and `f.hom ≫ f.hom = 𝟙 W.toScheme` |
| dim X = dim X₀ | `topologicalKrullDim X.left = topologicalKrullDim X₀.left` |

The symbol α₀ in the prose introduces the unique rational extension on X₀ and is
not an extra hypothesis or part of the conclusion. The theorem directly takes
the action from which it is determined; no assumption of extendibility is added.
Similarly α on X is specified by its maximal representative and its restriction
on the dense open G×Y. Density follows from the given dense open immersion and
flatness over a field. For integral finite-type schemes over the algebraically
closed field the product G×D is integral; hence the nonempty open W is dense.
Consequently its involutive isomorphism has precisely the stated rational-map
meaning, including dominance. These are equivalences of encodings, not extra
assumptions or postponed helper theorems.

Dependency declarations read and reused:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, the recorded match's component for
  algebraic closedness. No algebraic closure of another field is part of this node.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` and
  `AlgebraicGeometry.IsSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`. Properness includes separatedness
  and local finite type, and universal closedness gives quasi-compactness.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to schemes over Spec k,
  as specified by the node's recorded note. `ModObj` in
  `Mathlib.CategoryTheory.Monoidal.Mod` supplies its regular action.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its projections in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, through
  `CategoryTheory.Over.cartesianMonoidalCategory` and its explicit `tensorObj_left`
  equation in `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`.

Every currently recorded project/upstream proof dependency is imported privately.
Proof-only Mathlib dependencies for Noetherianness, closed points and residue
fields are also imported. The still unstated proof nodes
`lem-sfb-algclosed-integral-product`, `lem-sfb-smooth-normal-ascent`,
`lem-sfb-rational-action-domain-laws`, and
`lem-sfb-prime-divisor-image-extraction` have no modules to import. None is needed
to elaborate this statement; their future proofs are described and cited in the
docstring. No import cycles were encountered.

Edge cases checked: the empty scheme and empty Y are excluded by integral X₀
and density; the boundary-empty case is excluded exactly by hE; dimension zero
cannot satisfy the nonempty codimension-one boundary assumption. For curves D
has dimension zero, with the displayed successor equation reading 0+1=1.
The trivial connected group is allowed and yields the identity involution. No
positive group dimension, faithfulness, transitivity, projectivity, characteristic
restriction, regular action on all of X, or normality/smoothness of D is imposed.
The characteristic is arbitrary. All scheme and field universes are explicitly
bound by `universe u`, and `set_option autoImplicit false` checks every binder.

Searches made using the prescribed msearch wrapper:

- LeanFinder: “A rational group scheme action on a normal proper variety has a
  birational model with an invariant boundary prime divisor”: eight hits,
  including RationalMap.exists_rep and unrelated group-action results; no match.
- LeanSearch: “A proper birational model with an invariant boundary divisor for a
  rational algebraic group action”: eight abstract action/invariant-ring hits;
  no scheme theorem matching this node.
- Loogle: `AlgebraicGeometry.Scheme.PartialMap, CategoryTheory.MulAction`:
  zero hits, latter identifier unknown. Follow-up `CategoryTheory.ModObj`:
  twelve hits including the existing internal action object and its action map.
- Mathlib grep: `rational.*action|boundary.*divisor|structure.*Action` under
  AlgebraicGeometry: one unrelated ProjectiveSpectrum documentation hit.
- Project rg over WeilConjectures and Sheaf for
  `RationalAction|rationalAction|rational_action|BoundaryDivisor|boundary_divisor|RegularAction|SchemeAction`:
  rational maps, boundary-divisor results about curves, and the existing scheme
  action groupoid interfaces; no invariant boundary divisor model theorem.
- Project rg for the item's id in WeilConjectures: no match. Exact proposed
  declaration/module names were checked against WeilConjectures, Sheaf and
  dag/lean_names_upstream.json: no match.

Read the source at https://arxiv.org/html/1311.6060v2, Lemma 4.4 and the proof of
Proposition 4.1, especially the extraction of D, its invariance and the birational
involution. The archived node's seven-step proof supplies the detailed
normalization, codimension-one and common invariant open justifications.
No statement correction or STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled both the sandbox probe and the module against
the live published build with no errors or unexpected warnings. All validation
uses the prescribed wrapper; no local or global lake build was run.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
