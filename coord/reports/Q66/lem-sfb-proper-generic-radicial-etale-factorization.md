## Worker report

Stated `AlgebraicGeometry.Scheme.Hom.exists_generic_radicial_etale_factorization` in
`Sheaf.AlgebraicGeometry.Morphisms.GenericRadicialEtaleFactorization`.
The only theorem has proof `sorry`; no definition or theorem was proved, no new
notion was introduced, and the original DAG statement and dependencies are unchanged.
The docstring contains all seven original natural-language proof steps and their
named dependencies. Already recorded proof modules are imported non-publicly.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`. The schemes are `{X S : Scheme.{u}}`.
  `[IsIntegral X] [IsIntegral S]` includes nonemptiness, reducedness and irreducibility.
- The k-scheme structures are the actual maps `pX` and `pS` to
  `Spec (CommRingCat.of k)`. `[IsSeparated pX] [IsSeparated pS]` expresses
  separatedness over k. For each structure map, `LocallyOfFiniteType` and
  `QuasiCompact` together express finite type, without imposing properness over k.
- `(f : X ⟶ S)` and `(hf : f ≫ pS = pX)` express the specified k-morphism.
  `[IsProper f] [IsDominant f]` are exactly properness and dominance.
- `hfinite` is `FiniteDimensional S.functionField X.functionField` for the
  module underlying `Scheme.Hom.dominantFunctionFieldAlgebra f`. This is the
  canonical generic stalk map, rather than an arbitrary field algebra.
- The first conclusion is `Surjective f`.
- The open subscheme is `U : S.Opens`, with `(U : Set S).Nonempty`,
  `Dense (U : Set S)` and `IsAffineOpen U`. Its inclusion is the canonical `U.ι`.
- `X₀` is the actual categorical fibre product `pullback f U.ι`, and its
  structure map `f₀` is `pullback.snd f U.ι`. The conclusion includes
  `IsFinite (pullback.snd f U.ι)`.
- `T : Scheme.{u}` with `hT : IsIntegral T`, `a : pullback f U.ι ⟶ T`, and
  `e : T ⟶ U.toScheme` supply the intermediate integral scheme and both arrows.
  `a ≫ e = pullback.snd f U.ι` is the factorization equation.
- `IsFinite a` and `(topologically IsHomeomorph).universally a` state that u
  is finite and a homeomorphism after every scheme base change.
- `IsFinite e ∧ Etale e ∧ Surjective e` supplies all three properties of e.
- `d : ℕ` with `1 ≤ d` is the positive degree. The actual structure-module
  pushforward is `(Scheme.Modules.pushforward e).obj
  (SheafOfModules.unit T.ringCatSheaf)`. Its
  `SheafOfModules.IsFiniteLocallyFreeOfRank ... d` says finite locally free of
  constant rank d, using the same module as the dependency's variable-rank notion.
- `d = @Module.finrank ...` states `[K_s:K]`, with K_s literally
  `@separableClosure S.functionField X.functionField ...
  (Scheme.Hom.dominantFunctionFieldAlgebra f)`. The explicit `Submodule.module`,
  `Subalgebra.toSubmodule` and `IntermediateField.toSubalgebra` arguments only
  supply the restriction of this canonical scalar action; no extra algebra is
  chosen or assumed.
- `φ : T.functionField ≃+* K_s` together with the equation for every `t` says
  precisely that k(T) is this subfield under the induced inclusions. Writing
  `j = pullback.fst f U.ι`, the equation is `j* (φ(t)) = a*(t)` in k(X₀).
  Thus this is an identification compatible with the actual maps into k(X),
  not just an abstract ring isomorphism. The factorization equation forces
  compatibility with the base K as well, by functoriality of generic stalk maps.
- `hX₀ : IsIntegral (pullback f U.ι)` and the equalities `hj`, `ha` that the
  generic points map to generic points permit these function fields and
  `functionFieldMap`s to be typed. These are consequences of restricting the
  integral source to the nonempty open and of the universal homeomorphism;
  they add no geometric restriction or independent choice of field inclusion.

Dependency declarations read and used:

- `Field` in `Mathlib.Algebra.Field.Defs`; `Algebra` in `Mathlib.Algebra.Algebra.Defs`.
- `AlgebraicGeometry.IsIntegral` in `Mathlib.AlgebraicGeometry.Properties`.
- `AlgebraicGeometry.IsProper`, `IsSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `AlgebraicGeometry.Scheme.Hom.dominantFunctionFieldAlgebra` in
  `Sheaf.TraceFormula.LocalDimensionFormula`: its complete definition uses
  dominance to identify generic points, then `functionFieldMap` and `toAlgebra`.
- `AlgebraicGeometry.Surjective` in `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `AlgebraicGeometry.IsOpenImmersion` in `Mathlib.AlgebraicGeometry.OpenImmersion`:
  the inclusion here is the existing open-subscheme inclusion `U.ι`.
- `AlgebraicGeometry.Spec`, `Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`.
- `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `AlgebraicGeometry.IsFinite` in `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `CategoryTheory.MorphismProperty.universally` in
  `Mathlib.CategoryTheory.MorphismProperty.Limits`, with
  `AlgebraicGeometry.topologically` in
  `Mathlib.AlgebraicGeometry.Morphisms.Constructors` and `IsHomeomorph`.
- `AlgebraicGeometry.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `separableClosure` in `Mathlib.FieldTheory.SeparableClosure`: its carrier is
  exactly the elements separable over the base field.
- `SheafOfModules.IsFiniteLocallyFree` and `IsFiniteLocallyFreeOfRank` in
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
  The latter refines the former by requiring every local basis to have d elements.
- Existing canonical constructions used with these notions:
  `Scheme.functionField` in `Mathlib.AlgebraicGeometry.FunctionField`,
  `Scheme.Hom.functionFieldMap` in
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, and
  `Scheme.Modules.pushforward` in `Mathlib.AlgebraicGeometry.Modules.Sheaf`.

Edge cases checked before writing: an empty X or S is excluded by integralness
as in the node; an empty U is explicitly excluded. A purely inseparable L/K
has K_s = K and d = 1, so e may be the identity. For L = K this includes the
birational case after shrinking. Separable extensions and characteristic zero
are included, with no characteristic binder. Neither source nor intermediate
scheme is required to be normal or regular. The universe u is shared by the
field and schemes, as for schemes over Spec k in this project; arbitrary u is
allowed. No finiteness of the set of k-points is assumed.

Searches for the full statement (2026-10-24):

- `msearch.py ... leanfinder` with query "A proper dominant morphism of integral
  finite type schemes with finite function field extension factors over a dense
  affine open as a finite universal homeomorphism and finite etale surjection":
  8 hits, including `finite_appTop_of_universallyClosed`, `IsFinite`,
  `IsIntegralHom`, and normalization/rational-map declarations. None states
  the dense-open separable-first factorization or its field/rank identification.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Etale, separableClosure`: 0 hits.
- `msearch.py ... grep` in `AlgebraicGeometry` with query
  `radicial.*etale|etale.*radicial|generically.*finite`: 0 hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `radicial.*[Ee]tale|[Ee]tale.*radicial|generic.*factor` and the item id:
  related spreading, rational-map, normalization and local-generic factor
  ingredients, but no declaration stating this assertion. Searching the final
  declaration name in those roots and `dag/lean_names_upstream.json` had no match.
- `rg` for module pushforwards and fixed-rank structure sheaves located
  `Scheme.Modules.pushforward` and the existing finite-locally-free-rank API,
  which are reused directly.

Source reading: Stacks `morphisms.tex`, lemma-generically-finite (02NW),
including the quasi-compact/quasi-separated hypothesis for (4);
`fields.tex`, lemma-separable-first (030K), lemma-primitive-element (030N);
`algebra.tex`, definition-standard-etale (00UB), lemma-standard-etale (00UC).
These agree with the node's seven-step assembly. No statement correction or
STATEMENT-DISPUTED issue was found.

Validation: single-file server compilation through the prescribed `scompile.py`.
The first probes diagnosed explicit scalar-action and pullback-type elaboration,
then a line-length warning; these were repaired in the delivered file.

## Second reading by Q66

A separate self-review reopened the node and final Lean signature clause by
clause; no additional agent was started, as the dispatcher explicitly forbids
that. The maintainer supplies the independent review of this delivery.

Checked every hypothesis: field, two nonempty integral schemes, their separated
finite-type k-structures, the k-morphism equation, properness, dominance and
finiteness over the canonical function-field map are all present. Checked every
conclusion: surjectivity, nonempty dense affine open, the actual pullback and its
finite projection, the integral intermediate scheme, factorization, finite
universal homeomorphism, finite etale surjection, positive constant sheaf rank,
canonical relative separable closure and its degree are all present.

In particular, the ring equivalence φ is constrained by the displayed generic
stalk equation; dropping that equation would lose the node's "under the induced
function-field inclusions" clause. No such clause is dropped. Explicit module
arguments are the inherited scalar action on this very intermediate field;
there is no unrelated field algebra or arbitrary map hypothesis. The auxiliary
integrality/generic-point witnesses are consequences of the stated geometry.
No mathematical mismatch was found and no DAG field outside `lean` was changed.
