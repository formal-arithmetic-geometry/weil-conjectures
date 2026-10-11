## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectSupportedMapLift` states
`AlgebraicGeometry.Scheme.exists_perfect_supported_map_lift`; its sole proof is `sorry`.
No definitions, dependency modules, or new nodes are needed. The node is unchanged
except for its `lean` record.

Source checked: https://stacks.math.columbia.edu/tag/09IM, Lemma 36.13.11.
The local literature checkout contains the citation lists but not perfect.tex, so the
full statement and proof were read on the Stacks website. Its retro-compact complement
condition agrees with the node's quasi-compact complement on a qcqs scheme: intersections
of quasi-compact opens are quasi-compact, and X itself is quasi-compact.

Hypothesis and conclusion correspondence:

- X a scheme: `(X : Scheme.{u})`, the recorded def-pc-scheme declaration.
- X quasi-compact: `[CompactSpace X]`; X quasi-separated: `[QuasiSeparatedSpace X]`.
- U an open subset: `(U : X.Opens)`; U quasi-compact: `hU : IsCompact (U : Set X)`.
- T a closed subset: `(T : Set X) (hT : IsClosed T)`; quasi-compact complement:
  `hTc : IsCompact Tᶜ`.
- E in D_QCoh(O_X): `(E : schemeDerivedQCohCategory X)`. The full-subcategory
  underlying object is `E.obj`, and its property is precisely quasi-coherent cohomology.
- P in D(O_U): `(P : schemeDerivedCategory U.toScheme)`; perfectness:
  `hP : IsPerfect U.toScheme P`, using the recorded dependency, with all its open-site
  derived-category binders supplied explicitly.
- P supported on T intersect U: `hPT` says for every integer n and point x of U,
  `x.val ∉ T` implies `Subsingleton` of the additive-group stalk of H^n(P).
  Points of U already lie in U, so this is precisely support contained in T intersect U.
  The underlying presheaf is `.val.presheaf` for a `SheafOfModules`, without the
  category instance for the separately packaged `Scheme.Modules` carrier.
- Alpha a map P → E|_U: the `α` binder uses the derived functor of
  `SheafOfModules.overFunctor` followed by `Scheme.Modules.overEquiv U`'s functor.
  This transports localized-site module sheaves to the open subscheme's module sheaves.
  The exact same composite restricts R and beta everywhere in the conclusion.
- A global R and beta: `∃ (R : schemeDerivedCategory X) (β : R ⟶ E.obj)`.
- R perfect: `IsPerfect X R`; R supported on T: every cohomology stalk at x outside T
  is `Subsingleton`, with the same vanishing convention as for P.
- P a direct summand of R|_U: maps `ι : P ⟶ R|_U` and `π : R|_U ⟶ P` satisfy
  `ι ≫ π = 𝟙 P`. This is the usual retraction criterion, with no chosen complement
  or extra object imposed on the input.
- Compatibility with alpha and beta|_U: `ι ≫ restriction.map β = α`. Thus the map
  on the identified summand is exactly the prescribed alpha.

Dependency declarations read with their full signatures and docstrings:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- def-pc-derived-category: `Sheaf.AlgebraicGeometry.DerivedCategory`, declarations
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`, and
  `schemeDerivedQCohCategory`.
- def-pc-perfect-complex: `Sheaf.AlgebraicGeometry.PerfectComplex`, declarations
  `AlgebraicGeometry.Scheme.IsStrictlyPerfect`, `IsPerfect`, and `perfectSubcategory`.
  Importing PerfectComplex imports the other two dependency modules transitively.
- The restriction transport is Mathlib's `Scheme.Modules.overEquiv`; its signature and
  docstring in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean were read. The derived
  composite uses the same form as the landed `QcOpenDerivedLift` and
  `AffinePseudoCoherentLift` statements, retaining the shared SheafOfModules category.

The `HasDerivedCategory.{w}` binders provide the localization choices for X, U, and
all opens used by the recorded perfectness predicate, rather than mathematical
finiteness assumptions. Universes u and w are explicit, and autoImplicit is false.
Local typeclass attributes supply additivity and exactness of the composite restriction
from the existing exactness instances; no new instance or theorem is declared.

Edge cases checked before writing: empty X or U is allowed (no Nonempty binder);
P = 0 and E = 0 are allowed; T = empty forces all cohomology stalks of P and R to
vanish, whereas T = X imposes no stalk condition. No lower or upper cohomology bound,
Noetherian assumption, characteristic condition, or connectedness condition is added.
Every cohomology degree is quantified over ℤ. A zero additive-group stalk is expressed
by Subsingleton, not IsZero on a bare Type. Compatibility is with the inclusion of the
summand and does not impose a condition on the complementary summand.

Searches for an existing theorem (all remote service searches recorded by msearch.py):

- LeanFinder: "A morphism from a perfect complex on a quasi compact open to a quasi
  coherent derived object lifts globally with closed support as a direct summand".
  Eight hits, on derived-category fraction factorizations and boundedness, no match.
- LeanSearch: "perfect complex supported on closed subset lift morphism from open".
  Service unavailable (Internal Server Error), recorded as unavailable.
- Loogle: `IsPerfect, DerivedCategory`: zero hits, unknown identifier IsPerfect.
- Mathlib grep: `perfect.*support|support.*perfect|lift.*perfect`: nineteen unrelated
  hits on perfect rings, fields, Witt vectors and graph matchings, no theorem match.
- Source project and lean/Sheaf grep: `lem-sc-perfect-support-map-lift|perfect.*support|
  support.*perfect`: only unrelated etale coefficient perfectness and a field-theory
  support argument, no matching statement.
- Source-name index, Mathlib, WeilConjectures and lean/Sheaf grep for
  `exists_perfect_supported_map_lift|lem-sc-perfect-support-map-lift`: no declaration.
- Searched the existing derived/perfect modules for support and restriction, and read
  QcOpenDerivedLift, AffinePseudoCoherentLift and Mathlib Modules/Sheaf for the existing
  open restriction equivalence. Support is expressed inline by cohomology-stalk
  vanishing, following the standing module-support convention, so no second support
  definition is introduced.

No statement dispute or correction. The docstring carries all four proof steps and
names the three non-elementary proof dependencies, including the replacement-isomorphism
compatibility needed for gluing. Server compilation and delivery preflight are run as
required; independent second reading is reserved for the next worker.

## Second reading by M1

I independently read the node statement, Tag 09IM (Lemma 36.13.11), the three
statement dependencies, and `PerfectSupportedMapLift.lean`. The correspondence is:

- The scheme `X` is `(X : Scheme.{u})`, with `[CompactSpace X]` and
  `[QuasiSeparatedSpace X]`; these are exactly the quasi-compact and quasi-separated
  hypotheses.
- The quasi-compact open is `(U : X.Opens)` with
  `hU : IsCompact (U : Set X)`.
- The closed subset and quasi-compact complement are `(T : Set X)`,
  `hT : IsClosed T`, and `hTc : IsCompact Tᶜ`, matching the retro-compact complement
  on the qcqs scheme.
- `E` is an object of `D_QCoh(O_X)`, represented by
  `(E : schemeDerivedQCohCategory X)` and targeted by `E.obj`.
- `P` is an object of `D(O_U)`, represented by
  `(P : schemeDerivedCategory U.toScheme)`, with `hP : IsPerfect U.toScheme P`.
  The explicit derived-category instances for `X`, `U`, and all open restrictions are
  the localization data required by the recorded `IsPerfect` definition.
- `hPT` quantifies every `n : ℤ` and point `x : U.toScheme`; when `x.val ∉ T`,
  the stalk of the corresponding homology sheaf is `Subsingleton`. This is support
  contained in `T ∩ U` under the project's stalk-vanishing convention.
- `α` has source `P` and target the derived restriction of `E.obj`, formed by
  `SheafOfModules.overFunctor` followed by `Modules.overEquiv U` and
  `mapDerivedCategory`, exactly the restriction `E|_U`.
- The conclusion existentially introduces `R : schemeDerivedCategory X` and
  `β : R ⟶ E.obj`; it requires `IsPerfect X R` and the analogous stalk vanishing
  outside `T` for every integer degree and point of `X`.
- The final existential maps `ι : P ⟶ R|_U` and `π : R|_U ⟶ P`; the clauses
  `ι ≫ π = 𝟙 P` and `ι ≫ (β|_U) = α` express the direct summand and its
  compatibility with `α` and `β|_U` in the same quantifier order as the node.

No mismatch was found. The source has no Noetherian, characteristic, connectedness,
nonempty, or cohomological-boundedness hypothesis, and the Lean statement adds none.
The empty scheme and empty open, zero `P` or `E`, empty `T`, `T = X`, and all degrees
(including degree zero) remain admitted. `Subsingleton` is used for stalk vanishing,
so no invalid `IsZero` assertion on a bare type is introduced. The support condition
for an empty `T` forces vanishing outside it, while `T = X` imposes no pointwise
condition, as required.

I searched Mathlib, the slopmaster2 source, and this project's `lean/Sheaf` tree for
`exists_perfect_supported_map_lift`, `perfect.*support`, and `support.*perfect`; no
matching declaration exists. LeanFinder and Loogle searches likewise found only
unrelated perfect-ring/perfection results, and LeanSearch was unavailable. The
recorded dependency declarations (`schemeDerivedQCohCategory`, `schemeDerivedCategory`,
`IsPerfect`, and `Modules.overEquiv`) were opened and agree with their uses. The module
compiled cleanly with `scompile.py`; no repair was needed.
