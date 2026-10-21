## Worker report

The module `Sheaf.SixFunctors.FiniteProperClassicalTruncation` states
`AlgebraicGeometry.ProEtale.finiteProper_classical_truncation`, with `sorry` as its only
proof. It introduces no definitions and makes no statement correction. The node copy
changes only `lean`.

Hypothesis and conclusion correspondence:

- A finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`.
  No nontriviality, characteristic, or invertibility hypothesis is added.
- A proper scheme morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]`.
- The nonnegative dimension bound is `(e : ℕ)`. The hypothesis `_hbound` quantifies
  over every scheme `T`, map `g : T ⟶ Y`, and point `t : T`, and requires
  `topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞)`.
  This is the dimension of each scheme-theoretic fibre of each base change, including
  geometric fibres by taking algebraically closed field base changes.
- Arbitrary base change is `(S : Scheme.{u}) (g : S ⟶ Y)`; `X_S` is `pullback f g`
  and `f_S` is `pullback.snd f g`, using the recorded base-change conventions.
- The ordinary constant-A unbounded category is
  `Scheme.proEtaleDerivedCategory (pullback f g) A`. Its definition is the standard
  localization of all integer-indexed complexes of intrinsic constant-ring module sheaves.
  This is the published constant-ring presentation, with ULift coefficients, already used
  by the recorded ordinary pro-etale operations. It involves no completion and no
  boundedness or constructibility restriction. The dependency's continuous-function
  presentation `FiniteCoefficientModules` is imported and not redefined; its intrinsic
  commutative constant-ring presentation is the published category above.
- `_hJ : IsClassicalModuleComplex J` requires precisely classicality of every
  cohomology sheaf, using the recorded arbitrary-ring sheaf classicality predicate.
- `(m N : ℤ)` and `_hN : N < m - 2 * (e : ℤ) - 1` render the exact integer inequality.
- The canonical map is `(TStructure.truncGEπ DerivedCategory.TStructure.t N).app J`,
  the good truncation map of the standard t-structure, not a stupid truncation or an
  arbitrary morphism. Apply the total K-injective functor
  `Scheme.proEtaleConstantDerivedDirectImage (pullback.snd f g) A`, then
  `DerivedCategory.homologyFunctor _ m`, and assert `IsIso` of that specific map.
  The target of this homology functor is the abelian category of module sheaves on
  `S.ProEt`, so this is an isomorphism of the stated sheaves with their A action.
  Naturality is built into the map: it is the component of the good-truncation natural
  transformation after applying those two functors. For any morphism of classical
  complexes its square commutes by naturality and preservation of composition.
  Thus the inverse is natural as well; no arbitrary choice of an isomorphism is used.
- The quantifier order fixes `e` and its universal bound before choosing `S`, `g`, `J`,
  `m`, and `N`; the same bound and inequality therefore work for every base change.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: pullback/snd/fibre conventions
  documented with `AlgebraicGeometry.baseChange_fiber` and
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`; scheme fibre is Mathlib's
  `AlgebraicGeometry.Scheme.Hom.fiber`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, and the coefficient-ring construction, imported
  without a second definition. `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` gives
  the existing intrinsic commutative constant-ring presentation actually used here.
- `Sheaf.SixFunctors.ClassicalDefinition`: `IsClassicalModuleComplex`,
  `IsClassicalModuleSheaf`, whose definitions use the existing set-sheaf continuity
  predicate on the underlying module sheaf.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its resolution
  comparison and documented total-derived universal property.
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage` specializes the existing
  `Functor.rightDerivedFunctor` to the canonical constant-section module direct image,
  computed by K-injective resolutions. There is no bounded-below replacement here.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: documented good truncations
  on complexes and `DerivedCategory.TStructure.t`; the canonical derived-category map
  is Mathlib's `CategoryTheory.Triangulated.TStructure.truncGEπ`.

All already stated proof-dependency modules are imported without `public` when needed
only for the proof. `lem-sfb-finite-proper-classical-neighborhood-vanishing` has no Lean
record on the read base and is a proof dependency only; its future module import is
left to the maintainer after it is stated. No declaration needed for this statement
is missing. The docstring reproduces all four proof steps with their cited node ids.

Edge cases checked before writing: the zero ring is allowed and gives zero module
sheaves; an empty fibre has Krull dimension bottom and satisfies the bound; empty
`X` or `S` is not excluded; `e = 0` gives exactly `N < m - 1`; both degrees may be
negative; `J` can have nonzero cohomology in arbitrarily negative degrees. No
Noetherian, quasi-compact base, or finite-dimensional base condition is imposed.
The small site has object universe `u+1` and morphism universe `u`; no equality of
those universes is imposed. Finite coefficients in `Type u` lose no finite ring,
and all scheme base changes in the chosen scheme universe are quantified.

Searches actually run (2026-10-21):

- `msearch.py ... leanfinder`: "Proper direct image of an unbounded complex with
  classical pro-etale cohomology is unchanged in degree m by sufficiently negative good
  truncation uniformly after base change". Eight generic cochain/derived-category
  hits, including `CochainComplex.isIso_πTruncGE_iff`; no proper classical pro-etale
  direct-image statement.
- `msearch.py ... loogle '"truncGE"'`: twelve hits about generic shape embeddings and
  homological-complex truncations. These supply general truncation machinery, not
  this theorem.
- `msearch.py ... grep 'pro[Ee]tale.*trunc|proper.*[Cc]ohomological'`: zero Mathlib hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the exact node id: no hits.
  Concept searches for classical truncations and fibre bounds found
  `UnboundedClassicalTruncation`, which assumes an absolute sections bound and states
  a sections comparison, and existing relative-dimension/etale bounds. None states
  this proper direct-image sheaf comparison uniformly over all base changes.
  Its section cohomology theorem is a proof input, not an existing exact match.

Validation: `scompile.py O3 lem-sfb-finite-proper-classical-truncation` compiled the
module both as its sandbox module and its library module, cleanly (2.9 s and 2.2 s).
There is one named postponed theorem. No STATEMENT-DISPUTED flag or node fault.

## Second reading by O3

Worker self-check, recorded transparently: no second agent was started, as the
item brief prohibits starting agents and assigns independent review to the maintainer.
Re-read the node and final module together: the binder list preserves finite
commutative A, proper f, the universally quantified fibre dimension bound, arbitrary
S, classical cohomology of an unbounded J, and the strict integer inequality. The
conclusion applies homology to total direct image of the canonical good-truncation
map in its specified direction. No weaker existential isomorphism, arbitrary map,
boundedness hypothesis, or restriction to geometric points replaces a clause.
The naturality clause is supplied by the existing natural transformation, as explained
above. All universes and variables are explicitly bound. No mismatch was found and
no node changes beyond the Lean record were made. Maintainer review remains independent.
