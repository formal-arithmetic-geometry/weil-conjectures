## Worker report

The module `Sheaf.AlgebraicGeometry.ZeroDimensionalBaseAffineGlobal` states
`AlgebraicGeometry.proEtale_cohomology_vanishes_of_affine_of_zeroDimensional_base`.
The sole theorem has proof `sorry`; it introduces no definitions or axioms. The node's
statement and all its existing fields other than `lean` are unchanged.

Hypothesis and conclusion correspondence:

- The schemes are `{B X : Scheme.{u}}`. `[IsAffine B]` is exactly the affine-base
  condition. `hB : ∀ p : PrimeSpectrum Γ(B, ⊤), p.asIdeal.IsMaximal` says every prime
  of its coordinate ring is maximal. It permits nilpotents and the zero ring.
- `(g : X ⟶ B) [IsSeparated g]` gives the named separated structure map.
  `[LocallyOfFiniteType g] [QuasiCompact g]` is exactly finite type, using the
  conjunction recorded by `def-weil-finite-type-morphism`.
- `(e a : ℕ)` encodes the nonnegative integers. `he` quantifies over every
  `K : Type u` with `[Field K] [IsAlgClosed K]` and every `b : Spec (.of K) ⟶ B`.
  `topologicalKrullDim (pullback g b : Scheme.{u}) ≤ (e : WithBot ℕ∞)` is exactly
  the bound on each geometric fibre; it is not a bound on the set of lifts of a point.
- `R : Sheaf (Scheme.ProEt.topology X) Ab.{u+1}`, `[MonObj R] [IsCommMonObj R]`
  is an arbitrary commutative internal ring object in abelian pro-etale sheaves.
  `M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) R` is an ordinary internal
  module, rather than a completed or constructible derived object.
- `hlocal` quantifies over **every** `U : X.Opens` with `IsAffineOpen U`, and every
  `q : ℕ` with `a < q`. Its evaluation object is `Scheme.ProEt.mk U.ι`.
  The functor being derived is `Mod.forget R ⋙ sheafToPresheaf ... ⋙ evaluation ...`:
  it takes an internal R-module to its section group on U. `rightDerived q` derives
  this entire composite **in the internal R-module category**. It does not apply
  abelian-sheaf derived sections to the forgotten module without comparison.
- This is an exact presentation of the node's open-slice restriction: the sectionwise
  equivalence keeps the same section groups, and preserves injective resolutions.
  `module_derived_evaluation_slice` identifies their derived evaluation at U with
  abelian cohomology on the slice. Applied on the slice, the same theorem identifies
  the latter with module-derived global sections over the restricted ring.
  `proEtale_ringed_open_comparison` then identifies this slice with U's small
  pro-etale site with the actual inverse-image ring and module. Thus the local
  hypothesis is precisely H^q(RΓ(U_proet,M|U)) = 0, with both ring and module
  restricted; it imposes no acyclicity of the un-restricted section groups.
- The conclusion evaluates at `Scheme.ProEt.mk (𝟙 X)`, the terminal object.
  `(r : ℕ) (hr : e + a < r)` and `IsZero (...rightDerived r...).obj M` say
  H^r(RΓ(X_proet,M)) = 0 for r > e+a. The node defines RΓ via a degree-zero module
  and an injective resolution, exactly the construction of `Functor.rightDerived`.
  This is a vanishing statement, not a comparison of derived objects requiring a
  separate derived isomorphism. Since a,e ≥ 0, every quantified q or r in either
  vanishing range is positive; using ℕ instead of ℤ loses no asserted degree.
- The site has object universe u+1 and morphism universe u; coefficient groups use
  u+1. There is no SmallCategory X.ProEt binder or equality of these universes.
  The imported essentially-small sheaf/module instances supply the categorical
  structures and injective resolutions. No extra categorical hypothesis is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, `IsAffineOpen`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `Separated`:
  `AlgebraicGeometry.IsSeparated`, the separatedness clause of the proper-morphism
  dependency; properness itself is deliberately not assumed.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  the recorded geometric-fibre construction. `Mathlib.Topology.KrullDimension`:
  `topologicalKrullDim` with its empty-space value ⊥.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`,
  `ProEt.mk`; `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`,
  instantiated by the canonical open inclusion U.ι.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `Mod.forget`.
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `Resolution`:
  `Injective`, `InjectiveResolution`, used by `Functor.rightDerived` from
  `Mathlib.CategoryTheory.Abelian.RightDerived`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`:
  `Scheme.proEtale_ringed_open_comparison`, with its full arbitrary-ring signature.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleEquivalence` and `sectionRingSheaf`;
  `Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice`:
  `CategoryTheory.module_derived_evaluation_slice`. These justify the section/slice
  interpretation without replacing the coefficient ring by constants.
- `def-weil-size-convention` is a metatheoretic convention, as its existing record
  states. It is rendered by the explicit universe u and u+1 sizes above.

The module imports the available proof-dependency modules, including the recorded
field-extension dimension theorem, spectral-space definition, internal module equivalence,
sheaf tensor, arbitrary ringed-site Grothendieck category, module-derived slice comparison,
weakly-etale localization, site comparisons/composition/exact pullback, higher direct images,
affine basis, sheafification, Grothendieck spectral sequence, and injective preservation.
The node `lem-sfb-spectral-space-cohomology-dimension` currently has neither a Lean
record nor a Mathlib match, so there is no module to import for that proof-only input.
Its Stacks 0A3G proof role is retained explicitly in the theorem's proof docstring.
No statement dependency is missing or repaired.

Edge cases checked: X empty (dimension ⊥, all evaluated section cohomology zero);
B empty (forces X empty); empty affine opens; e=0; a=0; e=a=0; M zero; the zero ring
object; nonreduced and non-Noetherian zero-dimensional affine bases; arbitrary
algebraically closed geometric points. No Nonempty, reducedness, Noetherianity,
finite presentation, constructibility, adic completeness, constant coefficients,
w-contractibility, or separably closed residue-field assumption appears.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “On a separated finite type scheme over a zero
  dimensional affine base, affine open cohomology vanishing above a implies global
  cohomology vanishing above dimension of fibres plus a”. Eight hits, including
  `IsSeparated.hasAffineProperty`, affine-limit section lemmas, a finite discrete
  scheme affineness instance, and affine localization section lemmas. No match.
- `msearch.py ... loogle`: `topologicalKrullDim, CategoryTheory.Functor.rightDerived`.
  Zero hits. An earlier probe used unqualified `Functor.rightDerived` and returned
  an unknown-identifier message; the corrected search above also has no hits.
- `msearch.py ... grep`: `affine.*global.*(bound|cohomolog)|zero.*dimensional.*cohomolog`.
  Zero Mathlib hits.
- `rg` over lean/WeilConjectures and lean/Sheaf for affine/global cohomology and
  zero-dimensional cohomology found the curve étale zero-dimensional results and
  `Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension`.
  That module was read: it assumes a field, torsion étale coefficients, and uses a
  Noetherian Zariski bound. It is not the current arbitrary-ring pro-etale statement.
- `rg` for the item id in lean/WeilConjectures: no hit. `rg` for the new declaration's
  full last component in Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json:
  no hit. Existing core notions are used directly; no new notion was necessary.

Sources opened: the local Stacks cohomology.tex proposition
`proposition-cohomological-dimension-spectral` (0A3G), and sites-cohomology.tex
`lemma-Leray` (0732). Their spectral-space and ringed-topos statements support the
node's proof without a Noetherian or coefficient specialization.

Validation: scompile.py compiled the module both as a sandbox file and at its final
library module path. The initial runs identified only two long-line warnings; those
lines were split. The final clean compile and delivery preflight are recorded by the
prescribed wrappers. No Lean proof was filled, and no statement correction or dispute
was necessary.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
