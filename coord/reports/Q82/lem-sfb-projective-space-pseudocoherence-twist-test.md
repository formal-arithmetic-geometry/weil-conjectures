## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveSpacePseudoCoherenceTwistTest` states
`AlgebraicGeometry.ProjectiveSpace.isPseudoCoherent_of_twist_derivedGlobalSections`,
with `sorry` as its entire proof. It defines no new notion. The source read was
Stacks Project, `perfect.tex`, Tag 0CSG, `lemma-pseudo-coherent-on-projective-space`,
including its statement and the proof of (5) => (1), lines 8556–8647.
The item's statement, dependency lists, and accepted proof are unchanged.

Clause-by-clause correspondence:

- A commutative ring R is `(R : Type u) [CommRing R]`. No domain, nontriviality,
  field, finiteness, or Noetherian assumption is imposed.
- N >= 0 is `(N : ℕ)`, including zero. The projective space P is
  `ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))`, the existing model
  specified by the recorded projective-space-twist dependency. Its homogeneous
  coordinate set has exactly N+1 elements. `ULift` places it in the ring's universe.
- K in D_QCoh(O_P) is `(K : schemeDerivedQCohCategory P)`. By the dependency's
  `schemeDerivedQCohProperty`, this says that every integer cohomology sheaf of
  `K.obj` is quasi-coherent. It imposes no upper or lower cohomological bound.
- The test degrees d = 0,...,N are exactly `∀ d : Fin (N + 1)`, with integer
  twist exponent `(d.val : ℤ)`. The twist is the dependency's `ProjectiveSpace.twist`.
- The sheaf O_P(d) enters the derived category by `DerivedCategory.singleFunctor`
  in degree zero, explicitly for the shared `SheafOfModules` category, rather than
  the separately instantiated `Scheme.Modules` category.
- The tensor is `K.obj ⊗ (DerivedCategory.singleFunctor ... 0).obj (twist ... d)`.
  This uses the global `schemeDerivedTensorMonoidal` instance; no tensor structure
  is supplied as an extra hypothesis.
- RΓ is the recorded `schemeDerivedGlobalSections P`. Its coefficient ring is
  initially Γ(P,O_P). Application of `Functor.mapDerivedCategory.{wG, wR}
  (ModuleCat.restrictScalars.{u} (S := Γ(P,O_P)) φ)`
  makes the result an object of D(R), where φ is the actual structural ring map
  `((Scheme.ΓSpecIso (.of R)).inv ≫ (P ↘ Spec (.of R)).appTop).hom`.
  Exact restriction retains the R-action induced by the structural morphism. It is
  neither an arbitrary map nor an assumption identifying R with another ring.
  This is also precisely the scalar map used by the existing tilting node.
- Pseudo-coherence of every R-valued test is `DerivedCategory.IsPseudoCoherent`
  in hypothesis `hK`, using the recorded bounded-above finite-free definition.
- The conclusion is `Scheme.IsPseudoCoherent P K.obj`, exactly the recorded
  scheme-local bounded-above finite-free notion.
- The explicit `HasDerivedCategory` binders only select the shared localization
  interfaces needed by these definitions. The scheme and all open restrictions
  use `wX`, as required by the pseudo-coherent predicate; the coefficient
  categories use independent `wR` and `wG`. No equality of these universes is imposed.

Statement dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `AlgebraicGeometry.ProjectiveSpace.twist`, including its pullback construction,
  local bases, and transition-rule documentation.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`,
  `schemeDerivedQCohCategory`.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`.
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`.
- `WeilConjectures.AlgebraicGeometry.GlobalDerivedHom`:
  `AlgebraicGeometry.schemeDerivedGlobalSections` (the derived-sections clause of
  def-pc-global-derived-rhom); its full functor type and resolution documentation
  were read, as was `schemeGlobalDerivedHom`.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `AlgebraicGeometry.schemeDerivedTensorMonoidal`.

All recorded proof dependency modules are imported with plain `import` when they
are not already statement imports: `Sheaf.AlgebraicGeometry.ProjectiveSpaceTiltingEquivalence`,
`WeilConjectures.AlgebraicGeometry.PerfectComplex`,
`WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison`,
`Sheaf.RingTheory.FiniteFreeAlgebraPseudoCoherentResolution`, and
`Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation`.
Their theorem signatures and proof docstrings were read. The new theorem's docstring
retains all five steps of the accepted proof: unbounded tilting; perfect duality and
finite biproducts; finite sums of finite-free models; finite-free algebra resolution;
and bounded-above projective computation with standard-chart free representatives.

Edge cases checked before writing: N=0 gives exactly the one test O(0) over the
projective zero-space; K=0 passes the tests and conclusion; the zero ring is allowed
(the empty scheme gives a vacuous point-local conclusion); arbitrary non-Noetherian
rings and unbounded K remain allowed. The degree set is never empty because it has
N+1 elements. None of these cases needs a positivity or nontriviality hypothesis.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query “A complex on projective n space with quasi coherent
  cohomology is pseudo coherent if derived global sections of its twists O(d) for d
  zero through n are pseudo coherent”: 8 hits, general K-projectivity, projective
  resolutions, and sheaf cohomology; no finite-twist criterion.
- `msearch.py loogle`, query `PseudoCoherent, ProjectiveSpace`: 0 hits, unknown
  identifier `PseudoCoherent`.
- `msearch.py grep`, query `pseudo.?[Cc]oherent|pseudo_coherent`, subdirectory
  `AlgebraicGeometry`: 0 Mathlib hits.
- `msearch.py leansearch`, query “Pseudo coherent complexes on projective space are
  detected by derived global sections after tensoring with O(d) for zero through n”:
  8 hits, general projective resolutions, Proj sections, quasi-coherent presentations,
  and sheaf cohomology; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `projective.{0,90}pseudo|pseudo.{0,90}projective|0CSG` (case-insensitive) found only
  unrelated pseudo-coherence and projective-direct-image material, not this criterion.
  `rg` for the exact item id in `lean/WeilConjectures` found no hit.
  The pseudo-coherence searches in the projective-space sources and Sheaf modules
  found the existing general predicates and other results, not the finite-twist test.
  The declaration-name search in `dag/lean_names_upstream.json` found no candidate.

No new nodes, dependency repairs, statement corrections, or mathematical disputes.

Validation: the final module compiled through `scompile.py`, in both sandbox and
library module modes, with no errors or warnings. The early elaboration failure
was resolved by explicitly naming the coefficient ring in `restrictScalars` and
the independent localization universes in `Functor.mapDerivedCategory`. No
universe equality, mathematical hypothesis, or dependency repair was added.
All diagnostic `#check` commands and pretty-printing options were removed.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
