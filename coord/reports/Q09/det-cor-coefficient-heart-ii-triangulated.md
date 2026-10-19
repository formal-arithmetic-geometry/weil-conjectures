## Worker report

The module `Sheaf.Paper.CoefficientHeartTriangulated` states
`AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_field_triangulated`.
Its only theorem proof is `sorry`; there are no new definitions or auxiliary theorems.
The node is unchanged outside `lean`.

Source checked: current blueprint main-20261015,
sec-six-functors-basics/sk-cor-coefficient-heart-ii/
sk-cor-coefficient-heart-ii-triangulated.md and its proof file, together with the unit
_section.md. The DAG proof expands exactly the source's cohomology and direct-summand
argument. The docstring carries all six DAG proof steps and names their dependencies.

Hypotheses and clauses:

- `X : Scheme.{u}` is the source's arbitrary scheme; `[IsLocallyNoetherian X]`
  and `[CompactSpace X]` together mean Noetherian. There is no separatedness,
  finite-type, base field, or invertibility-of-ell hypothesis.
- `(ℓ : ℕ) [Fact ℓ.Prime]` makes explicit the fixed prime in the coefficient notation.
- `∀ E : PadicAlgCl.FiniteIntermediateField ℓ` states the assertion for every finite
  extension of Q_ell in the fixed algebraic closure. `Profinite.continuousMapRingObj.{u} E`
  is the continuous condensed ring E, with its canonical multiplication. Using the fixed
  closure realizes all finite coefficient extensions up to isomorphism, as in the source.
- The second part uses `Profinite.padicAlgClRingObj.{u} ℓ`, whose sections are continuous
  maps valued in a single finite subextension. This is precisely the source's condensed
  algebraic closure, rather than all continuous maps into the valuation-topological closure.
- In each case `constantModelBoundedConstructible Λ X` is the recorded Dbc object property:
  bounded for the standard derived t-structure and every cohomology sheaf constructible
  with finite constant local models. Its domain is the unbounded derived category of
  internal modules over the actual `condensedRingObj Λ X = p_X^* Λ`.
- `.IsClosedUnderIsomorphisms` is exactly the repleteness clause.
- `.IsTriangulated` extends `ContainsZero`, `IsStableUnderShift ℤ` and
  `IsTriangulatedClosed₂`. With repleteness, `ContainsZero` gives membership of zero;
  integer shift stability gives both +1 and -1. The extension axiom gives the middle
  vertex of a distinguished triangle when its outer vertices belong. The Mathlib
  instances `IsTriangulatedClosed₁` and `IsTriangulatedClosed₃` rotate triangles to give
  each of the other two choices of vertices. Thus this is exactly the stated zero,
  shifts and two-out-of-three criterion and the resulting triangulated full subcategory.
  All integer shifts follow from iterating the two shifts, so this adds no mathematical
  strength. The inherited triangulated structure and exact inclusion are Mathlib's
  full-subcategory constructions.
- `.IsStableUnderRetracts` says every retract of an object satisfying this property
  satisfies it. This is thickness/direct-summand closure, including both summands of
  a biproduct. Conversely a retract has a complement in the ambient derived category
  of this Grothendieck abelian module category, so this is the standard thickness clause.

Statement dependencies read and used:

- `det-def-sfb-constructible-tor-amplitude`: imported recorded module
  `Sheaf.Paper.ConstantModelTorAmplitude`, declaration
  `AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined`.
  Its docstring explicitly owns the well-definedness assertion while importing the four
  defining notions from `Sheaf.Paper.CondensedConstantConstructibility`; its
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and
  `IsConstantModelConstructible` are reused verbatim. No private copy and no substitution
  of the upstream stratified-local-finite-presentation notion is made.
- `def-weil-triangulated-subcategory` is a Mathlib leaf:
  `CategoryTheory.ObjectProperty.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Subcategory`. Read its full signature, docstring,
  zero/shift/triangle parent fields and the rotation instances. The recorded dependency
  module publicly exports it.

Proof imports cover every currently stated proof dependency: RingedSiteModules,
PbcQbarStandardCohomology (also retains the generic cohomology API), FiniteConstantLocalModel,
Shift.ShiftSequence, DerivedCategory.HomologySequence, Abelian.Basic,
Triangulated.Pretriangulated and DerivedCategory.Basic, in addition to the statement
imports. `def-weil-size-convention` is metatheoretic with no module. The proof dependency
`det-lem-coefficient-heart-closure` currently has neither a Lean record nor Mathlib match;
its future proof import is omitted. This does not affect the theorem's statement.
The coefficient declarations are the published upstream
`RingObjects.Condensed.FiniteSubextension` and its public imports. Their full definitions
and docstrings, including the finite-image Qbar construction, were read in the shared
read-only framework.

Edge cases checked before writing: empty schemes and the empty stratification remain
included; rank-zero local models and the zero complex belong; boundedness permits empty
cohomological support and arbitrary negative and positive degrees; the +1 convention
moves support from S to S-1; all three triangle-vertex choices follow by rotation.
In a retract a : M -> F, b : F -> M, the complementary idempotent on F is 1 - b ≫ a,
whose kernel is M; the docstring uses this order. No invertibility of ell on X is needed
for this purely categorical closure result. Universe u is explicit; condensed and
pro-etale sheaves take values in Ab.{u+1}, preserving the existing small-site convention.

Searches for an existing statement:

- `msearch.py ... leanfinder "Bounded constructible complexes over a condensed l-adic
  field form a thick triangulated subcategory"`: eight generic derived t-structure and
  boundedness hits, no statement about these constructibility conditions.
- `msearch.py ... loogle "CategoryTheory.ObjectProperty.IsTriangulated,
  CategoryTheory.ObjectProperty.IsStableUnderRetracts"`: generic
  `CategoryTheory.ObjectProperty.triangEnvelope_le_iff`, no coefficient-specific theorem.
- `msearch.py ... grep "constructible.*[Tt]riangulated|[Tt]hick.*constructible"`:
  zero Mathlib hits.
- `rg` on upstream WeilConjectures and project lean/Sheaf for the node identifier and
  `constantModelBoundedConstructible` with triangulated/thick names: no existing match.
  Broader coefficient searches identified the already published continuous E and
  finite-image Qbar coefficient declarations, which are imported rather than duplicated.
- Read the neighboring CondensedConstructibleSerre module: it concerns the different
  upstream local-finite-presentation constructibility predicate, so it cannot be used
  as an exact match for this finite-constant-model theorem.

Validation: prescribed `scompile.py Q09 det-cor-coefficient-heart-ii-triangulated` compiled
this file in both sandbox and library modes, cleanly (2.9 s and 4.0 s respectively).
There are no statement disputes or node faults.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
