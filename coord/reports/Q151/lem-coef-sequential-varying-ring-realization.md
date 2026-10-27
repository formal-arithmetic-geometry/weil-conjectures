## Worker report

Item: lem-coef-sequential-varying-ring-realization, group Q151.
The new module Sheaf.Paper.SequentialVaryingRingRealization states
AlgebraicGeometry.Scheme.SequentialVaryingRing.realization with proof `sorry`.
Its seven auxiliary definitions contain actual canonical data, not postponed data.
There are no new nodes, dependency repairs, or changes to the mathematical statement.

Clause-by-clause correspondence:

- Scheme and compatible site universes: `T : Scheme.{u}`, `ProEt.topology T`,
  coefficient sheaves `CommRingCat.{u+1}` and `reductionModules T` in the existing
  essentially-small pro-etale framework. The object universe is u+1, the site's
  morphism universe is u. No equality of these universes is imposed. AsSmall site
  transport is already supplied by AdicCoefficientDatum; it does not change modules.
- The positive level k is represented by natural index k-1 throughout, including
  the prescribed first pair at index zero. All levels and all ordered pairs occur.
- The sheaves B_n and all q_{m,n}, with identity and composition laws, are precisely
  `B : ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{u+1}`. Functor.map_id and
  Functor.map_comp are exactly the two ring-map hypotheses, not extra hypotheses.
- The common coefficient sheaf R and maps pi_n, satisfying q pi = pi, are
  `c : Cone B`, with `c.pt` and `c.π.app (op n)` and `c.w`. An arbitrary cone is
  used; it is not required to be a limit cone or to be an adic coefficient datum.
- Ordinary, complex and derived restriction are the existing `reductionRestrict`,
  its `mapHomologicalComplex (.up ℤ)`, and `reductionDerivedRestrict`. They are
  exactly Mathlib SheafOfModules.restrictScalars and its exact localization.
- `M` has every required derived module type. `τ m n h` has source M_m and target
  Res_{m,n} M_n. `hτid` uses the canonical derived unit, also transporting B.map_id;
  `hτcomp` uses the canonical derived compositor including B.map_comp. All maps
  are composed in Lean's left-to-right `≫` convention.
- The existential `C` consists of integer-indexed complexes of B_n modules;
  `i n : Q.obj (C n) ≅ M n` are isomorphisms in the full derived category.
- `t (n+1) n (Nat.le_succ n)` are the stated B_{n+1}-linear adjacent chain maps.
  The existential t also records all composites. Its diagonal HEq asserts the
  identity after transporting the coefficient identity; its three-index equation
  says precisely that the t's are the iterated composites of adjacent arrows.
  It is therefore not a free family of representatives for the composite arrows.
- The equation quantified over `(m n : ℕ) (h : n ≤ m)` reads Q(t) followed by the
  inverse exact factorization followed by Res(i_n) equals i_m followed by τ_{m,n}.
  Taking m=n+1 is the adjacent equation. The inverse factorization is necessary
  because Res(Q C_n) and Q(Res C_n) are canonically isomorphic, not literally equal.
- `C₀` and `i₀` are an arbitrary prescribed first pair. `C 0 = C₀` and
  `HEq (i 0) i₀` retain the pair itself, not merely its isomorphism class. Supplying
  an arbitrary first pair is equivalent to the unprescribed existence formulation:
  Q is essentially surjective, and the stronger prescribed-pair clause is explicit
  in the node. No extra condition is imposed on M or the coefficient system.
- `S` is a cochain complex in the existing `reductionTowerCategory T` for c.pt.
  `hS : S.asFunctor = restrictedTower ...` specifies its actual evaluated
  complexes, every differential, and its actual adjacent chain transitions.
  restrictedTower uses Functor.ofOpSequence on the restricted t's, with the
  identity-on-sections cone compositor; it is not a diagram of homology objects.
- Localizing S gives the node's M_bullet. `evaluationIso` explicitly composes the
  exact evaluation factorization, hS, inverse scalar factorization and Res(i_n).
  Thus its derived evaluation comparisons are canonical for the chosen model.
- `evaluatedTransition` is Q of the actual evaluated chain transition conjugated
  by the canonical evaluation factorizations. This is the evaluated transition
  on [S], not an arbitrary derived arrow. The last equation, for every m≥n,
  identifies it under evaluationIso with Res_m(τ_{m,n}), followed by the cone's
  canonical derived composition identification.
- No boundedness, constructibility, finite-ring, adic, flatness, or invertibility
  assumptions have been added. The import of AdicCoefficientDatum only uses its
  general ring-sheaf, scalar restriction and tower interfaces.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt, ProEt.topology.
- def-weil-size-convention is a metatheoretic convention; it has no declaration.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  SheafOfModules.restrictScalars, its section-preserving objects/maps and Additive.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently Mathlib SheafOfModules, with its inherited abelian structure.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: HasDerivedCategory,
  DerivedCategory and DerivedCategory.Q.
- Sheaf.Paper.AdicCoefficientDatum: Scheme.reductionModuleRing, reductionModules,
  reductionModulesHasDerivedCategory, reductionDerivedCategory, reductionRestrict,
  reductionRestrict_additive, reductionRestrict_preservesFiniteLimits,
  reductionRestrict_preservesFiniteColimits, reductionDerivedRestrict,
  reductionTowerCategory, reductionTowerEvaluation, reductionTowerHasDerivedCategory,
  reductionTowerDerivedEvaluation. Their complete signatures and relevant docstrings
  were read in the source. These permit arbitrary coefficient sheaves and cones.
- Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition:
  Functor.exactDerivedRestrictionComposition and exactDerivedRestrictionUnit,
  including their cochain-normalization theorems, are used by the canonical helpers.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  Functor.mapDerivedCategoryFactors and the exact derived functor.
- Mathlib.Algebra.Homology.Functor: HomologicalComplex.asFunctor.
- Mathlib.CategoryTheory.Functor.OfSequence: Functor.ofOpSequence.
- The stated proof prerequisites are imported without public visibility:
  Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction,
  Mathlib.Algebra.Homology.DerivedCategory.Fractions,
  Mathlib.CategoryTheory.Localization.CalculusOfFractions. The levelwise-abelian
  Mathlib functor-category interface is already in the public import closure.

Edge cases checked before writing and again against the final statement:
zero ring sheaves, zero modules and complexes, empty scheme, identity coefficient
maps, diagonal pairs m=n, first level, arbitrary unbounded complexes, zero and
noninvertible transition maps. Diagonal transport uses actual equality of ring
maps and the canonical derived unit; no definitional identity is presumed.
An arbitrary prescribed complex need not be K-flat or K-injective. The roof
induction changes only the next source, so retaining that complex is legitimate.
All universes and binders are explicit, with autoImplicit disabled. Arbitrarily
large compatible coefficients are accommodated by choosing the universe u that
contains the scheme and coefficients, as in the node's size convention.

Searches made (also captured in searches.jsonl by the prescribed wrapper):

- leanfinder: 'Sequential derived realization of inverse systems of complexes with
  varying sheaves of coefficient rings': eight hits, including InverseSystem.globalEquiv,
  localCohomology.diagram and LightProfinite.transitionMap; no statement match.
- loogle: 'SheafOfModules.restrictScalars, CochainComplex': zero hits.
- grep Mathlib Algebra/Category/ModuleCat:
  'restrictScalars.*(Comp|comp|Id|id)': module-level comparisons and presheaf
  restriction, no simultaneous varying-ring sequential realization.
- LeanSearch: 'An inverse sequence of derived modules over varying sheaves of
  rings admits simultaneous cochain representatives preserving the first
  representative': eight hits (cochain induction, module-sheaf limits and
  derivations), no statement match.
- rg over lean/WeilConjectures and lean/Sheaf for the item id,
  'sequential.*[Rr]ealization|varying.*ring': varying-ring systems and other
  realization results, no exact theorem. SequentialTowerEvaluationFull concerns
  compatible maps between already existing constant-ring tower objects and
  cannot replace this varying-ring existence theorem. ScalarInternalHomData's
  comparison interfaces were inspected, but importing that large unrelated
  scalar-Hom framework is unnecessary; the exact-restriction dependency supplies
  the compositor used here. No mathematical notion has been copied privately.

Sources opened: current blueprint lem-coef-integral-compact-support.proof.md
paragraph 2; Stacks derived.tex lemma-acyclic (05RT), categories.tex
lemma-morphisms-right-localization (04VI), and the recorded dependency source
modules. The theorem docstring includes the complete seven-step DAG proof route.
No STATEMENT-DISPUTED flag or node fault remains.

Validation: scompile.py compiled the sandbox and library module cleanly in 9.3 s
per file before the final proof-prerequisite import was added; delivery validation
recompiles the exact final file. Only the expected theorem `sorry` remains.

## Second reading by Q151

This is a direct second reading by the same dispatched worker, not an independent
agent review: the dispatcher explicitly forbids starting other agents and states
that the maintainer independently reviews the delivery. The node and final file
were reopened and compared using the complete clause mapping above.

The reading checked especially the reversed scalar direction (B_m acts on C_n
through B_m→B_n), both derived composition directions, arbitrary noninvertible
τ, preservation of the actual first pair, and all m≥n rather than only adjacent
pairs. It confirmed that hS identifies actual complexes and differentials, while
evaluationIso uses canonical factorization maps; the final clause is a derived
morphism equation. The t cocycle ensures the supplied all-pairs t's are exactly
adjacent composites. The only changes during elaboration were the actual API of
mapHomologicalComplexCompIso and an explicit functor type annotation in evaluationIso.
These did not change any mathematical hypothesis or conclusion.
