## Worker report

The module Sheaf.AlgebraicGeometry.PuncturedSupportCohomologicalBound states
AlgebraicGeometry.Etale.isZero_cohomology_punctured_of_support_dimension_le.
Its sole theorem has proof `sorry`; no definitions, helper axioms, new nodes or
dependency repairs are introduced. Only the item's lean field changes.

Hypothesis and conclusion correspondence:

- The prime ℓ is `(ℓ : ℕ) (hℓ : ℓ.Prime)`.
- The local scheme X is presented as `Spec R`, with `R : CommRingCat.{u}`,
  `[IsNoetherianRing R]`, `[IsStrictlyHenselianLocalRing R]`, and `hR : IsExcellent R`.
  This is the full notion: every local scheme is the spectrum of its local ring,
  including nonreduced and nonnormal local schemes. There is no finite dimension,
  domain, normality or finite type assumption. The closed point is
  `IsLocalRing.closedPoint R` and invertibility is `hunit : IsUnit (ℓ : R)`.
- `U : (Spec R).Opens` and hU identify U with the complement of that closed point.
  Keeping U as an open with its carrier equality avoids any second puncture construction.
- F is `Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))`,
  the coefficient-category encoding explicitly allowed by def-weil-pbc-etale-sheaves.
  ModuleCat allows its scalar ring in the small universe and its modules in u+1;
  ZMod ℓ therefore needs no coefficient-ring lift or comparison assumption.
- `s : ℕ` is exactly a nonnegative integer, including zero.
- hs quantifies over every algebraically closed field Ω in Type u and every geometric
  point `t : Spec (.of Ω) ⟶ U.toScheme`. Its underlying point in X is
  `U.ι (t (IsLocalRing.closedPoint Ω))`. Every geometric point determines such a point,
  so this combines the node's y and geometric-point quantifiers without losing cases.
  `¬ IsZero (pointedEtaleStalk F t)` says the module stalk is nonzero. The dimension
  inequality is `topologicalKrullDim (closure {U.ι (t ...)}) ≤ (s : WithBot ℕ∞)`;
  the singleton and closure are explicitly in Spec R, not in U.
- `p : ℤ` and `hp : (2 * s : ℤ) ≤ p` retain the integer degree and the inclusive bound.
- The conclusion is IsZero of `Etale.cohomology AddCommGrpCat U.toScheme p` applied
  to `DerivedCategory.singleFunctor ... 0` of the underlying abelian sheaf.
  The latter is obtained by the canonical `sheafCompose ... (forget₂ ModuleCat
  AddCommGrpCat)`, not an arbitrary abelian object. Thus precisely the specified
  right-derived global-sections cohomology vanishes.

Dependency declarations read and used:

- Sheaf.RingTheory.ExcellentRing: IsExcellent, the conjunction of IsQuasiExcellent
  and IsUniversallyCatenary, with their full definitions read.
- WeilConjectures.Mathlib.RingTheory.Henselian: IsStrictlyHenselianLocalRing,
  extending HenselianLocalRing with separably closed residue field.
- WeilConjectures.AlgebraicGeometry.EtaleSheaves: its recorded conventions for
  small-etale module sheaves, Sheaf and the ModuleCat encoding.
- Sheaf.AlgebraicGeometry.PointedEtaleStalk: pointedEtaleStalk, its explicitly
  defined opposite-neighbourhood diagram and colimit construction.
- Mathlib.RingTheory.KrullDimension.Basic: ringKrullDim; the scheme closure uses
  Mathlib.Topology.KrullDimension.topologicalKrullDim, the same dimension on
  the spectrum and its closed subspaces, with values in WithBot ENat.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek: Etale.cohomology,
  defined as rightDerivedGlobalSections followed by homologyFunctor;
  rightDerivedGlobalSections is the total right derived functor of Sheaf.Γ.
- def-weil-pbc-scheme-conventions has a convention-only lean record, no module
  of its own. Spec, Opens and their open subscheme/immersion are the existing APIs.

Source: opened the local ILO PDF, PDF pages 274--275 (printed pp. 268--269).
Proposition XVII 3.2.1 states exactly this result with d in N. It explicitly treats
arbitrary module sheaves and reduces to constructibles only in its proof. The proof
in the module follows the current DAG's two steps: finite Krull dimension of a
Noetherian local ring, then exponent-one specialization of
lem-per-strict-local-etale-dimension-bounds. That proof dependency has no lean
record yet, so it has no proof-only import to add. No changes to that node are needed
to state this item's assertion.

Edge cases: s=0 forces F to have zero stalks, because every point of U has a
strict specialization to the distinct closed point in X; therefore H^0 also vanishes.
Dimension-zero local schemes have empty U. The zero sheaf satisfies hs for every s.
A strictly local trait with s=1 gives vanishing starting at degree 2 and does not
assert vanishing of H^1. Nothing assumes support closed or constructible. All
universes and variables are explicitly bound with autoImplicit false.

Searches actually run through msearch.py for this NH item:

- LeanFinder: “Etale cohomology of a sheaf of modules killed by a prime on an
  excellent strictly henselian punctured local scheme vanishes above twice support
  dimension”: eight hits concerning algebraic etale loci and localization, no match.
- Loogle: `"cohomology", "punctured"`: zero hits.
- Mathlib grep: `punctured|support.*cohomolog` in AlgebraicGeometry: zero hits.
- LeanSearch: “Etale cohomology of an excellent strictly henselian punctured local
  scheme with bounded support dimension”: eight hits concerning etale morphisms/sites,
  no cohomological bound.
- rg in the upstream WeilConjectures tree for the item id, punctured cohomology,
  punctured/support bound names and strict-local bounds: no exact statement.
- rg in lean/Sheaf: PuncturedPerverseHighComparison cites this bound in its proof
  docstring but does not declare it. Q23's reviewed delivery is the stage-1 split;
  the current item has no lean record, so this is its first stage-2 statement.

Validation: scompile.py NH lem-per-punctured-support-cohomological-bound compiled
both its sandbox test and the final library-path file cleanly (2.1 s and 2.7 s).
No STATEMENT-DISPUTED issue or node correction was found.

## Second reading by NH

The dispatcher explicitly forbids starting other agents and provides independent
maintainer review. No independent worker review is claimed here. I reread the node,
module and printed source to check the inclusive degree bound, ambient closure,
arbitrary sheaves, actual abelian forgetful functor, and s=0/empty-puncture cases.
The comparison above is supplied for the maintainer's independent second reading.
