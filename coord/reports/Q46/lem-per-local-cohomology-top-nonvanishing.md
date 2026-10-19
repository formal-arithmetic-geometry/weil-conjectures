## Worker report

The module `Sheaf.Algebra.Homology.TopLocalCohomologyNonvanishing` states
`ModuleCat.top_local_cohomology_nonzero`, with its proof postponed by `sorry`.
It follows Stacks Project, Local Cohomology, Tag 0DXE (`lemma-cd-maximal`),
lines 594–633 of `literature/stacks-project/local-cohomology.tex`. Only the
nonvanishing assertion is stated, as requested by the node, not the additional
cohomological-dimension equality in that Stacks lemma.

Hypotheses and clauses, matched against the node:

- The commutative ring is `(R : Type u) [CommRing R]`, with arbitrary explicit
  universe `u`.
- Noetherianity is `[IsNoetherianRing R]`, the declaration recorded by
  `def-weil-pbc-noetherian-ring`. Its definition and
  `isNoetherianRing_iff_ideal_fg` say every ideal is finitely generated.
- The nonzero local-ring condition is `[IsLocalRing R]`. This Mathlib class
  extends `Nontrivial R`; no independent or omitted nonzero assumption is needed.
  Its distinguished unique maximal ideal is `IsLocalRing.maximalIdeal R`, which
  renders the node's `n`. The node does not quantify over a separate ideal.
- Finite nonnegative dimension is `(d : ℕ)` together with
  `hd : topologicalKrullDim (AlgebraicGeometry.Spec (.of R)) = (d : WithBot ℕ∞)`.
  This uses the exact topological dimension and affine spectrum recorded by the
  two dimension-related dependencies. There is no implicit change to a different
  dimension convention, or exclusion of dimension zero.
- The node introduces Gamma_n on modules. The existing
  `ModuleCat.idealPowerTorsion (IsLocalRing.maximalIdeal R)` is precisely that
  additive endofunctor. Its object is `Ideal.primaryComponent M J`, and its map
  is the restricted linear map. The primary-component membership theorem says
  an element is killed by all elements of some `J^n`. Its exponent can be zero;
  `J^0 = R` kills only the zero element, which is also killed by `J^1`, so this
  is exactly the node's positive-exponent convention.
- The node defines H^j as R^j Gamma. This is rendered literally by
  `(idealPowerTorsion (IsLocalRing.maximalIdeal R)).rightDerived d`.
  Mathlib's `Functor.rightDerived` applies the functor to an injective resolution
  and takes its degree-d cohomology. `ModuleCat.EnoughInjectives` supplies the
  resolution instance; no chosen injective resolution is assumed in the theorem.
- Evaluation on R is `.obj (ModuleCat.of R R)`, with its ordinary regular
  R-module structure. No arbitrary module or auxiliary complex replaces R.
- The conclusion `¬ IsZero (...)` means this object of the module category is
  nonzero, equivalently its underlying module is not subsingleton. `IsZero` is
  used on a module-category object, not a bare type.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`:
  `ModuleCat.idealPowerTorsion` and its additive instance. Its already landed
  owning node `def-sbc-ideal-power-torsion-functor` is added to `stmt_deps`,
  as authorized for landed notions. Its source is Stacks 0BJA.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `CategoryTheory.Functor.rightDerived`.
- `Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs`:
  `IsLocalRing.maximalIdeal`; `IsLocalRing` extends `Nontrivial` in LocalRing.Defs.

Private imports retain the currently stated proof dependencies: adic completion,
Noetherianity of completion, locality of completion, completion completeness,
faithful flatness, dimension of completion, Cohen presentation, derived internal
Hom, ring Krull dimension, and the finite-module completion tensor comparison.
The remaining proof-dependency nodes have no recorded Lean statement yet, so
there is no module to import for those. Their roles remain in the seven-step
proof docstring. `scompile.py --source` was used to read the current published
`WeilConjectures.RingTheory.AdicCompletionNoetherian` source, absent in the older
local upstream checkout.

Edge cases checked before writing: a field has maximal ideal zero and d = 0,
so Gamma is the identity and H^0(R) = R is nonzero. More generally a nonzero
Artinian local ring has nilpotent maximal ideal, again giving H^0(R) = R.
The zero ring is excluded by `IsLocalRing`; no claim is made in dimension
minus infinity. Positive characteristic and mixed characteristic require no
additional assumption and are included. There is no completeness, regularity,
domain, or residue-field hypothesis. Arbitrary ring universe is retained;
only the regular module R is evaluated, so no module-universe restriction
loses a case.

Searches made on 2026-10-18 UTC with the prescribed msearch wrapper:

- LeanFinder: `For a nonzero Noetherian local ring of finite dimension d, the top
  local cohomology at its maximal ideal is nonzero`. Eight results concerned
  completion, Krull intersection, or dimension inequalities; no nonvanishing
  theorem matched.
- Loogle: `localCohomology, IsLocalRing, topologicalKrullDim`. Zero results.
- LeanSearch: `top local cohomology of a nonzero Noetherian local ring is nonzero`.
  Eight results: the definition `localCohomology.ofSelfLERadical` and unrelated
  local-ring, Krull-intersection, and dimension results; no matching theorem.
- Mathlib grep: `localCohomology|local_cohomology|nonvanishing.*cohomolog`.
  Five hits in `Mathlib/Algebra/Homology/LocalCohomology.lean`, defining the
  Ext-colimit model; no top nonvanishing theorem. Read the complete file,
  including its future-work note about the derived-functor comparison.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `lean/Sheaf`, using those patterns: no upstream theorem; the side library
  contains ideal-power torsion, its derived-torsion/Ext-colimit comparison,
  punctured-spectrum H^1 comparisons, depth-three vanishing, and local
  cohomological dimension. Opened their relevant modules. The torsion functor
  supplies exactly the notion required here, without creating a duplicate.
- `grep -rn 'lem-per-local-cohomology-top-nonvanishing'` in the upstream source:
  no match. A further `rg` for `top_nonvanishing|top.*nonvanishing|nonvanishing.*local`
  found no existing declaration of this result, including in `dag/lean_names_upstream.json`.
- Parsed the DAG's recorded module/declaration fields to locate the existing
  `def-sbc-ideal-power-torsion-functor` and read both its node and full module.

No new nodes, dependency repairs, disputed statements, or statement corrections.
The existing torsion definition is cited by an added dependency only.

## Second reading by Q46

This is the author's second reading; the maintainer supplies the independent review.
Reopened the node and the final module and compared every binder and conclusion.
`CommRing`, `IsNoetherianRing`, and `IsLocalRing` cover exactly the stated ring
conditions, including nonzeroness. The natural d and dimension equality retain
zero and every finite dimension, and explicitly use Spec and topologicalKrullDim.
The existing torsion functor has exactly the annihilation condition, with its
harmless exponent-zero convention checked above. Its degree-d right-derived
functor is evaluated on R, and the conclusion is nonzero in ModuleCat. No
additional cohomological-dimension conclusion was introduced. The docstring
retains all seven proof steps, including completion of the finite module in
local duality and flat base change back to R. The only node delta besides the
Lean record is adding the owning node of the already landed torsion functor.
No mismatch was found and no mathematical statement was changed.

Validation: after adding the explicit public ModuleCat.Abelian import, scompile.py
compiled the sandbox and final library module cleanly (2.7 s and 2.8 s).
The prescribed deliver2.py --no-push passed server preflight and compilation,
printing `OK (dry run)` for commit `97ad6fe7bb`. The signature record matches
the source verbatim, all Lean lines have at most 100 characters, all variables
and the universe are explicitly bound, and the sole theorem has proof `sorry`.
