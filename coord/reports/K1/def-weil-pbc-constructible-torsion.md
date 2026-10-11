## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf` defines
`AlgebraicGeometry.CurveCoefficientPair.IsConstructible`. It specializes the existing
constructibility predicate to the underlying sheaf of sets of a curve coefficient pair.
There are no theorem declarations, no proofs, and no `sorry` in this module.

Hypothesis and clause correspondence:

- The algebraically closed base field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The curve coefficient pair `(C,F)` is the binder
  `(P : AlgebraicGeometry.CurveCoefficientPair k)`. The recorded structure supplies `P.C`,
  `P.toSpec`, `P.isCurve : IsCurve P.toSpec`, `P.F`, and
  `P.isTorsion : P.C.IsTorsionAbelianSheaf P.F`. Thus separatedness, finite type, dimension
  at most one, abelian coefficients on the small etale site, and torsion are retained.
- Forgetting the abelian group structure is Mathlib's
  `(sheafCompose P.C.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj P.F`.
  This is the same sections and restriction functions, not a new coefficient sheaf.
- The finite partition is the existential `S : Scheme.Stratification P.C` inside the
  recorded `Scheme.IsConstructibleEtaleSheafOfSets`. Its `n : ℕ` and index `Fin S.n`
  give finiteness, `iUnion_stratum_eq_univ` gives coverage, and
  `pairwise_disjoint_stratum` gives the partition condition.
- Locally closed strata are `isLocallyClosed_stratum`; constructibility is
  `isConstructible_stratum`; their subschemes and inclusions are `domain`, `immersion`,
  `isImmersion`, and `range_immersion` in that same recorded stratification.
- Restriction on each stratum is the existing `Scheme.etaleSetPullback (S.immersion i)`,
  whose definition is the sheafified left Kan extension along small-etale base change.
- Local constancy is `IsLocallyConstantEtaleSheafOfSets`: an etale cover on which `F.over`
  is constant. Finiteness is `Finite` of each geometric stalk, quantified over all
  algebraically closed geometric points, in `IsFiniteLocallyConstantEtaleSheafOfSets`.
  This is finite cardinality, not finite generation as a module. Constructibility of an
  abelian sheaf is the constructibility of its underlying set sheaf, as in Stacks 03RW(2).

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`:
  `AlgebraicGeometry.CurveCoefficientPair` (full structure and docstring read).
- `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`:
  `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`, through the structure's `isTorsion`
  field (definition and docstring read). No redundant torsion hypothesis is introduced.
- `Sheaf.AlgebraicGeometry.EtaleSheaves`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleSheafOfSets`, with its recorded
  `IsFiniteLocallyConstantEtaleSheafOfSets`, `IsLocallyConstantEtaleSheafOfSets`, and
  `etaleSetPullback` (full definitions and docstrings read).
- Mathlib `CategoryTheory.sheafCompose` and `CategoryTheory.forget`; source
  `AlgebraicGeometry.Scheme.Stratification` and `Topology.Stratification`, used through
  the recorded constructibility definition. Their fields/signatures were read.

Edge cases checked by unfolding the recorded definitions: the empty curve allows the
empty stratification (`n = 0`); a nonempty curve cannot satisfy coverage with zero strata.
The zero sheaf has singleton finite stalks and is locally constant. Dimension-zero,
disconnected, nonreduced, and nonproper curves remain permitted by `IsCurve`; no extra
smoothness, connectedness, properness, or characteristic restriction is imposed.
Infinite torsion stalks do not satisfy `Finite` merely because they are torsion. The
coefficient universe is exactly the pair's recorded `AddCommGrpCat.{u + 1}`, and
forgetting yields `Type (u + 1)` as required by the recorded set-valued predicate.

Searches for existing notions (2026-10-11):

- `msearch.py leansearch`: "constructible torsion abelian sheaf on a curve finite locally
  constant on finite locally closed constructible strata"; service unavailable with
  Internal Server Error (recorded as unavailable).
- `msearch.py leanfinder`: "constructible torsion abelian sheaf on a curve finite
  partition locally closed finite stalks"; eight unrelated quasi-compact/quasi-separated
  scheme section lemmas; no matching curve-pair predicate.
- `msearch.py loogle`: "CategoryTheory.Sheaf, IsConstructible"; no hits, unknown
  identifier `IsConstructible`.
- `msearch.py grep`: "IsConstructibleSheaf|IsConstructibleEtaleSheafOfSets|constructible
  torsion" over Mathlib; no hits.
- `rg` over `WeilConjectures` found `Scheme.IsConstructibleSheaf` in
  `ConstructibleSheaf/Defs.lean`. Reading it shows finite generation rather than finite
  cardinality of stalks; it is unsuitable here (even constant ℤ has finitely generated
  infinite stalks). No tagged declaration for this item or curve-pair constructibility
  predicate was found in the source or `dag/lean_names_upstream.json`.
- `rg` over `lean/Sheaf` found and reused the set-sheaf constructibility predicate in
  `EtaleSheaves.lean`; no existing curve-pair specialization was found.

The blueprint literature checkout is absent on this machine. The node's exact statement
and all dependency source modules were read; the cited mathematical source was checked
online at https://stacks.math.columbia.edu/tag/03RW and
https://stacks.math.columbia.edu/tag/095E. Stacks 095E applies the global finite
stratification criterion on quasi-compact quasi-separated schemes; the curve in the
pair is separated and finite type over a field, hence satisfies those conditions.
No node correction, missing notion, dependency repair, or statement dispute was needed.

## Second reading by K1

I read the item's node and Lean file independently, all three statement-dependency
nodes and their recorded modules, the source `IsCurve`, both source stratification
structures, and the upstream constructible-sheaf declarations. The source literature
checkout is absent here. I read the Stacks `etale-cohomology.tex` directly from
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
section `section-constructible`, including its introductory conventions,
`definition-constructible` (03RW), and
`lemma-constructible-quasi-compact-quasi-separated` (095E). I also checked the
rendered tags https://stacks.math.columbia.edu/tag/03RW and
https://stacks.math.columbia.edu/tag/095E. The introduction permits arbitrary induced
scheme structures on strata by topological invariance. For the global criterion,
095E assumes quasi-compactness and quasi-separatedness; the separated finite-type
curve supplies both. The node itself explicitly asks for a finite global partition.

Object, hypothesis, and clause list, with the Lean correspondence and verdict:

1. An algebraically closed field k, implicit through the curve coefficient pair:
   `{k : Type u} [Field k] [IsAlgClosed k]`. Exact; no characteristic restriction.
2. A curve C over k, separated, finite type and dimension at most one:
   `(P : AlgebraicGeometry.CurveCoefficientPair k)` supplies `P.C`, `P.toSpec`,
   and `P.isCurve : IsCurve P.toSpec`. Reading the source class shows
   `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and
   `topologicalKrullDim C ≤ 1`. Exact; no smoothness, properness or reducedness.
3. An abelian sheaf F on C's small etale site, torsion:
   `P.F : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1}` and
   `P.isTorsion : P.C.IsTorsionAbelianSheaf P.F`. The dependency's canonical
   filtered colimit of multiplication kernels is the node's torsion condition.
   Exact; no extra bounded-exponent hypothesis is introduced.
4. The notion to define is constructibility of this F:
   `CurveCoefficientPair.IsConstructible P : Prop`, applying the recorded
   `Scheme.IsConstructibleEtaleSheafOfSets` to
   `(sheafCompose P.C.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj P.F`.
   This forgets only the additive structure, preserving sections and restrictions.
   Finite local constancy of an abelian sheaf agrees with that of its underlying
   set sheaf: locally the finitely many addition/inverse/zero tables can also be
   trivialized. Thus this is the abelian constructibility clause, not a choice
   of an unrelated set sheaf. Exact.
5. A finite partition of C: unfolding the reused predicate gives
   `∃ S : Scheme.Stratification P.C, ∀ i : Fin S.n, ...`.
   `n : ℕ`, `iUnion_stratum_eq_univ`, and `pairwise_disjoint_stratum` give precisely
   finiteness, coverage and disjointness. The existential partition precedes the
   universal assertion for all its strata. Exact.
6. Locally closed constructible subschemes in that partition:
   `isLocallyClosed_stratum`, `isConstructible_stratum`, `domain`, `immersion`,
   `isImmersion`, and `range_immersion`. The source structure imposes no frontier
   ordering or nonemptiness of individual strata. Exact.
7. Restrict F to each such subscheme:
   `((Scheme.etaleSetPullback (S.immersion i)).obj ... )` is the recorded inverse
   image, constructed by left Kan extension along small-etale base change and
   sheafification. Exact; it is not direct image or mere presheaf evaluation.
8. Local constancy and finite stalks on every stratum:
   `IsFiniteLocallyConstantEtaleSheafOfSets` is the conjunction of an etale cover
   on which `F.over` is constant and `Finite` of every geometric sheaf fiber.
   This is cardinality finiteness, not just finite generation. Exact.

Edge cases: `S.n = 0` is allowed, with coverage forcing the curve to be empty;
empty strata are harmless. The zero abelian sheaf has singleton underlying stalks,
so the predicate has the expected meaning. Dimension-zero, disconnected,
nonreduced and empty curves are not excluded by `IsCurve`. Positive-characteristic
and characteristic-zero fields are equally covered, without prime-to-characteristic
conditions or a specified annihilator n (so no n = 0 side condition). Infinite
torsion stalks do not pass the `Finite` condition. All universes are bound:
`k`, schemes, stratum schemes and geometric-point fields are in arbitrary universe
u; coefficient groups and sets are in u+1, exactly the recorded pair and site
convention. Testing geometric points in universe u suffices since algebraic
closures of residue fields can be formed there, and geometric stalks are invariant
under enlargement of the algebraically closed field. There is no independent,
smaller test-field universe that could make the condition vacuous.

Independent searches (different queries from the worker):

- `msearch.py K1 def-weil-pbc-constructible-torsion leansearch
  "A torsion abelian sheaf is constructible if its underlying sets are finite
  locally constant on a finite stratification"`: service unavailable, Internal
  Server Error; recorded as unavailable, not as evidence of absence.
- `msearch.py ... leanfinder "abelian etale sheaf finite cardinality strata
  constructibility underlying sets"`: eight hits about constructible subsets,
  spectra, and scheme images; no matching sheaf predicate.
- `msearch.py ... loogle '"IsConstructible"'`: twelve results about
  `Topology.IsConstructible` and its operations; no sheaf predicate.
- `rg` for `IsConstructible`, `Constructible.*Sheaf`, constructible torsion,
  and `CurveCoefficientPair` across Mathlib AlgebraicGeometry/CategoryTheory,
  the source, the project's `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing declaration of curve-pair constructibility. I opened the hits
  `Scheme.IsConstructibleSheaf` and `Scheme.IsFiniteLocallyConstantSheaf` in
  `WeilConjectures/ConstructibleSheaf/Defs.lean`. They require abelian coefficient
  categories and finitely generated stalks; they do not give the general
  cardinality-based set-sheaf notion. On torsion abelian stalks finite generation
  does imply finiteness, but that equivalence does not replace the dependency
  node's recorded set-sheaf predicate. The delivered definition reuses that
  predicate, adding only the specialization to the already recorded pair.

No mathematical mismatch found. I left the correct Lean and node record unchanged;
only this independent review section was added. There are no new nodes, dependency
modules, or statement corrections. Both imports are used. The sole definition is
concrete, with no `sorry` or theorem proofs. The module and declaration docstrings
identify the source and blueprint id, and the node has no proof steps to reproduce.
The recorded `lean.statement` is verbatim the definition's signature before `:=`.
Compilation and delivery checks are recorded below.

Validation: `scompile.py K1 def-weil-pbc-constructible-torsion` with the absolute
sandbox module path compiled in 1.8 seconds, exit code 0, without warnings.
`deliver2.py K1 def-weil-pbc-constructible-torsion --no-push` printed OK: the
delivery passes preflight and compiles.
