## Worker report

States `AlgebraicGeometry.exists_proper_geometricFibre_torsion_cohomology_bound` in
`Sheaf.AlgebraicGeometry.Sites.ProperGeometricFibreTorsionBound`. The only postponed
proof is this theorem, whose docstring carries all four DAG proof steps. No definition,
extra theorem, dependency repair, new node or statement correction is needed. The node
copy changes only `lean`.

Hypothesis and clause correspondence, checked against the whole node:

- Schemes and the named morphism `p : X → Y` are `{X Y : Scheme.{u}} (p : X ⟶ Y)`.
- Properness is `[IsProper p]`, the recorded Mathlib definition (separated, universally
  closed and locally finite type; universal closedness also supplies quasi-compactness
  of the morphism, giving finite type).
- Quasi-compactness of the base is `[CompactSpace Y]`, without a separation axiom.
- The uniform nonnegative integer bound is `∃ c : ℕ`, outside every geometric-point,
  sheaf and degree quantifier. Natural numbers are precisely the nonnegative integers.
- Every geometric point is `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (ybar : Spec (.of Ω) ⟶ Y)`. There is no assumption that Ω is algebraic over the
  residue field, so transcendental algebraically closed extensions are included.
- The geometric fibre is the scheme `pullback p ybar`, exactly the base-change
  convention recorded by `def-pc-base-change`, not the set of Ω-valued lifts.
- An arbitrary abelian sheaf on its small étale site is
  `F : Sheaf (pullback p ybar).smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The explicit node meaning of torsion is rendered literally as
  `∀ (U : (pullback p ybar).Etaleᵒᵖ) (s : F.obj.obj U),
  ∃ n : ℤ, n ≠ 0 ∧ n • s = 0`. The annihilator comes after U and s, so no common
  integer annihilator is hypothesized. Opposite objects quantify over every étale
  object and `F.obj.obj U` is its group of sections.
- Every integer degree above the bound is `∀ i : ℤ, (c : ℤ) < i → ...`.
- Ordinary derived-section cohomology is precisely the recorded
  `(Etale.cohomology AddCommGrpCat.{u + 1} (pullback p ybar) i).obj
  ((DerivedCategory.singleFunctor _ 0).obj F)`.
  `Subsingleton` of its underlying additive group says it is zero.
- No `Nonempty`, dimension, Noetherian, constructibility, finite-coefficient or
  invertibility hypothesis is imposed. Thus empty bases and empty fibres are included.

Important interface distinction, not a statement fault: the item's last sentence
specifies that every section itself has finite order. The existing `Sheaf.IsTorsion`
predicate only requires finite order locally on a covering. They are not interchangeable
on this site, which admits non-quasi-compact objects. The recorded upstream
`Scheme.constant_ratModIntSheaf_sections_not_torsion` explicitly illustrates the
failure for Q/Z over an infinite disjoint union. Consequently the theorem uses the
literal sectionwise formula, not the stronger conclusion over all locally torsion
sheaves provided by `HasTorsionEtaleCohomologicalDimensionLE`. The proof input still
applies: sectionwise torsion implies local torsion by the maximal covering sieve.
No change to the node is necessary; its explicit statement is true.

Recorded statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points use the
  node's recorded inline form. Also read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` for the residue-extension interpretation.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: read the whole module,
  especially `baseChange_iterated` and `Scheme.Hom.geometricFiberAt`. The node's own
  record instructs scheme base-change consumers to use `Limits.pullback`, as done here;
  `geometricFiberAt` instead requires a chosen algebraic closure of the residue field
  and would incorrectly restrict this item's arbitrary geometric point.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, with
  `Scheme.smallEtaleTopology` from `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: read the signatures and
  docstrings of `Etale.rightDerivedGlobalSections` and `Etale.cohomology` and their
  coefficient-category assumptions. The latter applied to `singleFunctor _ 0` is
  exactly the ordinary cohomology encoding recorded on the dependency node.

All stated proof dependencies are imported non-publicly unless also a statement
input: `AlgebraicGeometry.exists_fibre_dimension_bound` from
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`;
`AlgebraicGeometry.topologicalKrullDim_fieldExtension_and_denseOpen` from
`Sheaf.AlgebraicGeometry.DimensionExtension`; proper base-change instances in
`Mathlib.AlgebraicGeometry.Morphisms.Proper`; `topologicalKrullDim` from
`Mathlib.Topology.KrullDimension`;
`Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed` from
`Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`;
`Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType` from
`Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension`;
and `Scheme.HasTorsionEtaleCohomologicalDimensionLE` from
`Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`.
Their node statements, records, full declaration signatures and docstrings were read.
No proof import closes a cycle.

Sources read: Stacks morphisms.tex lemma-morphism-finite-type-bounded-dimension
(Tag 0A3V), algebra.tex lemma-dimension-preserved-field-extension (Tag 00P3), and
etale-cohomology.tex proposition-cd-affine (Tag 0F0V); the current blueprint's
sk-thm-sfb-proper-base-change-finite.proof.md paragraph (1), and
thm-sc-finite-type-torsion-cd.proof.md (the Zariski-to-étale spectral sequence bound).
These give the four steps in the declaration docstring: choose the ordinary dimension
bound e, preserve it on geometric fibres, obtain torsion bound 2e, and handle the empty
site separately.

Edge cases checked: empty Y makes the geometric-point quantifier vacuous; empty fibres
have only the zero abelian sheaf by the empty covering; the zero sheaf works in every
degree; c = 0 still tests every positive integer i; negative and zero degrees are not
spuriously required to vanish. No restriction on characteristic or torsion orders is
present. The annihilator depends on the section; none is provided as global data.
The universe u is explicit and polymorphic, with Scheme.{u}, Ω : Type u, and the
recorded AddCommGrpCat.{u + 1} coefficient-size convention. All variables are bound.

Searches actually run through msearch.py for this item:

- LeanFinder: `Uniform torsion etale cohomology vanishing on geometric fibres of a
  proper morphism over a quasi compact scheme`. Eight hits, including
  `AlgebraicGeometry.exists_of_res_zero_of_qcqs_of_top`, affine-transition-limit
  section-vanishing lemmas and étale/formally-unramified facts. No uniform étale
  cohomological fibre bound.
- Loogle: `AlgebraicGeometry.IsProper, "cohomology"`. Zero hits.
- Mathlib grep: `geometric.*(cohomolog|torsion)|cohomolog.*[Ff]ib` under
  AlgebraicGeometry. Zero hits.
- LeanSearch: `Uniform bound on torsion etale cohomology of geometric fibres of a
  proper morphism with quasi compact target`. Eight hits about proper morphisms,
  quasi-compact fibres, and the étale category, with no statement of this bound.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `proper.*(geometric|torsion|cohomolog)|exists.*(geometric.*[Ff]ib|[Ff]ib.*cohomolog)`
  found geometric support and proper-base-change constructions and other
  cohomological results, but no exact theorem. Searches of the torsion and geometric
  fibre interfaces located the shared cohomological-dimension predicates and the
  Q/Z sectionwise-torsion counterexample discussed above. Searching the item id in
  `lean/WeilConjectures` gave no hit. No existing exact attachment was found.

Validation: scompile.py compiled the delivered module on the server both as a sandbox
module and at its intended library module path (2.8 s and 2.6 s respectively), with
no errors or warnings. The prescribed deliver2.py --no-push dry run passed server preflight and
compilation (commit 62bbbf40fbb); the final delivery uses the same wrapper.

## Second reading by Q08

No second reading by a worker: the dispatcher brief prohibits starting other agents;
the maintainer's independent review reads this direct worker delivery. The final
self-check reread the full node and Lean file, in particular the distinction between
sectionwise torsion and covering-local torsion, the arbitrary Ω, the outer uniform
bound, integer degree, ordinary derived cohomology and the empty cases. No mathematical
mismatch was found. No claim of an independent worker review is made.
