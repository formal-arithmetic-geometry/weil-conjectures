## Worker report

The module `Sheaf.CategoryTheory.FilteredCyclicComparisonTransfer` states
`CategoryTheory.RelativeCyclic.filtered_cyclic_comparison_transfer`, with its entire
proof `sorry`. The six helper definitions assemble the existing ordinary derived-invariant
functor, the existing relative cyclic total with trivial residual action, its actual cyclic
restriction comparison, and the two integer-indexed cohomology functors. They introduce no
new action category, total model, invariant functor, localization or independent notion.
All definition data is explicit composition of recorded functors and canonical maps.
Only the assigned node's `lean` field changes; its statement, dependencies and proof stay
verbatim. No dependency repair, new node or statement correction is needed.

Hypotheses and clauses, individually:

- The arbitrary commutative condensed ring R is `A : CondensedBar.Ring.{u}`. This is
  `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})`; its underlying
  `A.toMon` is precisely `Profinite.CondensedRing` with bundled commutativity. No
  topological presentation, discrete coefficient ring or solidification is imposed.
- Profinite H is `{H : Type u}` with `Group`, `TopologicalSpace`, `IsTopologicalGroup`,
  `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`.
- The continuous homomorphism from the discrete integers is `v : Z.{u} →ₜ* H`;
  the dependency's `Z` is `Multiplicative (ULift.{u} ℤ)` with the discrete topology.
  Its positive `generator` represents 1, so the induced differential is v(1)-1.
- Ordinary internal modules are the existing `CondensedBar.Modules A`, transparently
  `Profinite.CondensedAction.Modules A.toMon`, hence the recorded `CategoryTheory.Mod`.
  The input action modules are exactly `Equivariant A H`, an abbreviation of the
  recorded `Profinite.CondensedAction.ActionModule A.toMon H`.
- Ordinary full-action derived invariants on N[0] are `cyclicComparisonSource A`, namely
  `DerivedCategory.singleFunctor _ 0 ⋙ CondensedDerivedRestriction.derived A H`.
  The derived Hom universe is explicitly u+1, matching the published small-Hom interface.
- K(N) is `cyclicComparisonComplex A K v`: restrict along v, use
  `addTrivialResidual A`, put the module in degree zero, apply `K.functor`, then forget
  the residual `PUnit.{u + 1}` action. `TotalModel.coordinates` gives N^n plus N^(n-1),
  so for a single module only degrees 0 and 1 remain; `TotalModel.differential` gives
  the positive generator minus identity from degree 0 to 1. Its `maps` field fixes the
  functorial diagonal maps. `cyclicComparisonTarget` applies `DerivedCategory.Q`.
- `{K : TotalModel A PUnit.{u + 1}}` and `C : HasComparison A PUnit.{u + 1} K` name
  precisely the normalized model specified by the dependency. They are representation
  data, available for every A by `relative_cyclic_restriction_model A PUnit`, without
  any restriction on A, H, v or N. The statement holds for every such normalized model;
  no arbitrary uncharacterized comparison map is an input.
- The specified c_N = lambda_N inverse after beta_N is `cyclicComparison A C v N`.
  Its first factor is the canonical scalar `CondensedDerivedRestriction.groupMap A v`.
  The exact single-complex identification puts its codomain in the prescribed degree-zero
  form. The following two maps insert the identity-normalized trivial residual action:
  `unitResidualIso.inv` on the single module, then
  `HomologicalComplex.singleMapHomologicalComplex ... .inv`. The last factor is
  `(forgottenLambda A PUnit C ...).inv`. `forgetBeta` identifies this scalar restriction
  with the forgotten relative beta; `forgottenLambda` is the recorded relative lambda
  with the same exact localization transports. Thus this is the actual c^1, with no
  replacement by a chosen arrow or an assumed isomorphism.
- The compatible small nonempty filtered category is `(I : Type (u + 1)) [SmallCategory I]
  [IsFiltered I]`. `IsFiltered` includes nonemptiness. No poset or monic-arrow condition
  replaces a general filtered category.
- The arbitrary diagram is `N : I ⥤ Equivariant A H`, and the induced-action sheaf
  colimit is `colimit N`. The existing `forgetCreatesFilteredColimit A H I N` identifies
  its underlying internal module with the sheaf colimit and identifies its actual legs.
  Colimit existence follows from the published Grothendieck abelian instances, not an
  extra hypothesis.
- Every integer q is quantified as `∀ q : ℤ`. `cyclicSourceCohomology A q` and
  `cyclicTargetCohomology A K v q` apply `DerivedCategory.homologyFunctor` to the above
  functors; cochain homology is the cohomology in the node.
- The actual a_q is `colimit.post N (cyclicSourceCohomology A q)`; b_q is
  `colimit.post N (cyclicTargetCohomology A K v q)`. The first two conjuncts assert
  `IsIso` for precisely these arrows, equivalently isomorphisms with these forward maps.
  `colimit.ι_post` gives each leg exactly as the corresponding cohomology functor applied
  to the original action-module coprojection. No alternative colimit cocone is substituted.
- The output witness `m` is colim_i H^q(c_i). Its type is the exact source-to-target
  cohomology-colimit arrow. The equation for every `i : I` fixes its composite with each
  coprojection to `H^q(c_i)` followed by the target coprojection. These equations uniquely
  determine m by the colimit universal property; m is an output, never an assumed map.
- The next equation is `a_q ≫ H^q(c_colimit) = m ≫ b_q`, which is exactly the displayed
  square in Lean's left-to-right composition convention.
- For `q < 0` the four `IsZero` assertions state zero objects for the source and target
  of a_q and the source and target of b_q. They do not mistakenly assert vanishing of
  arbitrary higher invariant cohomology.
- The final implication takes `∀ i : I, IsIso (cyclicComparison ... (N.obj i))` and
  concludes `IsIso (cyclicComparison ... (colimit N))` in the ordinary derived category,
  not merely a cohomological assertion.
- No extra injectivity, finite generation, nilpotence, norm/completeness, density of v,
  or uniform cohomological-dimension condition appears. Colimits take place in the
  actual internal module/action categories, not spaces of topological sections.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; the commutative
  specialization `CondensedBar.Ring` is from the relative model's public imports.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.forget`,
  `Mod.regular`, through the recorded internal module category.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.ActionModule`, `Modules`, `inflate`, `forgetAction`;
  these supply the same internal generalized-section actions as the node.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the size convention is metatheoretic and
  is rendered by the explicit universes, not a duplicate definiendum.
- `Sheaf.CategoryTheory.RelativeCyclicRestrictionModel`:
  `CategoryTheory.RelativeCyclic.relative_cyclic_restriction_model`, together with its
  published `TotalModel`, `HasComparison`, `cyclicMap`, `forgottenLambda`, `forgetBeta`,
  `single`, `addTrivialResidual`, `unitResidualIso` and the exact scalar restriction
  `CondensedDerivedRestriction.groupMap` reexported by that module. Read the complete
  signatures/docstrings, especially the total's coordinates/differential/maps and the
  invariant-unit normalization of `HasComparison`.
- Proof-only imports `Sheaf.CategoryTheory.ProfiniteInvariantsFilteredContinuity`
  (`higherInvariants_filteredColimit_isIso`, `forgetCreatesFilteredColimit`),
  `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`
  (`SheafOfModules.filteredColimitsTensorComplex`),
  `Sheaf.CategoryTheory.ArrowExactColimits` (`Limits.arrow_exact_colimits`),
  `Sheaf.CategoryTheory.CondensedDerivedInvariantBar` (`condensed_derived_invariant_bar`),
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
  (`DerivedCategory.isIso_iff`). The proof docstring records all five DAG proof steps.

Edge cases checked before writing: the zero ring and zero module give zero objects
throughout; H=1 and the trivial homomorphism are allowed, without asserting c is always
invertible (for a nonzero trivial module the cyclic target can have degree-one cohomology).
The singleton filtered category gives identity colimit comparisons. Noninjective
transition maps and filtered categories with parallel arrows remain allowed. Empty I is
excluded exactly by filteredness/nonemptiness in the node. For q<0 all four comparison
objects vanish; at q=0,1 the cyclic cohomology is respectively kernel/cokernel of tau-1;
for q>1 only the cyclic target is forced zero. No dimension bound on the source is added.

Searches for reuse (2026-10-24):

- `msearch.py ... leanfinder "The canonical cyclic restriction comparison for condensed
  profinite action modules commutes with filtered sheaf colimits and remains an isomorphism
  under filtered colimits"`: eight hits, including `Condensed.profiniteSolid`,
  `Condensed.isoLocallyConstantOfIsColimit`, and `CondensedMod.ofSheafProfinite`;
  none states this comparison square or transfer theorem for internal condensed rings.
- `msearch.py ... leansearch "Canonical cyclic restriction comparison for internal condensed
  profinite group modules commutes with filtered colimits"`: eight hits, including
  `Limits.colimitLimitIso`, ordinary module filtered-colimit constructors and their
  universal-property lemmas; none states the assigned theorem.
- `msearch.py ... loogle "colimit.post, colimMap, IsIso"`: zero hits, with unknown identifier
  `colimit.post` in that search index. Retried the established query
  `"rightDerived", "preservesColimitsOfShape"`: zero hits.
- `msearch.py ... grep "(cyclic|invariants).*(filtered|colimit)" RepresentationTheory`:
  zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for cyclic comparison and filtered
  continuity found the existing relative model, total, trivial-map specialization and
  profinite continuity theorem used here, but no combined square/transfer statement.
  `grep -rn` for the assigned node id in `lean/WeilConjectures` returned no hits.
- Exact identifier searches over `dag/lean_names_upstream.json`, both library roots,
  and Mathlib's CategoryTheory/Condensed/RepresentationTheory trees found no clash for
  the seven new declaration names.

Source reading: used `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`.
Its paragraph (3) now delegates the open case to `sk-prop-open-coefficients`; the assigned
node explicitly records this filtered-passage theorem as an agent-formulated auxiliary
obligation with exact external reference wanted. This provenance is retained in the
module docstring. No mathematical fault or statement dispute was found.

Validation: compiled the module separately through the prescribed `scompile.py`, both
in sandbox mode and at its actual library module name, with no errors or warnings.
The final delivery dry run and push are through `deliver2.py`. No live file was edited,
no direct Git command or global build was run, and no other agent was started.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
