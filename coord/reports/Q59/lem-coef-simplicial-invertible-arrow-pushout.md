## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialInvertibleArrowPushout` states
`SSet.Bergner.simplicial_invertible_arrow_pushout`, with its sole proof `sorry`.
No definitions or other postponed theorems are added. The node statement is unchanged.

Clause-by-clause correspondence:

- Small simplicial categories: `SCat.{u}`, the existing bundled Mathlib enrichment
  with the project's `sCatCategory`. The universe `u` is explicit and arbitrary.
- The Bergner model structure: `M : BergnerModelData.{u}`. Its fields assert the model
  axioms, Dwyer–Kan weak equivalences, Bergner fibrations, and the left-lifting
  characterization of cofibrations against trivial fibrations. This is precisely
  the model structure assumed in the node, not a coherent-nerve comparison hypothesis.
- The discrete walking arrow A: `walkingArrow.{u}`, definitionally
  `bundle (U (𝟙_ SSet.{u}))`. Its two labels are `ULift.up false` and `ULift.up true`;
  its forward vertex is `PUnit.unit`, its reverse mapping set is empty, and its
  identity mapping sets are the tensor unit.
- The discrete walking isomorphism J: `walkingGroupoid.{u}` has the same labels and
  the tensor unit as each of its four mapping sets. `adjoinInverse.{u}` is identity
  on labels and the unique map on each mapping set, so it sends the forward vertex
  to the distinguished isomorphism.
- Any factorization: `E`, `j : walkingArrow ⟶ E`, `q : E ⟶ walkingGroupoid`, and
  `hfactor : j ≫ q = adjoinInverse`. No fibrancy or fixed-object condition on E is used.
- The two factorization conditions are `hj`, membership in M's cofibrations, and
  `hq : dwyerKanEquivalences q`; q need not be a fibration.
- The arbitrary category C and functor f are explicit binders `C` and `f`.
- Invertibility of [f(a)] in π₀C is `hf : IsEquivalenceVertex
  (EnrichedCat.str (V := SSet) C) ((f.map ...).app _ PUnit.unit)`. The recorded
  predicate asks for an actual reverse vertex whose two composites have the same
  components as identities. It uses components, not strict inverse equations.
- The ordinary pushout and canonical map are rendered by arbitrary `P`, `c : C ⟶ P`,
  `e : E ⟶ P`, and `hpushout : IsPushout f j c e`. Mathlib's predicate asserts both
  commutativity and the ordinary categorical universal property. Thus c is the
  canonical coprojection, up to the unique pushout isomorphism; there is no choice
  of an unrelated comparison and no homotopy-pushout substitution. Quantifying over
  all such squares avoids an auxiliary colimit-instance assumption and covers the
  chosen ordinary pushout in the node.
- The conclusion is exactly `dwyerKanEquivalences c ∧
  M.model.categoryWithCofibrations.cofibrations c`.
- There is no cofibration condition on f, no local Kan condition on C, and no
  inequality between its two image objects.

Dependencies and declarations read and used:

- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.Fixed`, `bundle`, `U`, `Two`, `IsEquivalenceVertex`, and
  `simplicial_interval_lifting`. Read the constructions and the full theorem.
- `Sheaf.AlgebraicTopology.SimplicialIntervalCellStability`:
  `SSet.Bergner.dwyerKanEquivalences`, which bundles the existing
  `CategoryTheory.DwyerKanEquivalence`, and `simplicial_interval_cell_stability`.
- `Sheaf.CategoryTheory.CoherentNerveComparison`, supplied through those imports:
  `CategoryTheory.BergnerModelData` and the component-equivalence predicates.
- `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`:
  `CategoryTheory.SimplicialLocalizationCalculus.walkingArrow`, `walkingGroupoid`,
  `adjoinInverse`. Read all three definitions. Only these constructions are used;
  the localization-comparison theorem is not an input to this theorem's proof.
- Mathlib's `CategoryTheory.Limits.IsPushout`, with arbitrary enriched functors in SCat.

Proof-only imports cover the stated recorded proof dependencies:
`BisimplicialDiagonalEquivalence`, `CountableEquivalenceWitness`,
`FixedObjectScatLeftProper`, `RealizationFiniteLimits`, `SortedSimplicialAlgebraModel`,
and Mathlib's `BrownLemma` and `MorphismProperty.LiftingProperty`.
The two proof dependencies `lem-coef-cofibrant-localization-diagonal-nerve` and
`lem-coef-groupoidal-cofibrant-nerve-detection` have no recorded modules in the read
snapshot, so there are no imports to add for those statements. They are not needed
for the type of this statement. The theorem docstring carries all nine DAG proof
steps, including both uses.

Import-direction note: the existing walking-arrow/groupoid definitions are owned by
`lem-coef-simplicial-localization-comparison-calculus`, which reaches this item through
walking-groupoid-components. That module is imported solely for its real definitions,
not its theorem. Do not add a reverse proof import through that chain: it would close
an import cycle (stages/2-statements.md §3.7). No dependency edge to that downstream
statement is added. Its definitions already express the exact required objects, so
copying them here would violate the one-definition rule. Its theorem was not used
to establish any of this statement's hypotheses or definitions.

Edge cases checked before writing: coincident endpoints of f are allowed; the vertex
predicate still states inverse equations in the single endomorphism simplicial set.
The identity vertex is included. Empty C cannot admit f from the two-object A, so the
quantification is correctly vacuous there. Non-Kan C is allowed because components
and the reverse-vertex condition are defined for every simplicial set. Arbitrary
cofibration factorizations E are retained, including ones with additional objects;
q need only be a Dwyer–Kan equivalence. The conclusion retains both clauses for every
ordinary pushout representative. Object and mapping simplices share the arbitrary
small-category universe already used by the recorded dependency, without a bound on u.

Searches:

- `msearch.py leanfinder`, query “Adjoining a coherent inverse to an invertible arrow
  in a simplicial category is a Dwyer Kan equivalence pushout”: eight unrelated Cech
  nerve/conerve results, no match.
- `msearch.py loogle`, query `SimplicialCategory, DwyerKanEquivalence, IsPushout`:
  zero hits, unknown identifier SimplicialCategory.
- `msearch.py leansearch`, query “simplicial category pushout adjoining inverse
  invertible arrow Dwyer Kan equivalence”: eight unrelated simplicial-object and
  simplex-category results, no match.
- `msearch.py grep`, query `invertible.arrow.pushout|Bergner|Dwyer.Kan|homotopy.coherent.inverse`:
  zero Mathlib hits. Also searched source WeilConjectures and upstream name index
  for the item id, Bergner and DwyerKan; no exact theorem found.
- `rg` over `lean/Sheaf` found the recorded enrichment/DK definitions and existing
  walkingArrow, walkingGroupoid and adjoinInverse constructions. Reused them.
  `SimplicialCategoryBergnerLeftProper` concerns cobase change of a weak equivalence,
  not this theorem: A→E need not itself be a weak equivalence.
- Read Mathlib SimplicialCategory.Basic and SimplicialSet.CoherentIso: the latter's
  WalkingIso is an ordinary category and its nerve; it does not state this assertion.

Source checked: HTT PDF fetched from the IAS mirror, Appendix A.3.2.12–A.3.2.18,
printed pp. 862–863. Remark A.3.2.14 specifies the cofibration/weak-equivalence
factorization of A→J and the ordinary pushout; Example A.3.2.18 supplies invertibility
for simplicial sets. No statement correction or disputed statement is needed.

Validation: the prescribed scompile.py compiled the sandbox and final library module
cleanly, with all variables explicitly bound. The first elaboration attempt needed
`(V := SSet)` on EnrichedCat.str; the corrected signature compiled without warnings.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
