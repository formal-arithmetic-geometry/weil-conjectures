## Worker report

States `CategoryTheory.FilteredTwoColimit.comparison_characterization` in
`lean/Sheaf/CategoryTheory/FilteredTwoColimitCharacterization.lean`. This is a single theorem
with four conjuncts, all with `sorry` as the whole proof. The statement, dependencies and
proof plan of the item are unchanged. Repairs the deleted model dependency under §1(B).
No new nodes or statement corrections are needed.

The node and both its main-20261015 blueprint statement and proof were read. The item uses
exactly the comparison functor constructed in its model dependency, rather than an arbitrary
functor equipped with assumptions asserting the desired conclusions.

| Hypothesis or clause | Lean rendering |
| --- | --- |
| Directed preordered set I | `{I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`. Nonemptiness follows the source's directed-index convention, also recorded in the model's earlier independent review. |
| Stage categories | `{C : I → Type u} [∀ i : I, Category.{v} (C i)]`. |
| Ordinary vertex category D | `{D : Type u'} [Category.{v'} D]`. |
| Coherent normalized cocone | `c : CoherentCategoryCocone (C := C) (D := D)`, repaired in the model dependency, extending the recorded `CategoryCocone C D`. |
| The canonical comparison Phi | `comparison c`, with source `Object c` and target `D`, with the object and arrow formulas of the model. |
| 1. Phi essentially surjective iff Obj | `((comparison c).EssSurj ↔ c.toCategoryCocone.EssSurjObj)`. |
| 2. Phi full iff Hom-surj | `((comparison c).Full ↔ c.toCategoryCocone.HomSurj)`. |
| 3. Phi faithful iff Hom-inj | `((comparison c).Faithful ↔ c.toCategoryCocone.HomInj)`. |
| Hence filtered 2-colimit iff Phi is an equivalence | `(c.toCategoryCocone.IsFilteredTwoColimit ↔ (comparison c).IsEquivalence)`. |

The conjunction retains every numbered equivalence separately. The last equivalence has the
orientation of the node. `Functor.IsEquivalence` is Mathlib's fully faithful and essentially
surjective predicate; `Functor.asEquivalence` gives the actual quasi-inverse and natural
isomorphisms. Its converse is supplied by the equivalence instances. No additional assumption
of full faithfulness, a comparison-category structure, or colimit universality is imposed.

Dependencies read and used:

- `det-def-sfb-filtered-two-colimit-model`: module
  `Sheaf.CategoryTheory.FilteredTwoColimitModel`, `CoherentCategoryCocone`,
  `FilteredTwoColimit.category`, and `FilteredTwoColimit.comparison`, all in namespace
  `CategoryTheory`. The recorded module was unavailable locally and through
  `scompile.py --source Sheaf.CategoryTheory.FilteredTwoColimitModel`; it is supplied by this
  delivery's dependency repair.
- `det-def-sfb-filtered-two-colimit-conditions`: module
  `WeilConjectures.CategoryTheory.FilteredTwoColimit`, declaration
  `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` and its exact existing predicates
  `EssSurjObj`, `HomSurj`, `HomInj`. Read the full module and its signatures. Obj uses an
  isomorphism in the inverse direction, which is equivalent by inversion. The Hom-surj equation
  is theta inverse, then Phi_k(g), then theta, exactly the node in Lean composition order.
- The repaired model's recorded cocone dependency uses the same upstream module and
  `CategoryTheory.CategoryCocone`, with fields `T`, `Φ`, `iso`; no duplicate cocone was written.
- The repaired model's category-colimit dependency uses `CategoryTheory.Limits.Cocone`,
  `Limits.IsColimit`, and `CategoryTheory.IsFiltered` from Mathlib. An actual lifted Hom cocone
  is given and its universal property is stated. Read the category-colimit node and Mathlib's
  `Functor.ColimitType`, `ιColimitType`, `ColimitTypeRel`, and `CoconeTypes` interfaces.
- Proof dependency `lem-weil-pbc-filtered-colimit-sets-elementwise`: read its node and the
  signatures/docstrings of `Limits.Types.jointly_surjective` in `Types.Colimits`, and
  `Limits.Types.FilteredColimit.isColimit_eq_iff` / `isColimit_eq_iff'` in `Types.Filtered`.
  The latter module is imported as a proof import in both delivered modules.
- Proof dependency `lem-trf-fully-faithful-ess-surj-equivalence`: read its node and
  `CategoryTheory.Functor.asEquivalence` in `Mathlib.CategoryTheory.Equivalence`.
- Proof dependency `lem-sf-quasi-inverse-hom-bijection`: read its node and
  `CategoryTheory.Equivalence.mk`, `fullyFaithfulFunctor`, and
  `Functor.FullyFaithful.map_bijective`. No triangle identities on input isomorphisms are added.

Edge cases checked before writing and again after compilation:

- Singleton index: normalization identifies T_ii with identity and theta_ii with identity;
  the assertions specialize to the usual full/faithful/essentially-surjective properties of
  the sole vertex functor.
- Empty stage categories and empty Hom sets are allowed. If all stages are empty, the pair
  category is empty. Fullness and faithfulness and their two Hom conditions are vacuous; Obj
  and essential surjectivity hold exactly when the vertex is empty.
- Empty I is excluded by the source's nonempty directed convention, not accidentally by a
  choice of representatives. No stage category or vertex is assumed nonempty.
- Distinct stages, equality arising only at a later stage, and non-antisymmetric preorders
  are supported. No linear order, supremum operation or finite-stage faithfulness is assumed.
- The five universes are independent. Pair objects live in `Type (max w u)` and Hom colimits
  in `Type (max w v)`. The `ULift` in the actual Hom cocone only moves the stage sets into that
  same universe; no bound on the size of I relative to the category universes is imposed.
- Zero objects, characteristic and integer degrees do not enter this categorical statement.

Searches made on this run (all msearch commands use group NI and this item):

- LeanFinder query: "The comparison functor from a filtered colimit category is essentially
  surjective full and faithful exactly when objects morphisms and equalities descend to a
  stage". Eight hits included `Functor.ιColimitType_eq_iff_of_isFiltered` and its primed
  variant, `Functor.EssSurj`, and generic filtered-finality lemmas. The set-colimit equality
  criterion is useful but is not this category comparison theorem or model.
- Loogle query: `CategoryTheory.Functor.IsEquivalence, CategoryTheory.Functor.EssSurj`.
  Four hits: `Functor.IsEquivalence.essSurj`, `IsEquivalence.mk`, a quotient functor equivalence,
  and a localization property. They provide only the general categorical criterion, not the
  comparison theorem; the actual `Equivalence` source was read.
- Mathlib grep through msearch, scope `CategoryTheory`, query
  `CoherentCategoryCocone|IsFilteredTwoColimit|FilteredTwoColimit`: zero hits.
- LeanSearch query: "The comparison functor from the category of pairs of a coherent directed
  system of categories is essentially surjective full and faithful if and only if objects
  morphisms and equalities descend to stages". Eight hits concerned comma functors, comonad
  comparisons and prestack descent, none this model or characterization.
- `rg -n 'CoherentCategoryCocone|namespace FilteredTwoColimit|homTransition|HomRepresentative'`
  in `lean/WeilConjectures` and `lean/Sheaf` found unrelated Hom representatives and transition
  fields, no definition of the deleted model or this comparison theorem.
- `grep -rn 'det-def-sfb-filtered-two-colimit-characterization' lean/WeilConjectures`:
  no hits. `rg 'TwoColimit|two.colimit' lean/Sheaf/CategoryTheory` found the upstream cocone
  import and unrelated coefficient-colimit material, no characterization declaration.
- Read `coord/reports/Q69/det-def-sfb-filtered-two-colimit-model.md`: it documents the former
  concrete model, its source normalization and independent universe choices. The replacement
  keeps those same mathematical constructions, using the actual current dependency interfaces.

All fifteen law theorems in the model belong to the definition node's explicit proof steps:
`homTransition_id`, `homTransition_comp`, `homClass_transition`, `homCocone_isColimit`,
`commonStage_isFiltered`, `homClass_eq_iff`, `compRepresentative_eq_compAt`,
`compRepresentative_rel_right`, `compRepresentative_rel_left`, `identity_comp`, `comp_identity`,
`comp_assoc`, `mapHomRepresentative_rel`, `mapHom_identity`, `mapHom_comp`. Each is listed in
its node's `lean.declarations`, has a source and proof plan, and has whole proof `by sorry`.
The item theorem is the sixteenth postponed theorem. No definition's data is `sorry`.

## Dependency modules

`det-def-sfb-filtered-two-colimit-model`: the old `lean` record names
`Sheaf.CategoryTheory.FilteredTwoColimitModel`, but its note records deletion on 2026-10-20.
The live-source wrapper confirms "Module source unavailable". This is an unusable recorded
interface, repaired under §1(B), not a new notion. The node copy changes only `lean`, including
the required explanation in `lean.note`. Its module reconstructs the source's precise model:

| Model clause | Declaration or field |
| --- | --- |
| Original cocone data | `CoherentCategoryCocone extends CategoryCocone C D`. |
| Associators T_ij then T_jk isomorphic to T_ik | `tau hij hjk`. |
| T_ii = Id | `transition_identity`. |
| theta_ii = identity | `cocone_identity`, heterogeneous equality accounting for the normalized domain. |
| tau_iij and tau_ijj = identity | `tau_identity_left`, `tau_identity_right`, likewise heterogeneous equalities. |
| Four-index cocycle | `tau_cocycle`, equality at each component, with the same two composites. |
| Compatibility with the cocone | `compatibility`, Phi_k(tau inverse), then theta_jk, then theta_ij. |
| Pair objects (i,x) | `Object c := Σ i : I, C i`. The parameter c selects the associated category instance. |
| Common-stage index k >= i,j | `CommonStage i j` with `commonStagePreorder`. |
| H_k and t_kk' | `HomAt`, `homTransition`; the latter is tau at the source inverse, T(g), then tau at the target. |
| Filtered set-colimit Hom | `homDiagram`, `HomSet := (homDiagram ...).ColimitType`, `homClass`, `homCocone`, `homCocone_isColimit`, `commonStage_isFiltered`, `homClass_eq_iff`. |
| Composition at any common upper stage | `compAt`; `compRepresentative` chooses an actual upper bound from Mathlib's proved directedness lemma; `compRepresentative_eq_compAt` states independence of that choice. |
| Independence of representatives | The two `compRepresentative_rel_*` theorems justify the actual `Quot.liftOn₂` in `compHom`. |
| Identity [i,id_x] | `identityHom`, using the identity of T_ii(x), identified with x by normalization. |
| Category laws | `identity_comp`, `comp_identity`, `comp_assoc`, assembled into `category`. |
| Comparison objects | `comparison.obj a := (c.Φ a.1).obj a.2`. |
| Comparison arrows | `mapHomRepresentative`, descended by `mapHom`, using exactly theta inverse, Phi(g), theta. |
| Well-defined comparison functor | `mapHomRepresentative_rel`, `mapHom_identity`, `mapHom_comp`, assembled into `comparison`. |

Only proofs of specified laws are postponed. The category, quotient Hom sets, composition,
identity, comparison and universal cocone are real constructions. Neither the category nor the
comparison is chosen from an arbitrary existential theorem or an assumed Hom equivalence.

## Second reading by NI

A separate review pass by this worker re-opened both node statements, the current blueprint
model and characterization statements, both delivered modules, and the existing three cocone
predicates. The dispatcher explicitly prohibits starting another agent; independent review of
the delivery is performed by the maintainer, rather than claimed to have occurred here.

The four conjuncts match the three numbered source assertions and its final sentence in their
stated orientations. The model's tau conjugation, cocone comparison equation, pair objects,
common-stage composition, identity and comparison formulas were checked in Lean's
left-to-right composition order. The HEq normalizations express exactly the identity comparisons
across the equal normalized functor domains; they introduce no extra strictness assumption.
Every independent universe remains bound explicitly. The `Object` parameter does not change
the pair data and makes the category instance nameable by its coherent cocone.

During this pass, directedness was made explicit in the two helper signatures
`commonStage_isFiltered` and `homClass_eq_iff`. Recompilation showed that Lean had already
retained the earlier section instances, producing duplicate-instance warnings. The section
binders were therefore moved below these two explicitly bound helpers. Each helper now has
one directedness hypothesis; no linter was disabled. These helpers need no separate nonempty
index hypothesis because their supplied endpoint indices already witness nonemptiness.
The main theorem explicitly retains the source's nonempty directed index convention. No source
statement or node dependency needed correction.

The empty-stage and singleton cases, later equality, and preorder versus partial-order issue
were rechecked. No mathematical statement dispute remains.

## Validation

Both delivered files were compiled separately in dependency order with the prescribed
`scompile.py NI det-def-sfb-filtered-two-colimit-characterization` wrapper, against the live
published library. The complete model compiles in about 2 seconds and the characterization
in about 1 second, with no errors or warnings. No global build, live-source edit, or direct Git
command was run. Delivery preflight and the final push are performed through `deliver2.py`.
