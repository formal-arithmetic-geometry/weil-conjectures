## Worker report

The module `Sheaf.Paper.SfConstructibleCanonicalCompleteness` states
`AlgebraicGeometry.Scheme.sfConstructibleCanonicalCompleteness`,
`sfConstructibleCanonicalReflectorComplete`, and
`sfIntegralConstructibleCanonicalCompleteness`. All three proofs are `sorry`.
There are no definitions, additional nodes, dependency repairs, or statement changes.

Clause-by-clause correspondence:

- The arbitrary scheme is `X : Scheme.{u}`. The coefficient ring is
  `A : Type (u + 1)` with `[CommRing A]`, and `d : AdicCoefficientDatum A`
  contains exactly the Noetherian, finitely generated ideal, torsion first quotient,
  finite positive quotient and perfect positive quotient hypotheses. No completeness
  of A, properness, nonemptiness, or finiteness condition on X is added.
- The actual ambient object is `M : PbcCompletedDerived X d`, the derived category
  of module sheaves over the actual limit ring `pbcAdicCompletion X d`, equivalently
  `d.completedRing X`. The site retains object universe u+1 and Hom universe u.
- The specified scalar-preserving coefficient presentation and its derived functor
  occur inside the reused predicate `PbcIsIntrinsicallyComplete X d M`.
  Unfolding it gives precisely an existential `r`, tuple `f : Fin r → A`,
  equality `Ideal.span (Set.range f) = d.ideal`, presentation complex `C`,
  isomorphism from its localization to
  `(pbcDerivedExtend (pbcCompletedComparison X d).inv).obj M`, and
  `IsCompletedIntrinsicallyDerivedComplete ... C e`. The latter is invertibility
  of the published localized Koszul fiber (u,0) unit. This is the witness the
  node explicitly identifies with the first constructible membership condition;
  no arbitrary equivalence or completion map is substituted. The Cech form of
  the coefficient equivalence is the imported
  `completed_constant_coefficient_equivalence`.
- The main theorem's first conjunct quantifies over EVERY `r : ℕ`,
  `a : Fin r → A`, generation equality `ha`, actual completed-coefficient
  cochain complex `D`, and EVERY `i : DerivedCategory.Q.obj D ≅ M`.
  Its conclusion is exactly
  `IsIso (intrinsicCompletionUnit X d r a ha M D i)`, the supplied-realization
  actual Koszul unit. There is no condition relating these choices to the
  existential witnesses.
- The main theorem's second conjunct is `d.TowerComplete X M`. By its published
  definition it means invertibility of `d.completionUnit X M`, namely the unit
  of the derived constant-tower/limit adjunction followed by the derived limit
  of `completedReductionAugmentation`. That augmentation is an abbreviation
  for `completedReductionTowerUnit`; this is the strict quotient unit in the node.
- The second theorem states the explicit "in particular" clause as
  `WfIsComplete X d r a ha M` for any stipulated generating tuple. Its definition
  is the same actual unit at `wfCompletionRepresentative X d M` and
  `DerivedCategory.Q.objObjPreimageIso M`. It adds no reflector universal-property
  assumption.
- The last theorem states the integral conclusion using the recorded
  `pbcBoundedConstructibleComplete X l E hdim hl`. Its binders are exactly a
  prime l, finite extension E of Q_l in Type(u+1), a Noetherian X, finite
  dimension, and invertibility of l on X, as required by that category.
  Its datum `pbcPadicCoefficientDatum l E` is the actual valuation ring and
  uniformizer ideal. For every object M it concludes tower completeness of
  `M.obj` and `WfIsComplete` for every generating tuple. The arbitrary-representative
  assertion also applies to M.obj through its first membership condition, by the
  main theorem. No uniform-constructibility or origin data is imposed beyond
  membership in the already specified integral category.

Dependency declarations and modules read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`,
  `reductionModules`, `reductionDerivedCategory`, and the datum-indexed completed
  ring and derived-category abbreviations. `AdicCoefficientDatum` is the
  published structure from `Sheaf.Paper.CompletedAdicCoefficientDatum`.
- `Sheaf.Paper.CompletedConstantCoefficientEquivalence`:
  `completed_constant_coefficient_equivalence`, preserving scalars and strict
  quotient units under the specified presentation equivalence.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete`,
  `pbcPadicCoefficientDatum`. Its supporting module
  `Sheaf.Paper.BoundedConstructibleComplete` supplies
  `PbcCompletedDerived`, `PbcIsIntrinsicallyComplete`, and the three membership
  conditions. The main hypothesis uses precisely its existential witness.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`, `completedIntrinsicCompletionMap`,
  and `completedKoszulUnitComplex`. `Sheaf.Paper.IntrinsicCompletion` supplies
  their transported actual-ring form `intrinsicCompletionUnit` and
  `IsDerivedCompleteIntrinsic`.
- `Sheaf.Paper.WeilCompletedTensorReflector`: `wfCompletionReflector`,
  `wfCompletionRepresentative`, `wfCompletionUnit`, and `WfIsComplete`.
- The recorded completed-pullback module
  `Sheaf.Paper.PbcQbarCompletedPullback` retains the actual strict-tower interface
  by public imports. Its ambient canonical completeness definitions are in
  `Sheaf.Paper.CompletedPullback`: `AdicCoefficientDatum.completionUnit`,
  `AdicCoefficientDatum.TowerComplete`, and `completedReductionAugmentation`.
  No Qbar specialization is used for the arbitrary-datum theorem.
- Proof imports are `Sheaf.Paper.PbcIntrinsicTowerComplete`
  (`pbcIntrinsicComplete_towerComplete`) and
  `Sheaf.Paper.CompletedKoszulQuotientComparison`
  (`completedKoszulQuotientComparison`). Their full signatures and proof
  docstrings were read. The former proves the tower clause directly; the latter
  identifies each actual Koszul unit with this same tower unit after an isomorphism.

Sources checked: the current main-20261015 blueprint's
`sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product.md`, the node's reviewed
four-step proof, Stacks algebraization.tex `lemma-derived-completion-koszul`
(Tag 0A0E), and proetale.tex `lemma-naive-completion` (Tag 099M). The existing
`wfConstructible_complete` in `Sheaf.Paper.WeilTensorProduct` is only the
canonical-representative constructible specialization; it does not state the
arbitrary-object/arbitrary-representative assertion or the strict tower clause,
so it is not an exact existing match for this node. Its private
`wfComplete_of_presentation` likewise only treats the fixed canonical representative.

Edge cases checked before writing:

- r=0 is allowed whenever the generation equality holds (I=0); no positive
  length or nonzero generator is required.
- Redundant, repeated and zero generators are allowed; all finite tuples enter
  solely through the stated ideal-span equality.
- The zero ring, I=A, and the zero object are not excluded. In the whole-ideal
  case the completed coefficient ring and its module category can be zero;
  the theorem retains its actual ambient category rather than introducing an
  unjustified nontriviality assumption.
- Empty schemes and all characteristics are allowed in the main theorem. For
  the integral theorem only the category's original scheme-level invertibility
  hypothesis is present, which also makes sense on the empty scheme.
- D can be unbounded, and i can be any isomorphism with the prescribed endpoints.
  No K-flat or K-injective condition is added to the representative.

Searches (all through the prescribed msearch wrapper, Q38 / this item):

- LeanFinder: "An intrinsic Koszul completeness witness for a completed
  coefficient sheaf implies invertibility of the canonical actual completion
  unit for every generating tuple and representative". Eight hits, including
  BDeRham, BDeRhamPlus, ModuleCat.Tilde.isUnit_toStalk, ordinary adic-completion
  lifting and precompleteness lemmas; no derived sheaf unit statement.
- Loogle: `"DerivedCategory", "completion"`. Zero hits.
- Mathlib grep: `intrinsic.*[Cc]omplet|[Kk]oszul.*[Cc]omplet|towerComplete`.
  Zero hits.
- LeanSearch: "An intrinsic completeness witness implies invertibility of every
  actual Koszul derived completion unit of sheaves of modules". Eight hits,
  all ordinary AdicCompletion / IsAdicComplete statements; no match.
- `rg` in `lean/WeilConjectures` for `PbcIsIntrinsicallyComplete`,
  `towerComplete_iff_intrinsic`, `intrinsicCompletionUnit`, and this node id,
  plus `grep -rn` of this node id: zero hits.
- `rg` in `lean/Sheaf` found the reused Pbc intrinsic/tower implication,
  `towerComplete_iff_intrinsic`, actual Koszul comparison, and the downstream
  fixed-representative `wfConstructible_complete`. None states the whole node;
  their existing notions and maps are reused rather than copied.
- No repair note exists for this item.

Validation: the prescribed `scompile.py` compiled this single module both as a
sandbox module and at its library module name against the live published build,
with no errors or warnings (6.9 s and 9.1 s). No local/global build was run.

## Second reading by Q38

A separate cross-check pass by this worker compared the node with all three
signatures and the definitions just listed; the dispatcher instruction forbids
starting another agent, and the maintainer supplies the independent review.
The main theorem has the exact existential-presentation hypothesis and the
universal actual-unit and tower conclusions. The second signature explicitly
retains the canonical-reflector choice, and the third uses the recorded integral
category with its original coefficient and base hypotheses. The coefficient
universe remains one above the scheme universe. No mismatch or statement fault
was found, and no definition or unit was replaced. The source's four proof steps
are reproduced across the three theorem docstrings. All three proofs are sorry.
