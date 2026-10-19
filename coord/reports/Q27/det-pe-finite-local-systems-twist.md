## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProEtaleFiniteLocalSystemsTwist.lean` states
`AlgebraicGeometry.ProEtale.finiteLocalSystemsTwist` and defines the four predicates used
to render the local-system clauses: finite-presentation pro-etale systems,
finite-presentation etale systems, finite-model pro-etale systems, and an etale
trivializing cover.  All definition data is explicit; the theorem proof is the single
expected `sorry`.

The Lean rendering of the statement is as follows.

* `X` is `Scheme.{u}`, `Λ` is a commutative ring of `Type u`, and the pro-etale sheaf
  `F` is a sheaf of `ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)`.  The predicate
  `IsFinitePresentationProEtaleLocalSystem` combines the recorded fixed-coefficient
  local-constancy predicate with a pro-etale cover whose constant models satisfy
  `Module.FinitePresentation`.
* The first conclusion is an etale sheaf `G` satisfying
  `IsFinitePresentationEtaleLocalSystem` and an isomorphism
  `((comparisonUpperStar (ModuleCat ...) X).obj G) ≅ F`.
* Classicality is rendered by `IsClassical` on the underlying set sheaf obtained by
  `sheafCompose` and `forget`; `HasEtaleTrivializingCover X Λ F` spells out the
  asserted etale trivializing cover after applying `Scheme.toProEt`.
* The next clauses state preservation of finite-presentation local systems by
  `comparisonUpperStar` and by `comparisonLowerStar`, and bijectivity on all morphisms
  between the etale finite-presentation objects.
* The unit of `comparisonAdjunction` is required to be an isomorphism on each etale
  finite-presentation object, and its counit is required to be an isomorphism on each
  pro-etale finite-presentation object.  Together with the preceding preservation and
  bijectivity clauses these spell out the restricted quasi-inverse equivalence.
* The final implication is `Finite Λ → ...`: every pro-etale local system with finite
  constant models (`IsFiniteModelProEtaleLocalSystem`) has finite-presentation models.

The statement uses these recorded declarations: `AlgebraicGeometry.Scheme` and its
`ProEt.topology`/`smallEtaleTopology` site objects (Mathlib scheme and etale-site
declarations); `AlgebraicGeometry.ProEtale.comparisonUpperStar`,
`comparisonLowerStar`, and `comparisonAdjunction` from the comparison-morphism module;
`CategoryTheory.constantSheaf`; `ModuleCat`; and
`AlgebraicGeometry.ProEtale.IsClassical` from
`Sheaf.AlgebraicGeometry.ClassicalContinuityMap`.  The fixed-coefficient local-constancy
predicate is the current published dependency declaration, imported directly.  `Module.FinitePresentation`
is the Mathlib match for `def-sc-finitely-presented-module`.

Edge cases checked while choosing the binders and predicates were the empty scheme,
the zero ring, the zero module, an empty indexing type on an empty cover, nonempty
finite covers, and a finite ring with a finite zero model.  No extra nonemptiness,
Noetherian, or finiteness hypothesis is present in the main implication.

Searches made before writing:

* `msearch.py ... leanfinder "finitely presented module exact sequence finite free modules"`:
  found Mathlib `Module.FinitePresentation` and its finite-presentation lemmas; this is
  the exact recorded Mathlib match for `def-sc-finitely-presented-module`.
* `msearch.py ... loogle "Module.Finite, Module.Free, FinitePresentation"` returned no
  additional match; the direct Mathlib declaration was retained.
* `msearch.py ... grep "FinitelyPresented|FinitePresentation|IsFinitelyPresented" Algebra`
  found `Mathlib/Algebra/Module/FinitePresentation.lean` and related presentation files.
* `rg` over `WeilConjectures` and `lean/Sheaf` for local-constant and finite-local-system
  names found only the general etale `IsLocallyConstantSheaf`, the pro-etale fixed-module
  interface, and finite-ring special cases; no declaration states this arbitrary-ring
  comparison theorem.
* The node's recorded Mathlib/source declarations were opened in full, including the
  comparison, constant-sheaf, module-sheaf, fixed local-constancy, and classicality
  modules.  The source of Stacks Tag 099Y and the blueprint twist proof were read.

## Current-source self-check

On 2026-10-17 the saved item was checked against the current node, all nine
statement dependencies, Stacks Tag 099Y and the current blueprint twist detail.
The source and all clauses remain unchanged. The current published module
`Sheaf.Paper.ProEtaleFixedModuleLocalConstancy` already has exactly the saved
fixed-coefficient predicate, so the redundant dependency packet is archived in
this sandbox and is not delivered. Its node is already recorded in
`sec-nagata-compactification`; the saved copy in this item's chapter would have
created a duplicate node. The item directly reuses the published declaration.

The first dry run compiled both saved files without errors or unexpected warnings.
Preflight exposed a signature-record mismatch: the saved `lean.statement` included
`:=`, while the signature reader excludes it. The record now matches that reader.
No Lean statement or definition changed. The independent second-reading section is
reserved for the separate reader, as required by `deliver2.py`.

The repeated LeanFinder query "A locally constant sheaf of finitely presented
modules on the pro etale site descends to the etale site" found condensed-module
constructions and general sheaf finite-presentation predicates, not this descent
statement. Loogle `Module.FinitePresentation` confirmed the exact module predicate.
The Mathlib grep `FinitePresentation.*LocalSystem|finiteLocalSystemsTwist|compare.*locally.*constant`
in AlgebraicGeometry returned zero hits; project/source searches found no copy of
the theorem. The coefficient lift is canonical, all variables and universes are
explicit, and the zero ring, zero model and empty scheme remain included.

No new definition DAG node is needed: the finite-presentation and finite-model
predicates are helpers of the owning item, listed in `lean.declarations`.

## Second reading by Q27

I read the node statement, its source at Stacks Tag 099Y, the blueprint twist
statement and proof, the Lean module, and every recorded statement dependency.
The item remains a statement node; its `lean.statement` is verbatim the theorem
signature in `ProEtaleFiniteLocalSystemsTwist.lean`.

The node's introduced objects and hypotheses match the Lean as follows.

* `X` is `Scheme.{u}` in the theorem and in each of the four predicates.  This
  is the recorded `[def-pc-scheme]` object, with no separated, quasi-compact,
  Noetherian, nonempty, or characteristic hypothesis.
* `Λ` is the discrete commutative ring `(Λ : Type u) [CommRing Λ]`.  The
  coefficient category is rendered canonically as
  `ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)` on both sites.  The `ULift` only puts
  the ring in the module-value universe; it does not change the ring or add a
  finiteness assumption.
* `ν_X`, the small pro-etale and etale sites, constant sheaves, and sheaves of
  modules are rendered by `Scheme.ProEt.topology X`, `X.smallEtaleTopology`,
  `comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction`,
  `constantSheaf`, and the `ModuleCat` sheaf categories.  These are the
  declarations recorded for `[def-weil-pbc-site-comparison-morphism]`,
  `[def-weil-pbc-proetale-site]`, `[def-weil-pbc-etale-site]`,
  `[def-weil-pbc-constant-sheaf]`, and
  `[def-weil-sheaf-of-modules-category]`; no private site or comparison map is
  introduced.
* The hypothesis `F` is exactly a sheaf on `X.ProEt` with the displayed module
  coefficients.  `IsFinitePresentationProEtaleLocalSystem` is the conjunction
  of fixed-coefficient local constancy and a pro-etale covering whose model
  modules satisfy `Module.FinitePresentation`.  The fixed-coefficient
  declaration is the published repair of
  `[def-weil-proetale-locally-constant-sheaf]`; it allows arbitrary varying
  models and imposes no finiteness beyond the second conjunct.
* `IsFinitePresentationEtaleLocalSystem` is exactly an etale covering with
  constant models satisfying `Module.FinitePresentation`.  The first
  conclusion is rendered by `∃ G`, that predicate, and a nonempty isomorphism
  `comparisonUpperStar.obj G ≅ F`, matching `ν_X^*F_0 ≅ F`.
* The next conjunct is `IsClassical` on the underlying set sheaf obtained by
  `sheafCompose` and `forget`, exactly the node's classicality clause.  The
  following conjunct is `HasEtaleTrivializingCover`, namely an etale cover and
  constant module isomorphisms after `Scheme.toProEt`.
* The two preservation conjuncts state that `comparisonUpperStar` sends etale
  finite-presentation local systems to pro-etale ones and
  `comparisonLowerStar` sends pro-etale ones to etale ones.  The next conjunct
  gives bijectivity on every morphism between etale finite-presentation
  objects.  The final two comparison conjuncts state that the adjunction unit
  is an isomorphism on each etale object and the counit is an isomorphism on
  each pro-etale object.  Together these are the explicit restricted
  quasi-inverse equivalence asserted by the node, with the quantifiers in the
  same order.
* The final implication is `Finite Λ → ∀ F'`, with
  `IsFiniteModelProEtaleLocalSystem` requiring finite underlying sets for the
  constant models and conclusion `IsFinitePresentationProEtaleLocalSystem`.
  This is exactly the finite-ring clause and adds no hypothesis to the main
  implication.

The edge cases remain included.  The empty scheme is allowed and its empty
  cover makes the existential cover predicates vacuous.  The zero ring and
  zero module are valid commutative-ring/module objects; the finite-model
  argument includes both.  Empty indexing types are admitted by the cover
  encodings, while any actual cover may be nonempty.  No clause requires a
  nonzero model, a positive rank, a nonempty scheme, or a characteristic
  restriction.  The universe binders are explicit; the coefficient lift and
  site/value universes are the same canonical convention used by the recorded
  comparison declarations.

I repeated the three required searches.  `msearch.py` LeanFinder queries for
  descent of finitely presented pro-etale local systems returned only condensed
  or general finite-presentation predicates; Loogle queries for
  `Module.FinitePresentation` and constant-sheaf equivalences returned no
  theorem for this comparison; and `rg` over Mathlib, the slopmaster2 source,
  and `lean/Sheaf` found no `finiteLocalSystemsTwist` or equivalent arbitrary
  ring statement.  The only project match is this module.  The direct Mathlib
  declaration `Module.FinitePresentation` is the recorded dependency, so no
  duplicate definition node is needed.  I also checked the current
  fixed-coefficient local-constancy declaration and its dependency note; it is
  the usable interface for the module-valued comparison and states the same
  coverwise local-constant notion without extra finiteness assumptions.

The only defect found was documentary: the theorem docstring compressed the
node's eight proof steps into a short paragraph and did not name the proof
dependencies.  I expanded that docstring to enumerate the decomposition,
torsor, comparison, overlap-cocycle, gluing, pullback, restricted-equivalence,
and finite-ring steps, with their node citations.  No Lean definition,
hypothesis, conclusion, universe, dependency list, or theorem signature was
changed.  `scompile.py` compiles the module cleanly with no warnings other than
the expected `sorry` declaration.
