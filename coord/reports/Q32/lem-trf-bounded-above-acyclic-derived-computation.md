## Worker report

Group Q32, 2026-10-19. The earlier interruption left only dispatcher markers, with no
Lean file, node copy, report or evidence of a stage-2 delivery. The current item has
Q68's reviewed stage-1 split, but no lean record. That split is preserved verbatim.
The stale-assignment diagnosis in the earlier handoff confused stage 1 with stage 2.

The module `Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation` states
the entire item using two named theorems, both with `sorry`: the projective-resolution
clause and the remaining computation/comparison/naturality clauses. No new definition,
dependency repair, statement correction or axiom is introduced. The sole node change
is its lean field; both theorems are listed in lean.declarations. Each theorem's
source/blueprint docstring contains its complete corresponding natural-language proof.

Hypotheses and clauses, checked against the node:

- Arbitrary abelian categories are `A : Type uA`, `B : Type uB`, independent
  `Category.{vA}` / `Category.{vB}` and `Abelian` instances. The localization hom universes
  `wA` and `wB` are independent `HasDerivedCategory` parameters. No universe equality,
  smallness, ring-module specialization, generator, or extra completeness is imposed.
- Enough projectives is Mathlib's `EnoughProjectives A`. Its presentations are exactly
  epimorphisms from projective objects. `Projective` is the lifting property stated in
  the node, not an assumption of already having projective resolutions.
- The first theorem takes any integer bound `b` and `hX : X.IsStrictlyLE b` and returns
  `P`, `a : P ⟶ X`, `P.IsStrictlyLE b`, `∀ i, Projective (P.X i)`, and `QuasiIso a`.
  Mathlib's `isStrictlyLE_iff` identifies this bound with `IsZero (X.X i)` for `b < i`.
  Quantifying every bound states both the bounded-above existence clause and the
  retention of a prescribed upper bound; it adds no termwise-epic conclusion.
- `V : A ⥤ B`, `[V.Additive]`, and `[PreservesFiniteColimits V]` express additive and
  right exact. Between abelian categories this is equivalent to preservation of
  cokernels and finite sums: see Mathlib `Preadditive/LeftExact.lean`, especially
  `Functor.preservesFiniteColimits_of_preservesCokernels`. This is not full exactness.
- `LV : DerivedCategory A ⥤ DerivedCategory B` and
  `ε : DerivedCategory.Q ⋙ LV ⟶ V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q`
  retain the given canonical comparison, with exactly its domain and codomain.
  `hLV` uses `Functor.IsLeftDerivedFunctor` to specify its universal counit. Using
  the cochain localization rather than Qh is the equivalent localization explicitly
  allowed by def-weil-abstract-derived-category; `quotientCompQhIso` and
  `mapHomotopyCategoryFactors` identify the two presentations canonically.
- `hdefined` retains the everywhere-defined requirement of Situation 05S8/Definition
  05S9, as existence of an essentially constant denominator pro-diagram at every
  homotopy-category object, for `V.mapHomotopyCategory ⋙ Qh`. This is the body of the
  dependency's `Functor.IsTriangulatedLeftDerivedDefinedAt`: the saturated triangulated
  quasi-isomorphism system and exactness of the homotopy functor are fixed facts, so
  they are not extra variable hypotheses. The universally specified LV/counit is
  uniquely identified with these values. The statement does not replace essential
  constancy by existence of an arbitrary Kan extension alone.
- First conjunct: every `P` with some bound and projective terms has `IsIso (ε.app P)`.
- Left V-acyclicity is written literally as
  `IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj M))`. The target is the image
  of V applied to M[0], canonically V(M)[0]. This is an inlined property, not a second
  definition of a notion or acyclicity as vanishing without its comparison map.
- Second conjunct: every bounded-above `C` whose every term satisfies that precise
  predicate has `IsIso (ε.app C)`.
- Third conjunct: for every augmentation `a : C ⟶ X` with `[QuasiIso a]`, the specified
  map `inv (LV.map (Q.map a)) ≫ ε.app C` is an isomorphism. It is the canonical
  identification in the node, written in diagrammatic composition order; nothing is
  selected from an unconstrained existence theorem. `X` is unrestricted.
- Fourth conjunct: for independently bounded `C` and `C'`, acyclic terms in each,
  quasi-isomorphisms `a` and `a'`, and arbitrary `f : C ⟶ C'`, `h : X ⟶ X'` satisfying
  `f ≫ a' = a ≫ h`, the exact equality is
  `(inv (LV.map (Q.map a)) ≫ ε.app C) ≫ Q.map (Vcomplex.map f) =
   LV.map (Q.map h) ≫ (inv (LV.map (Q.map a')) ≫ ε.app C')`.
  This is precisely Q(V(f)) ε_C LV(Qa)^(-1) =
  ε_C' LV(Qa')^(-1) LV(Qh), in Lean's diagrammatic order. There is no invertibility
  assumption on f or h and no equality between the two bounds.

Dependency declarations read and used:

- def-sp-abelian: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic,
  full class and its docstring read; it is already imported by DerivedCategory.Basic.
- def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`, `quotientCompQhIso` in
  Mathlib.Algebra.Homology.DerivedCategory.Basic; full signatures/docstrings read.
- def-pur-saturated-triangulated-localization: the recorded
  Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem is publicly imported;
  its `Functor.IsTriangulatedLeftDerivedValue` / `IsTriangulatedLeftDerivedDefinedAt`
  bodies were read in full. hdefined uses their actual underlying recorded predicate
  `CategoryTheory.IsEssentiallyConstantProDiagram`, not a private copy. Its full
  definition in Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro was read.

All stated proof dependencies are imported privately: Mathlib.CategoryTheory.Abelian.Refinements
for lem-sp-abelian-refinements; Mathlib.Algebra.Homology.HomotopyCategory.KProjective for
CochainComplex.isKProjective_of_projective; Mathlib.Algebra.Homology.DerivedCategory.KProjective
for CochainComplex.IsKProjective.Qh_map_bijective; and the upstream
WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic for
CochainComplex.mappingCone.quasiIso_iff_acyclic. The essential-constancy module is
already publicly imported through the statement dependency. The genuine proof-only
node lem-trf-left-acyclic-short-exact has no Lean declaration and is not needed to
TYPE these statements, so no invented import or postponed helper is introduced.

Sources opened: literature/stacks-project/derived.tex at 0646(3), 06XN, the
05S8/05S9 situation/definition, 015D and 015E. The node's left-derived dual and the
specified comparison order were checked directly. No source correction was needed.

Searches made (actual msearch responses are preserved by the wrapper in searches.jsonl):

- msearch.py leanfinder: "Every bounded above complex of acyclic objects computes a
  total left derived functor via its counit and bounded above projective resolutions
  exist". Eight hits, including Functor.leftDerived, fromLeftDerivedZero,
  ProjectiveResolution.isoLeftDerivedObj, total-derived universal instance and
  mapDerivedCategoryFactors. The first group computes individual derived functors
  on objects; the latter supplies Kan-extension/exact-functor infrastructure. None
  states bounded-above termwise acyclic total-counit computation. Read Mathlib
  CategoryTheory/Abelian/LeftDerived.lean and Functor/Derived/LeftDerived.lean.
- msearch.py loogle: `"IsLeftDerivedFunctor"`. Twelve hits (universal-property class,
  its constructor/instance, uniqueness and functoriality). Read the class's complete
  source. None states this node.
- msearch.py grep: `acyclic|projective` in CategoryTheory/Functor/Derived. One comment
  in RightDerived.lean about projective/injective derivability, no matching theorem.
- rg of the upstream WeilConjectures category-theory files for bounded acyclicity,
  IsLeftDerivedFunctor and the exact node id. Upstream supplies the right-derived,
  bounded-below dual and a more specialized tensor functor. It has no declaration
  for the item and no occurrence of its node id.
- rg of lean/Sheaf for bounded acyclicity, projective resolutions, essential constancy
  and the exact two proposed declaration names. Existing DerivedColimitBar cites
  this item but does not state it. DerivedHomProjectiveResolution treats derived
  Hom, not an arbitrary right-exact functor. LeftDerivedFromResolvingClass constructs
  a functor from an adapted class, not this computation result. No proposed name
  was already declared. These files and the canonical Kan/pro bridge were inspected.

Edge cases checked before drafting: zero complex (any upper bound), complexes in a
single arbitrary integer degree, infinitely many negative nonzero terms, zero functor,
identity functor, and exact V. All fit the quantified bounds without truncating the
negative tail. For V = tensor with Z/2 on abelian groups, acyclicity is imposed on
terms via the actual total comparison; arbitrary torsion terms are not silently
accepted. Identity augmentations recover ε. A zero f and h or a general noninvertible
square is still covered. No boundedness on X or X' is imposed. Independent category
and localization universes are retained.

Validation: prescribed scompile.py server compilation passed in both sandbox and
library contexts (2.8 s and 2.3 s), no errors or warnings. Every variable/universe is
explicitly bound. Only the two named theorem proofs are sorry. No STATEMENT-DISPUTED
issue, node correction, new node or dependency module was needed.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
