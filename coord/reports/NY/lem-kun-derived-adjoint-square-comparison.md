## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison` states
`CategoryTheory.Adjunction.derived_adjoint_square_comparison`, with one `sorry` proof.
It introduces no definitions. The node statement is unchanged. The conclusion contains
all three displayed forms of the compatibility: arbitrary adjuncts, units, and counits.

Hypothesis and clause correspondence:

- The four abelian categories are `A`, `B`, `A0`, `B0`, each with `Category`, `Abelian`,
  and `HasDerivedCategory`. Object, morphism, and chosen derived morphism universes are
  independently bound for each category. All complexes are unbounded cochain complexes
  indexed by `ℤ`.
- The additive adjunctions are `L`, `R`, `L0`, `R0`, the four `Additive` instances, and
  `adj : L ⊣ R`, `adj0 : L0 ⊣ R0`. Exactness of the left functors is precisely
  `PreservesFiniteLimits` and `PreservesFiniteColimits`.
- The vertical functors are `V` and `W`, each additive and preserving finite limits and
  finite colimits. No injective preservation hypothesis occurs.
- `a : L ⋙ V ≅ W ⋙ L0` and `c : R ⋙ W ≅ V ⋙ R0` are the stated natural isomorphisms,
  with Lean composition written in diagrammatic order. `hc` says for every underived
  `M`, `N`, `t` that the second adjunct of `a.inv.app M ≫ V.map t` equals
  `W.map (adj.homEquiv M N t) ≫ c.hom.app N`.
- `RR` and `RR0` are total right derived functors with comparison units `γ` and `γ0`.
  Their `IsRightDerivedFunctor` instances assert the total right-derived universal
  properties at quasi-isomorphisms. `hR` and `hR0` explicitly assert everywhere-defined
  right derivability in the essential-constancy sense of the recorded adjunction node:
  the diagrams of all quasi-isomorphisms from each homotopy object are essentially
  constant ind-diagrams. This does not replace that condition by a bare Kan extension.
- `D(L)`, `D(L0)`, `D(V)`, `D(W)` are the corresponding `mapDerivedCategory` functors;
  their canonical localization identifications are `mapDerivedCategoryFactors`.
- `d : L.mapDerivedCategory ⊣ RR` and `d0 : L0.mapDerivedCategory ⊣ RR0` are the two
  canonical derived adjunctions. `hcan` and `hcan0` specify canonicality by the recorded
  dependency's Hom compatibility formula, on cochain complexes: the adjunct of the
  localization of `f`, transported along the exact left functor identification, is
  the localization of its termwise adjunct followed by `γ` or `γ0`. This is a
  characterization of the stipulated canonical adjunctions, not an assumption of
  the square's unit compatibility. The homotopy-category formula in the dependency
  descends from precisely this cochain formula; quotienting by homotopy and the
  `quotientCompQhIso` identify the two formulations.
- The postcomposition `IsRightDerivedFunctor` instance is the hypothesis that
  `RR ⋙ W.mapDerivedCategory` remains right derived with its localized comparison
  unit. The unit is the composite of the inverse exact `W` identification,
  `Functor.whiskerRight γ W.mapDerivedCategory`, and the functor associator. Its
  source is termwise `R` followed by termwise `W` followed by localization, i.e.
  termwise `WR` followed by localization.
- `b` is the stated natural comparison and `hb` is its characterization on every
  complex `P`. The left side first uses `W.mapDerivedCategoryFactors.inv` to identify
  the localized `WR` complex with `D(W)` of the localized `R` complex, then applies
  `D(W)(γ_P)` and `b`. The right side applies localized termwise `c`, then `γ0`
  at `C(V)P`, then `RR0` of `V.mapDerivedCategoryFactors.inv`. Thus both sides have
  exactly the common source and target of the node's comparison equation, with its
  unnamed localization identifications made explicit. No `IsIso b` is required.
- `aD : L.mapDerivedCategory ⋙ V.mapDerivedCategory ≅
  W.mapDerivedCategory ⋙ L0.mapDerivedCategory` is `a^D`. `haD` characterizes it as
  the localization of termwise `a`. The left side follows `aD` by the exact `W` and
  `L0` identifications; the right side follows the exact `L` and `V` identifications
  by `Q` of termwise `a.hom`. This uniquely specifies the induced comparison, with
  no additional geometric data or unrelated arbitrary isomorphism.
- The first conclusion conjunct is the adjunct formula for every derived `M`, `N`,
  and `t`. `d.homEquiv` and `d0.homEquiv` render the two adjunct operations.
- The second conclusion conjunct says
  `W.mapDerivedCategory.map (d.unit.app M) ≫ b.app (L.mapDerivedCategory.obj M) =
  d0.unit.app (W.mapDerivedCategory.obj M) ≫ RR0.map (aD.inv.app M)` for every `M`.
- The third conjunct says
  `V.mapDerivedCategory.map (d.counit.app N) = aD.hom.app (RR.obj N) ≫
  L0.mapDerivedCategory.map (b.app N) ≫ d0.counit.app (V.mapDerivedCategory.obj N)`
  for every `N`. These are the node's unit and counit equations in diagrammatic
  composition order. As the source proof explains, the adjunct statement specializes
  to the unit equation, the unit equation gives all adjuncts, and specializing to
  the counit gives the counit equation (with the reverse implication by transposition).

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (class signature and explanation inspected).
- `def-weil-abstract-derived-category`: `DerivedCategory`, `DerivedCategory.Q`,
  `DerivedCategory.Qh`, and `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `lem-pc-derived-adjoint-functors`:
  `CategoryTheory.Adjunction.exists_derived_adjunction_of_essentially_constant`,
  `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`. Its full signature/docstring
  supplies the precise everywhere-defined assumptions and canonical Hom formula.
  Its imported `IsEssentiallyConstantIndDiagram` is used without copying it.
- `lem-weil-pbc-exact-functor-derived-factorization`: the recorded Mathlib match
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, together with
  `mapDerivedCategory`, from `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- The already stated proof dependencies are imported without `public`:
  `CategoryTheory.Functor.exactFunctor_derivedFunctor` in
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`;
  `CategoryTheory.preDerivedAdjunctionGeneral` in
  `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`;
  `CategoryTheory.Localization.natTrans_ext` (the recorded Mathlib universal-property
  clause) in `Mathlib.CategoryTheory.Localization.Predicate`.
- The canonical termwise adjunction is the existing
  `CategoryTheory.Adjunction.mapHomologicalComplex` in
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`, publicly imported
  by the adjunction dependency. Its full construction and homotopy descent were read.
  Termwise natural transformations use `CategoryTheory.NatTrans.mapHomologicalComplex`.

Source checked: `literature/stacks-project/derived.tex`,
`lemma-derived-adjoint-functors` (09T5), `lemma-pre-derived-adjoint-functors-general`
(0FND), and their canonical Hom calculation. The compatible square is the node's
explicit agent generalization; its five-step proof is included in the theorem docstring.

Edge cases checked: zero categories, zero complexes and zero functors impose no extra
condition or nonemptiness binder. Identity vertical functors reduce to the ordinary
adjunction identities. Noninvertible `b` remains allowed; the calculation uses
naturality and never cancels `γ` or `b`. There are no boundedness, enough-injectives,
K-injective-preservation, geometric-square, or fixed-universe-size restrictions.
All comparison composites were typechecked including their localization transports.
No statement fault or disputed assertion was found.

Searches (2026-10-15):

- `msearch.py ... leanfinder` with query “An adjoint square of exact functors induces
  a compatible square of derived adjunctions”: eight hits, including `Adjunction.derived'`,
  `Adjunction.derived`, and Guitart-exact derivability results. The derived-adjunction
  file was read in full: it handles a single adjunction under absolute derivability,
  not the comparison of this square under the given hypotheses.
- `msearch.py ... loogle '"derived", "Adjunction"'`: twelve hits, all single derived
  adjunction constructions, units, counits, and their factorization formulas;
  no match for this theorem.
- `msearch.py ... grep 'derived.*(mate|square)|comparison.*(unit|counit)' CategoryTheory`:
  eighteen hits, on lifting, monadicity, and derivability; no matching theorem.
- `msearch.py ... leansearch` with query “The canonical right derived comparison
  preserves units and counits of a compatible square of adjunctions”: service
  unavailable (Internal Server Error); no conclusion drawn from unavailable search.
- `rg` of `WeilConjectures` and `lean/Sheaf` with
  `derived.*(mate|square)|comparison.*(unit|counit)` found specific geometric mate and
  unit comparisons, but no generic four-abelian-category theorem with these hypotheses.
  The narrower name queries `derived_adjoint_square_comparison|AdjointSquareComparison`
  in Mathlib, upstream source, `lean/Sheaf`, and `dag/lean_names_upstream.json` had no hits.
  Searching the upstream source for this item's exact id also had no hits.

Validation: compiled the delivered module with `scompile.py`, server only, nice 19,
two threads, 60-second per-file limit. No local compiler or build was run.

## Second reading by NY

I independently opened the item node, the delivered Lean file, all four statement
 dependency records, their declaration sources, and Stacks derived.tex at
lemma-pre-derived-adjoint-functors-general (0FND),
lemma-pre-derived-adjoint-functors (0DVC), and lemma-derived-adjoint-functors (09T5).
The source assumes abelian categories and everywhere-defined unbounded derived
functors, without enough injectives or boundedness. The compatible-square assertion
is explicitly an agent generalization in the node, not a quotation of 09T5.

My object/hypothesis/conclusion checklist, with verdicts:

1. Four abelian categories with unbounded derived categories: `A`, `B`, `A0`, `B0`,
   their `Category`, `Abelian`, and `HasDerivedCategory` instances. Matches.
   I checked `Abelian` in Mathlib/CategoryTheory/Abelian/Basic.lean and
   `DerivedCategory`, `Q`, `Qh`, `HasDerivedCategory` in
   Mathlib/Algebra/Homology/DerivedCategory/Basic.lean. These are exactly the
   recorded dependency notions, not alternative derived categories.
2. Additive adjunctions B to A and B0 to A0: `L`, `R`, `L0`, `R0`, their four
   `Additive` instances, `adj : L ⊣ R`, `adj0 : L0 ⊣ R0`. Matches.
3. Exact left functors: finite-limit and finite-colimit preservation for `L`,
   `L0`. Exact additive vertical functors: the same two instances for `V : A ⥤ A0`
   and `W : B ⥤ B0`, plus additivity. Matches; no exactness is imposed on `R`, `R0`.
4. Underived square isomorphisms: `a : L ⋙ V ≅ W ⋙ L0` and
   `c : R ⋙ W ≅ V ⋙ R0`. `hc` quantifies M, N, t in that order and equates
   `adj0.homEquiv ... (a.inv.app M ≫ V.map t)` with the W-image of the first
   adjunct followed by `c.hom.app N`. Matches both orientation and adjuncts.
5. Everywhere total right derived functors: `RR`, `RR0`, comparison transformations
   `γ`, `γ0`, and their quasi-isomorphism `IsRightDerivedFunctor` instances.
   `hR`, `hR0` additionally give the essential constancy at every homotopy object
   required by the recorded `exists_derived_adjunction_of_essentially_constant`.
   I read that dependency's full signature and its imported
   `IsEssentiallyConstantIndDiagram`: outgoing quasi-isomorphisms with all
   commuting triangles (`⊤`). Matches; a Kan property alone is not substituted
   for everywhere defined in the Stacks sense.
6. Canonical derived adjunctions: `d`, `d0`, `hcan`, `hcan0`. The Hom formula is
   the dependency's formula transported from homotopy categories to complexes.
   I checked the actual upstream `Adjunction.mapHomologicalComplex` and
   `mapHomotopyCategory` constructions: their units/counits are termwise and
   descend through the homotopy quotient. The exact left comparison is
   `mapDerivedCategoryFactors.hom`, so the formulas express canonicality for
   arbitrary maps of complexes. They do not assume the square's unit identity.
   Matches.
7. Exact derived functors D(L), D(L0), D(V), D(W): the existing Mathlib
   `mapDerivedCategory` and `mapDerivedCategoryFactors`. Their source identifies
   Q followed by D(F) with termwise F followed by Q, in this direction. Matches.
8. Right derivability after D(W): the third `IsRightDerivedFunctor` instance is
   on `RR ⋙ W.mapDerivedCategory`; its comparison first uses the inverse W
   localization isomorphism, then whiskers `γ`, then reassociates. It derives
   termwise WR, precisely the hypothesis of the node. Matches.
9. Canonical b: `b : RR ⋙ W.mapDerivedCategory ⟶ V.mapDerivedCategory ⋙ RR0`.
   `hb` quantifies every complex P. Its left side starts at Q(C(W)C(R)P), uses
   the inverse W factorization, D(W)(γ), then b. Its right side uses Q(C(c)),
   γ0 at C(V)P, and RR0 of the inverse V factorization. Both end at
   RR0(D(V)(QP)); this is exactly the node's equation with its explicit
   localization identifications. Matches; b need not be invertible.
10. Induced aD: `aD` has D(L) then D(V) as source and D(W) then D(L0) as target.
    `haD` compares its component at QX with Q of termwise a, using the two
    successive exact-functor factorizations on either side. Matches and
    characterizes the induced isomorphism, rather than arbitrary square data.
11. Arbitrary derived adjunct clause: first conjunct, for every M in D(B), N in
    D(A), and t from D(L)M to N, compares the second adjunct of
    `aD.inv.app M ≫ V.mapDerivedCategory.map t` with D(W) of the first adjunct
    followed by `b.app N`. Matches every quantifier and conclusion.
12. Unit clause: second conjunct, D(W)(η_M) then b at D(L)M equals η0 at D(W)M
    then RR0 of aD inverse. Matches the first displayed consequence.
13. Counit clause: third conjunct, D(V)(ε_N) equals aD at RRN, then D(L0)(b_N),
    then ε0 at D(V)N. Matches the second displayed consequence. Stating all
    three consequences as conjuncts is logically equivalent to the node's
    simultaneous assertions.

The node's five proof steps are all present in the declaration docstring:
identity-fraction calculation of the units; degreewise underived unit identity
and the b comparison; localization uniqueness; arbitrary adjuncts by naturality;
counits by transposition. The already-stated proof dependencies are imported
without `public`. No definitions, dependency modules, or new nodes are delivered;
H12/H13 introduce no additional review items here. There is one public named
sorry theorem and nothing proved. Both source docstrings carry the exact blueprint
id. There is no file-local notation, private definition, local instance, hidden
`let`, or unbound variable/universe. Maximum Lean line width is 95. I compared
the node's `lean.statement` directly with the complete signature: verbatim equal.
Only the `lean` field differs from the repository node; no correction or citer
verdict is needed.

Edge cases: the zero categories, zero complexes, and zero functors remain allowed.
An empty abelian category is already excluded by the source's abelian-category
axioms, not by an extra Lean hypothesis. There is no external index family, n,
characteristic, coefficient ring/field, or scheme parameter. Cochain indices are
all integers, without a boundedness restriction. All four object universes, all
four original morphism universes, and all four derived morphism universes are
independently quantified. Identity vertical functors and noninvertible b are
allowed. No preservation of K-injectives or geometric-square assumption occurs.

Independent duplicate searches, 2026-10-15:

- LeanFinder via msearch, query "Beck Chevalley compatibility of localized
  adjunctions with right Kan extension comparison": eight hits, on localization
  of a single adjunction (including `Adjunction.localization` and its unit and
  counit formulas). They require the right adjoint itself to descend; they do not
  give this theorem for nonexact right adjoints and their total derived functors.
- Loogle via msearch, query `"derived", "compatibility"`: zero hits.
- `rg` with `conjugate.*derived|derived.*conjugate|beck.*chevalley|mate.*derived`
  in upstream CategoryTheory, project CategoryTheory, and Mathlib derived-functor
  sources found three closer source candidates, which I opened:
  `mapDerivedCategoryAdjunction_mate` in MapDerivedCategoryMate.lean imposes
  exact right adjoints (as well as extra resolution/tensor structures);
  `derivedPlus_mateEquiv_app_fac` in RightDerivedFunctor/PlusAdjunction.lean is
  bounded below with enough injectives;
  `rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv` in
  RightDerivedFunctor/CompConjugate.lean is a composition comparison with
  K-injective resolution and preservation assumptions. None states the node.
- Exact declaration/module name searches in Mathlib, upstream, project Lean,
  and dag/lean_names_upstream.json returned no pre-existing match.

Verdict: no mathematical or signature mismatch found; I preserved the module
and node and added this independent review only. The initial compile invocation
used a relative path from the repository and failed before invoking Lean; I
reran it from the sandbox. The required server scompile then succeeded cleanly:
AdjointSquareComparison.lean 1.6 seconds, nice 19, two threads, 60-second limit.
Its side-only ExactFunctorDerivedFunctor import also compiled in the private
overlay (1.2 seconds). No local compiler or global build was invoked.
