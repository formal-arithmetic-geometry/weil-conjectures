## Worker report

The module `Sheaf.Paper.NativeWeilLocalizingBrownAdjoints` states
`lem-sf-native-weil-localizing-brown-adjoints` in two named theorems, both with
whole proof `sorry`. `AlgebraicGeometry.nativeWeil_localizing_hulls` states the
hull assertions, and `AlgebraicGeometry.nativeWeil_localizing_brown_adjoints`
states the two restricted operations and every ordinary Brown assertion.
There are no independent new notions, dependency repairs, statement corrections,
or disputed assertions. Every helper is a literal specialization of a published
construction or an abbreviation of this node's conjunction of conclusions.
No definition contains postponed data or selects data from an existence axiom.

Hypothesis and object correspondence:

- Finite field: `(k₀ : Type u) [Field k₀] [Finite k₀]` in both theorems.
- The algebraic closure is the framework's canonical `AlgebraicClosure k₀`, as
  used by `Scheme.Hom.geometricFiber` and `WeilSheaf.frobeniusPullback`.
  This follows the recorded dependency's actual native encoding; the source's
  symbol k is an algebraic closure, with no further chosen structure used here.
  It does not replace geometric base change by a rational fiber.
- The prime and invertibility condition are `(l : ℕ) [Fact l.Prime]` and
  `[Fact (ringChar k₀ ≠ l)]`. The coefficients are the existing `PadicAlgCl l`
  and the universe lift already built into the native coefficient sheaves.
- `X,Y : Scheme.{u}` with their `Over (Spec (CommRingCat.of k₀))` instances
  are X₀,Y₀. Their locally finite type and quasi-compact structure maps are
  explicit instance binders; Y's quasi-separated structure map is explicit.
- `(f : X ⟶ Y) [f.IsOver ...]` is f₀. `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, `[QuasiCompact f]` give all its relative hypotheses.
  There is no absolute separatedness binder on X or Y.
- `nativeWeilChosenCompactification k₀ f` is exactly
  `HasCompactification.compactification f` with
  `hasCompactification_of_over (k₀ := k₀) f`, the same witness as
  `WeilComplex.derivedLowerShriek`. It is not an arbitrary replacement
  compactification. Its `Z`, `i`, `g` are Z₀,j₀,p₀. Properness of g and the
  hypotheses on Y give the required finite type and quasi-compactness of Z.
- `nativeWeilUnderlyingHull` uses the geometric fiber and the published
  `ProEtale.DerivedCategory.boundedAdicConstructible` predicate. Thus C_T
  uses the actual internal `ProEtale.AdicSheaf` heart and bounded native
  constructible cohomology. `IsAdicLisseSheaf` has the quantifiers
  `∀ V f, R f → ∃ n : ℕ, ...`; ranks are allowed to vary with covering member.
  `IsAdicStratifiedLisseSheaf` uses finite constructible immersion strata,
  and `IsAdicConstructibleSheaf` makes this local on the underlying scheme.
- The fixed-pair heart is the existing `ProEtaleWeilSheaf k₀ l T`, definitionally
  `IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l T)`. Neither fixed pairs in a
  derived category nor a different coefficient category are substituted.
- U_T is `(IsoAlgebra.forget ...).mapDerivedCategory`; I_T is
  `(IsoAlgebra.Free.functor ...).mapDerivedCategory`. These are the declarations
  in `lem-sf-free-derived-weil-resolution`; its specified adjunction and counit
  are retained, not supplied as additional assumptions. The unit η_T belongs to
  that same adjunction; no conclusion here imposes a new normalization on it.
- Universe u+1 is the native hearts' Hom universe. The existing
  Grothendieck `HasDerivedCategory` instance gives the same derived Hom universe.
  All representative indices, coproduct indices, solution families and Hom-value
  groups use exactly u+1. The generic conjunction helper uses one explicit v for
  both Hom universes and indices and specializes here to u+1. No site universe
  equality or extra size hypothesis is imposed.

Clause correspondence:

1. `nativeWeilLocalizingHull` is `localizingClosure (ofObj (I_T on C_T))`.
   Its full subcategory is replete, triangulated and closed under all coproducts
   of the fixed universe, using the published localizing-closure definition.
   The first conjunct of `nativeWeil_localizing_hulls` quantifies over
   `I : Type (u+1)` and `S : I → C_T.FullSubcategory`, with
   `∀ A, ∃ i, Nonempty (S i ≅ A)`, and identifies `Loc(I_T S)` with this
   choice-free expression. Duplicates in a representative family do not affect
   the closure. Essential smallness supplies such a family through the recorded
   realization dependency; it is not an extra mathematical hypothesis.
2. The next conjunct is literal equality of object properties:
   `nativeWeilLocalizingHull ... = (nativeWeilUnderlyingHull ...).inverseImage U_T`.
   Together with clause 1 this is exactly the displayed equality for the chosen
   S_T, including every unbounded K in the ambient ordinary derived category.
3. The next two universal conjuncts state I_T(L_T) ⊆ L_W,T and
   U_T(L_W,T) ⊆ L_T, separately and explicitly.
4. `WeilComplex.objectProperty ... ≤ nativeWeilLocalizingHull ...` is the native
   bounded constructible Weil membership clause, using the dependency's predicate.
5. The final two conjuncts assert `IsIdempotentComplete` for the full ordinary
   and Weil hulls. Applying this theorem to T=X,Y,Z gives the three hull
   equalities/inclusions and in particular the two source-hull splittings.
6. In the main theorem, the existential witnesses `h,hW` are preservation of
   membership under the actual ambient composites. `liftFullSubcategory` then
   restricts exactly those composites; it does not quantify over arbitrary
   functors agreeing only on selected objects.
7. F is `nativeWeilUnderlyingCompactSupport` for the chosen compactification:
   native `adicOpenImmersionLowerShriek` along the geometric fiber map of i,
   applied termwise via `mapDerivedCategory`, followed by `rightDerivedFunctor`
   of native `adicLowerStar` along the geometric fiber map of g. Its definition
   installs only the published `Compactification.over` instance. All data and
   coefficient maps are the existing native constructions.
8. F_W is the existing `ProEtaleWeilSheaf.rightDerivedLowerShriek` for exactly
   the same chosen compactification, hence has the specified Frobenius lifts.
   Both `IsTriangulated` conjuncts and both `∀ I : Type (u+1),
   PreservesColimitsOfShape (Discrete I)` conjuncts are explicit.
9. `nativeWeilBrownAssertions` is only a conjunction abbreviation, expanded for
   each of these two restrictions. It says `∃ G, Nonempty (F ⊣ G) ∧ ...`.
   Thus these are ordinary right adjoints with precisely the full hulls as domain
   and codomain, natural in both variables by `Adjunction`.
10. Its H_M is literally `F.op ⋙ preadditiveYoneda.obj M`, valued in
    `AddCommGrpCat.{v}`. This is Hom(F(-),M), and its action is precomposition
    with F.map. `.IsHomological` is the cohomological assertion on the opposite
    triangulated source. `PreservesLimitsOfShape (Discrete I)` for every small
    I says coproducts in the source go to products.
11. Its solution family is `(I : Type v) (B : I → C)
    (b : ∀ i, F.obj (B i) ⟶ M)`, with
    `∀ Z z, ∃ i f, F.map f ≫ b i = z`. This has exactly the required weak
    universality direction Z→B_i, with no uniqueness or compactness premise.
12. The final natural isomorphism
    `yoneda.obj (G.obj M) ≅ H_M ⋙ forget AddCommGrpCat` makes the same G(M)
    represent that functor; no unrelated representing object is substituted.
    The adjunction already supplies naturality also in M.

Dependency declarations read and reused:

- `def-sf-native-weil-derived-framework`: public import
  `WeilConjectures.WeilSheaf.LowerShriek`; the definitions in this module,
  `WeilSheaf.Category`, `WeilSheaf.OpenImmersion` and `WeilSheaf.LowerStar` give
  the native hearts, Frobenius, `WeilComplex.objectProperty`, chosen Nagata
  witness, exact open extension and derived proper image. Signatures and
  docstrings were read in their source files. The constructibility definitions
  were read in `WeilConjectures.SixFunctors.ProEtale.Adic.Constructible`.
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  implemented by the explicit universes above.
- `def-weil-triangulated-subcategory`: public import
  `Mathlib.CategoryTheory.Triangulated.Subcategory`, declaration
  `CategoryTheory.ObjectProperty.IsTriangulated`. `localizingClosure` and
  `IsLocalizing` are reused from
  `WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure`.
- `lem-sf-free-derived-weil-resolution`: public import
  `Sheaf.CategoryTheory.FreeDerivedWeilResolution`; its existing
  `IsoAlgebra.Free.functor`, `forget`, `freeWeilDerivedAdjunction`,
  `exists_freeDerivedWeilResolution` and `freeWeil_mem_localizingClosure`
  are the source/induction interfaces and the stated proof route.
- `lem-sf-locally-finite-adic-constructible-realization`: public import
  `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`;
  `WeilConjectures.LocallyFiniteAdicRealization.locally_finite_adic_constructible_realization`
  supplies `RealizationCore.targetSmall` for the actual bounded constructible
  full subcategory. Its full signature and record fields were read.
- `lem-sf-locally-finite-adic-compact-support-sums` remains a proof dependency
  only, with a plain import of `Sheaf.Paper.NativeAdicCompactSupportSums`.
  `nativeWeilUnderlyingHull` directly specializes the published predicate as
  `(ProEtale.DerivedCategory.boundedAdicConstructible l
  (T ↘ Spec (CommRingCat.of k₀)).geometricFiber).localizingClosure`.
  Its theorem `nativeAdicCompactSupport_localizing_preservesCoproducts`
  supplies the geometric coproduct/preservation proof input; its abbreviation
  is not used in this statement module.
- Other stated proof inputs are plain imports: the Grothendieck derived
  coproduct theorem, K-injective resolution and locally-small-derived modules,
  `isIdempotentComplete_of_countableCoproducts`, the triangle Hom exactness API,
  `setGeneratedDerived_cohomological_solutionSet`,
  `cohomological_isRepresentable_of_solutionSet`, and
  `Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top`.
- `lem-sf-native-weil-derived-induction-comparison` has no Lean record or
  Mathlib match in the current DAG. It is a proof dependency, not a missing
  object needed to type this statement, so no import for it can yet be added.
  Its role is explained in the proof docstrings. No import cycle is introduced.

Edge cases checked before writing:

- Empty source scheme, zero complexes, and zero sheaves remain admissible.
  Finite free rank zero and an empty stratification of an empty scheme remain
  covered by the native constructibility predicate.
- Empty coproducts are included: indices quantify over all Type (u+1), with
  no `Nonempty` assumption. Solution families have no artificial nonemptiness
  binder either; universality has its literal quantified meaning.
- Negative Frobenius iterates are retained in the existing free induction.
  The proof docstring spells out the inverse-automorphism argument rather than
  inferring inverse stability from forward stability alone.
- The identity morphism and a nontrivial unipotent/Jordan-block Weil structure
  are not excluded: there is no semisimplicity, finite-order action, compactness,
  uniform-rank or fixed-pair-in-derived-category assumption.
- Nonseparated finite-type schemes are included. Only relative f is separated;
  properness of the compactification leg does not impose absolute separatedness.
- K and M range over full unbounded hulls; neither adjoint is claimed on the
  entire ambient pro-etale derived category.
- Representative families need not have an injective enumeration, so duplicate
  representatives and equivalent choices yield the same replete hull.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Localizing hull of free derived Weil sheaves Brown
  right adjoint compact support"`: eight hits, chiefly condensed free/forget
  adjunctions and sheaf-module free constructions; no native hull/Brown theorem.
- `msearch.py ... leansearch "triangulated functor preserving coproducts has right
  adjoint Brown representability"`: eight hits including `Functor.IsTriangulated`
  and the partial-adjoint criterion. These are generic ingredients, not this
  native statement or its hull equality.
- `msearch.py ... loogle "CategoryTheory.Functor.IsLeftAdjoint,
  CategoryTheory.ObjectProperty.localizingClosure"`: zero hits (the project-local
  closure is unknown to the Mathlib service). Follow-up query
  `"CategoryTheory.Functor.IsLeftAdjoint"`: twelve hits, the generic adjunction API.
- `msearch.py ... grep "localizingClosure|brown|Brown" CategoryTheory`: three
  Mathlib hits, all author names, no native theorem.
- `rg` of the exact node id in `lean/WeilConjectures`: no match. Scoped searches
  for localizingClosure/Brown/localizing-hull names in `WeilSheaf` and native
  `Sheaf/Paper` modules found the ordinary compact-support hull/sums declaration
  already reused here, and no existing full native Weil assertion.
- `rg` in `dag/lean_names_upstream.json` and DAG node records confirmed the
  published localizing-closure API and the recorded dependency names; no second
  definition of an existing notion has been introduced.

Validation: the final module compiled via prescribed `scompile.py` in module mode,
for both sandbox and library module names, without errors or warnings. Both named
theorems intentionally retain `sorry`; all universes and variables are explicit.
The source contract's example `CompactObject.lean` is now withdrawn, so its node's
existing-Mathlib binding was read along with the current module-mode instructions.

## Second reading by Q69

A separate pass by the same dispatcher-started worker reopened the node and final
Lean source and checked the twelve clause mappings above. No independent worker
was started, as the assignment explicitly forbids other agents; the maintainer's
independent delivery review remains the independent reading.

This pass found that an initial draft exposed a general compactification argument
rather than the native chosen one. The final theorem instead uses the exact
`HasCompactification.compactification` witness of the native framework in both F
and F_W. It also verified that solution-family arrows point Z→B_i, that the same
right adjoint G occurs in the representing-object clause, and that the hull theorem
includes both source idempotent-completeness assertions. No node statement changed.
The aliases use real data, the representatives theorem identifies the all-object
presentation with each small representative presentation, and all seven public
helper/theorem declarations are listed in `lean.declarations`.

## Repair of independent review H2

The return at immutable head `a3c1d133015b` identified one fault: the plain
hull abbreviation did not justify adding the theorem node
`lem-sf-locally-finite-adic-compact-support-sums` to `stmt_deps`. The saved
packet passed the initial prescribed dry run (commit `129c95cf12c`), but the
substantive H2 repair was still required.

Removed that added statement dependency, retaining it in `proof_deps`, and
changed its module import from public to plain. Expanded
`nativeWeilUnderlyingHull` directly to the existing bounded-constructible
predicate followed by `localizingClosure`, exactly as the return requested.
The read source of `nativeAdicConstructibleLocalizingHull` confirms this is
its literal defining expression, so no mathematical statement changes.
The recorded primary theorem signature is still verbatim and unchanged.

Compared the retained packet with the current shared node: after the repair,
only `lean` differs; the original five `stmt_deps`, statement, proof and
`proof_deps` agree exactly. No dependency module or new node is needed.
The second reading rechecked the expanded expression on the geometric fiber,
the unchanged universe u+1, both hull theorems and all twelve clause mappings
above. All previously accepted substance is retained.

Repair validation (2026-10-24): prescribed `scompile.py` compiled the repaired
file in both sandbox and library module modes (5.4 s and 5.5 s), with no
errors or warnings. The saved primary signature was checked verbatim; the
node differs from current main only in `lean`, the sums proof dependency is
retained, every line has at most 100 characters, and both theorem proofs
remain `sorry`.
