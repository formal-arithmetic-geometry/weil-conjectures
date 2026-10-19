## Worker report

Stage 2, Q65, 2026-10-17. This packet states the full generic abelian-category calculus in
`Sheaf.Algebra.Homology.FilteredDerivedHomCalculus`, with main theorem
`CochainComplex.FiniteFiltered.filteredDerivedHomCalculus`. The theorem asserts
`Nonempty (DerivedHomCalculus A)`. Unpacking that structure gives the three standard
triangulations, both truncation calculi over A, the truncation calculus over abelian groups,
and the filtered global Hom bifunctor with all comparisons. These are existential theorem
witnesses; no definition selects functors from a postponed non-unique existence assertion.
Every theorem in the packet has proof `sorry`. The raw localization and its objects have
real data. The main theorem's docstring includes all seven current DAG proof steps (maintainer fix: the former docstring steps 7 and 8 are merged into step 7, matching the node).

I read the current node, each statement dependency and its recorded source declaration,
the whole stage-2 brief, stage document, delivery-errors H, and the CompactObject example.
No maintenance repair note for this item exists. The retained sandbox contained no Lean,
node copy, or report: only dispatcher brief markers. The previous rejection describes a
stage-1 split, whereas the current node is split with no lean record. This delivery supplies
its missing stage-2 statement rather than trying to deliver an unchanged stage-1 node.

The source is Varshavsky, pp.39–41, §§5.1.1–5.1.2, Lemma 5.1.4(i), and §5.1.5; read from
the archived PDF. The current DAG's explicit bounded-input version is retained, not replaced
by an assertion that Hom of arbitrary bounded-below inputs is bounded below. Stacks 05S2–05S6
supply the localization convention. The known reversed adjunction wording in Varshavsky
5.1.1(c) is not used: the high truncation is right adjoint and the low quotient left adjoint.
Neither the item's statement nor a blueprint unit is changed.

Clause-by-clause rendering:

- Arbitrary abelian A: `A : Type u`, `[Category.{v} A]`, `[Abelian A]`, independent u and v.
  Enough injectives is exactly `[EnoughInjectives A]` on the main theorem. There is no
  finite-injective-dimension assumption and no equality between object and Hom universes.
  `[HasDerivedCategory.{max u v} A]` and the analogous instance for
  `AddCommGrpCat.{max u v}` are choices of localization, available from
  `HasDerivedCategory.standard`, not mathematical restrictions. All localizations and Hom
  groups fit in the common larger universe. The ordinary Hom representative uses
  `AddCommGrpCat.uliftFunctor.{u,v}` on `HomComplex K I` to transport the Hom universe v
  to max u v without restricting either universe.
- Bounded finite-filtered complexes: `FiniteFiltered.Complex A true` is the full subcategory
  of the existing `FilteredObject (CochainComplex A ℤ)` with `filtration.IsFinite` and
  `DegreeBound A true`. The latter requires strict lower and upper cochain bounds. `false`
  retains the lower bound only. `IsFinite` means whole and zero steps as subcomplexes, so its
  bounds are uniform in cochain degree. The maps are the existing filtration-preserving maps.
- Localization: `quasiIso bounded` means `∀ p, QuasiIso ((graded bounded p).map f)`.
  `Derived bounded` is literally this morphism property's `Localization`, and `Q bounded`
  is its canonical functor. `graded` uses the existing graded complex and its canonical map.
- Forgetting and grades: `TruncationCalculus.omegaComparison` and `grComparison` are natural
  isomorphisms after precomposition with Q, to the actual forgetful and graded complex
  functors followed by ordinary `DerivedCategory.Q`. Thus these are descended operations,
  not unrelated functors. For bounded inputs, `GlobalHomCalculus.omegaBounded` and
  `grBounded` factor them through the full ordinary bounded derived subcategory, with natural
  comparison isomorphisms. `BoundedDerived` means isomorphic to Q of a strictly bounded
  ordinary complex.
- For every integer r, raw high is the actual subcomplex `F^r K` with the induced intersection
  filtration; raw low is the actual cokernel of its inclusion with the image filtration.
  `highι` and `lowπ` are the actual inclusion and projection. The named truncation_bounds
  theorem contains only their required well-formedness proofs, not construction data.
- Exact descended functors: `TruncationCalculus.high` and `.low`, with CommShift and
  IsTriangulated fields for every r. The high/low comparison isomorphisms identify their
  values on QK with Q of the actual truncations. `inclusion_normalization` and
  `quotient_normalization` explicitly identify the natural transformations with Q applied
  to `highι` and `lowπ`.
- Distinguished triangles: `inclusion`, `quotient`, and natural `connecting` form the
  `Triangle.mk` in `distinguished` for every localized object. A natural connecting
  transformation into `high r ⋙ shiftFunctor _ 1` gives functoriality for every localized
  morphism. The `TriangulatedLocalization` instances are themselves existential witnesses
  normalized to actual cochain shifts and filtered cone triangles by `shiftComparison`,
  `shift_naturality`, and the iff `cone_normalization`. Raw cones use images of the canonical
  stepwise cone inclusions and the actual signed Mathlib cone-triangle projection.
- The specified high and low graded support is `high_support` and `low_support`, using
  `a < r` and `r ≤ a`. `unique_triangle` quantifies over every candidate distinguished
  triangle with those supports and asserts `∃!` triangle isomorphism whose middle map is
  exactly `𝟙 P`. It is not merely uniqueness of the end objects or of a chosen cone.
- Underlying triangles: omega has CommShift and IsTriangulated fields, so its image of the
  displayed distinguished triangle is distinguished. The raw-map normalization equations
  and omegaComparison identify the first two arrows with the underlying subcomplex inclusion
  and quotient. This also applies to all localized morphisms by naturality.
- Global Hom: `GlobalHomCalculus.filteredHom` is a curried bifunctor from bounded filtered
  objects, contravariant in its first variable, to `Derived false` over abelian groups.
  The target has uniformly finite filtration and bounded-below cochain representatives by
  the actual definition of that localization.
- Ordinary global RHom: `ordinaryHom` takes ordinary bounded derived arguments into ordinary
  D(Ab). `cohomology` is an additive equivalence in every integer degree with ordinary
  derived Hom into the shifted target; `cohomology_source` and `cohomology_target` state
  naturality in both variables. `ordinary_model` additionally identifies it with the
  actual universe-transported `HomComplex K I` whenever K is a bounded representative and
  I a bounded-below termwise-injective representative. Its hypotheses describe that model,
  not extra hypotheses on the item inputs.
- The underlying comparison is `underlyingComparison`, a natural isomorphism in the second
  variable; `underlying_source` states its first-variable naturality explicitly.
- The graded formula is `gradedComparison r P Q` to the point of `gradedSum r P Q`.
  This is a bilimit bicone on the family
  `ordinaryHom (grBounded a P) (grBounded (a+r) Q)` indexed by a in ℤ.
  `gradedSum_isBilimit` is its universal direct-sum assertion; `finite_support` says all
  summands outside a finite set are zero, so this is the required finite direct sum.
  Both `graded_source` and `graded_target` specify naturality of every projection component.
- The filtered Hom/H^0 formula is the additive equivalence `homEquiv P Q`, whose target is
  `H^0 (C.omega ((C.high 0) (filteredHom P Q)))`. `homEquiv_source` and `homEquiv_target`
  state precisely the precomposition/postcomposition naturality.
- Forgetful map: `forgetful_map` applies H^0 to the actual omega image of `C.inclusion 0`,
  then the underlying comparison, then the ordinary degree-zero cohomology equivalence.
  The equation identifies the result with the actual `B.omega.map f`, conjugated by the
  ordinary bounded-object comparison. The standard shiftFunctorZero iso removes [0].
- Graded projection: `C.gradeProjection` is a natural transformation from high 0 followed
  by omega to gr 0. Its raw normalization is exactly Q of the quotient F^0 K to
  F^0 K/F^1 K. `graded_projection` applies H^0 of this map and of the grade-zero bicone
  projection to a; the equation identifies it with `(B.gr a).map f`, conjugated by the
  graded bounded-object comparisons. The explicit eqToHom induced by `Int.add_zero a`
  normalizes a+0 to a, without a hidden let/show binder.
- Both cochain boundedness variants are supplied in `DerivedHomCalculus.bounded` and `.plus`;
  there is no global Hom assertion for two arbitrary plus inputs.

Dependencies used:

- `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic.
- `CategoryTheory.EnoughInjectives`, `Injective`, and `InjectiveResolution`,
  Mathlib.CategoryTheory.Preadditive.Injective.Basic/Resolution.
- `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`, and `homologyFunctor`,
  Mathlib.Algebra.Homology.DerivedCategory.Basic/HomologySequence.
- `CategoryTheory.DecreasingFiltration`, upstream
  WeilConjectures.CategoryTheory.Abelian.Filtration; `FilteredObject` and `IsFinite`,
  WeilConjectures.CategoryTheory.Filtration; `induced`, `quotient`, `step`, and `gradedPiece`,
  Sheaf.CategoryTheory.Filtration. See the lean-only representation repair below.
- `DecreasingFiltration.complexQuotientπ` and the recorded subquotient module,
  Sheaf.Algebra.Homology.FilteredComplexSubquotients.
- `FilteredObject.restrictionSteps` and `gradedMapSteps`,
  Sheaf.CategoryTheory.FiniteFiltrationInduction.
- Proof-only imports of the localization universal-property interface, K-injective Hom and
  plus injective representative interfaces, and the recorded
  `CategoryTheory.Pretriangulated.triangle_morphism_extension` upstream module are retained.
  The two not-yet-stated filtered model/embedding proof prerequisites have no module to import;
  no proof of them is silently assumed as an input to the statement.

Edge cases checked: zero category/object/complex, empty graded support (the bicone point is
zero); one-step filtrations in any integer degree; cut r outside either filtration bound,
giving the trivial inclusion/quotient triangles; source grade 1 and target grade 0 contribute
Hom grade -1, and the reverse gives +1; arbitrary positive/negative cochain degrees and
r=0; Q with infinite injective dimension (resolution bounded below only); the distinction
between a zero derived graded piece and a literally zero representative; independent u/v.
The H^0 projection equation was compiled with the necessary a+0 equality transport. No
counterexample or disputed statement was found.

Searches made through msearch.py, Q65 and this item:

- LeanFinder: "filtered derived global Hom with finite decreasing filtrations truncation
  triangles associated graded derived Hom" — eight ordinary derived-category bound/fraction
  declarations, no filtered calculus.
- Loogle: "FilteredComplex, DerivedCategory, HomComplex" — zero hits, unknown FilteredComplex.
- Mathlib grep: "FilteredDerived|filteredDerived|RHomF|filtered.*derived", CategoryTheory —
  zero hits. Whole upstream and project rg searches found only module/two-step localizations,
  subquotient machinery, and unrelated filtered-colimit facts. Exact item-tag grep found no
  upstream declaration. Relevant ordinary source signatures were opened.
- LeanSearch: "localization of finite filtered bounded cochain complexes at graded quasi
  isomorphisms" — eight ordinary localization declarations; no generic finite-filtered one.
- LeanFinder: "finite decreasing filtrations on bounded complexes and filtered derived
  localization category" — eight ordinary boundedness/truncation declarations, no match.
- DAG and blueprint searches for finite filtered and filtered derived category found the
  specialized nodes described below and no generic definition; blueprint search returned
  zero matching blueprint-node texts. New full declaration names were searched in all three
  Lean source trees with no collision.

Validation: the two modules were compiled together through scompile.py, each compiled alone
in dependency order, against the published library plus private side overlay. Both compile
without errors or warnings. Compilation is statement validation only; all postponed proofs
remain named `sorry` theorems. The prescribed delivery dry run is the final validation step.

## Localization interface

The repository already contains the generic bounded-below finite-filtered localization node
`def-trf-finite-filtered-localization` (Q03), whose published module is imported. Its
objectwise finite-filtration interface allows bounds varying with cochain degree, whereas
this item needs the source's uniform finite filtration on a whole cochain complex and its
strict bounded/strict bounded-below variants. The compatible uniform-complex construction
is therefore declared in the owning item module, under the same existing filtration,
graded-map, quotient, and cone interfaces; no independent new DAG definition node or
private filtration notion is introduced. The three search kinds and upstream/project/DAG
searches are recorded above. The bounded-derived pro-etale specialization, two-step module
localization, and module homotopy nodes do not supply this generic interface.

## Dependency modules

`def-sp-filtration` receives a lean-only existing-declaration repair under §1(B), with no
new module: the binding is the exact upstream `CategoryTheory.DecreasingFiltration` in
WeilConjectures.CategoryTheory.Abelian.Filtration. I opened the current server sources of
both the recorded PBCDecreasingFiltration and this declaration. They give the same decreasing
subobject family, but the PBC structure is not accepted by the already recorded
FilteredComplexSubquotients and gradedMapSteps interfaces. Reusing the existing original
representation makes these dependent interfaces compose; no mathematical assumption or
filtration definition is changed. The upstream PBC declaration and all its consumers remain
available. Every other field of the dependency node is preserved. Its lean.note explains
this precise incompatibility and the exact reuse.


## Second reading by Q65

I read the node statement clause by clause against Varshavsky, pp. 39--41, §§5.1.1--5.1.5
and Lemma 5.1.4(i), and against Stacks Tags 05S2--05S6. The following list records each
object, hypothesis, and conclusion clause and the Lean rendering.

* The ambient object is an arbitrary `A : Type u` with `[Category.{v} A]` and
  `[Abelian A]`; enough injectives is exactly `[EnoughInjectives A]`. The Lean theorem
  `filteredDerivedHomCalculus` has no finite-dimensional, Noetherian, or finite-injective-
  dimension assumption and leaves `u` and `v` independent. Its derived categories use
  `HasDerivedCategory.{max u v} A` and the common larger universe for `AddCommGrpCat`,
  matching the node's universe convention.
* The bounded filtered objects are `CochainComplex.FiniteFiltered.Complex A true`:
  existing `FilteredObject (CochainComplex A ℤ)`, finite as one whole filtration and
  strictly bounded below and above. Morphisms are the existing filtration-preserving
  maps. The bounded-below `+` version is `Complex A false`, with the same finite
  filtration and only the strict lower cochain bound. This is exactly the node's
  `DF^b` and `DF^+` convention; filtration bounds are independent of cochain degree.
* The graded functor is `FiniteFiltered.graded`, using the recorded
  `FilteredComplexSubquotients` graded quotient and its canonical graded map. The
  localization is `FiniteFiltered.Derived`, at `FiniteFiltered.quasiIso` (a map is a
  quasi-isomorphism on every grade), with canonical functor `FiniteFiltered.Q`. Thus the
  Lean object is the node's localization, rather than an unrelated ordinary derived
  category.
* The actual pre-localization truncations are `FiniteFiltered.highObject` (`F^r K` with
  induced/intersection filtration) and `lowObject` (the cokernel `K/F^r K` with image
  filtration), with maps `highι` and `lowπ`. `truncation_bounds` and the corresponding
  `high`/`low` definitions preserve precisely the stated finite filtration and cochain
  bounds.
* For every `r : ℤ`, `TruncationCalculus.high` and `.low` descend these operations to
  exact functors, with `inclusion` and `quotient` natural transformations. Their
  `highComparison`, `lowComparison`, `inclusion_normalization`, and
  `quotient_normalization` fields identify them with the actual subcomplex inclusion and
  quotient before localization. `distinguished` gives the displayed triangle, and
  `connecting` makes it natural in every localized morphism. `high_support` and
  `low_support` state exactly `gr^a L = 0` for `a < r` and `gr^a R = 0` for `r ≤ a`.
  `unique_triangle` gives the required unique triangle isomorphism fixing the middle
  object by `e.hom.hom₂ = 𝟙 P`; it is uniqueness of the whole triangle, not only of its
  ends. The `omega` fields assert the underlying distinguished triangle and identify
  its first two maps after forgetting the filtration.
* The filtered global Hom is `GlobalHomCalculus.filteredHom`, contravariant in its first
  bounded filtered argument and covariant in its second, with values in the bounded-below
  finite-filtered localization over `AddCommGrpCat`. `underlyingComparison` identifies
  its underlying object with the ordinary derived Hom; `ordinaryHom`, `cohomology`,
  `cohomology_source`, and `cohomology_target` identify the ordinary Hom complex and its
  degree-`q` cohomology with `Hom_D(ωP,ωQ[q])` (and the graded analogues). The explicit
  `ordinary_model` is the concrete universe-transported `HomComplex` model required by
  the node's “derived Hom complex of abelian groups” clause, not an additional input
  hypothesis.
* For every `r`, `gradedComparison` identifies `gr^r H` with a biproduct bicone whose
  components are `ordinaryHom (gr^a P) (gr^(a+r) Q)`. `gradedSum_isBilimit` gives the
  canonical direct-sum universal property and `finite_support` makes the sum finite.
  `graded_source` and `graded_target` give naturality in both variables, with the target
  index `a+r` and hence the node's target-minus-source sign convention.
* `homEquiv` is the additive equivalence
  `Hom_DF(P,Q) ≃ H^0(ω(t_{≥0} filteredHom P Q))`. Its source and target naturality
  fields give functoriality. `forgetful_map` identifies the map to ordinary derived Hom
  with `H^0` of the inclusion `ω t_{≥0}H → ωH`; `gradeProjection` and
  `graded_projection` identify the grade-zero projection components with the actual maps
  `gr^a P → gr^a Q`, including the explicit `a + 0 = a` transport.
* `DerivedHomCalculus` supplies the bounded, bounded-below, and abelian-group
  triangulated localization models needed by the node's “same notation with +” clause;
  it asserts no extra hypothesis on the inputs. The theorem asserts only `Nonempty` of
  this package, so no non-canonical functor is selected from a postponed existence proof.

Edge cases checked: the zero category, zero complexes and zero graded pieces; empty graded
support (the bicone is the zero biproduct); one-step filtrations in any integer degree;
cuts `r` outside the filtration interval (trivial inclusion or quotient triangles);
`r = 0`; positive and negative cochain degrees; source grade 1/target grade 0 and the
reverse cross-grade sign; arbitrarily large injective dimension (only bounded-below
resolutions); and independent object/category universes. Empty index sets do not occur
as a hidden hypothesis: the graded index is all of `ℤ`, with finite support supplied by
`finite_support`.

Searches were repeated with `msearch.py`/LeanFinder/Loogle and `rg` over Mathlib,
`WeilConjectures/`, and the repository's `lean/Sheaf`: no generic finite-filtered derived
localization or filtered RHom calculus exists. The only nearby declarations are ordinary
derived-category localizations and module/two-step filtered specializations. The exact
item tag has no upstream declaration.

The existing localization interface is imported, while the owning item module supplies
its uniform whole-complex bounded/plus presentation and all real construction data; only
named theorem proofs remain postponed. I also repaired the recorded `def-sp-filtration`
Lean binding under §1(B): its consumers require the exact upstream
`CategoryTheory.DecreasingFiltration`, not the incompatible PBC representation. The
mathematical statement and all other node fields are unchanged. No statement correction
was needed. The delivered module compiles cleanly with `scompile.py`; the remaining proofs
are the named `sorry` declarations documented in its docstrings.
