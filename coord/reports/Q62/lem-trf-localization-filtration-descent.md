## Worker report

Repair of the independent stage-2 return for immutable head `9ba3ac27feb6`, H3.
The retained packet was inspected first and its required initial dry run passed as
`249ff7de36`. A successful mechanical check did not resolve the mathematical return:
that packet still used `DerivedCategory.Plus` and an arbitrary `D` and `Presentation`.
This repair replaces that interface substantively, preserving the node's statement.

The only theorem is `AlgebraicGeometry.Etale.localization_filtration_descent`, with
proof `sorry`. The auxiliary definitions in its module contain real data or are
transparent abbreviations/Prop-valued specifications; the two additive instances
are inherited by `infer_instance`. The four old, unregistered helper sorry lemmas
and the bounded-below derived-map definition have been removed.

### Hypotheses, one by one

- `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`: finite commutative coefficients.
  `LocalizationCoefficients Λ = ModuleCat.{u+1} Λ` includes all modules over Λ;
  no finiteness restriction is placed on a sheaf or its sections.
- `{U X Z : Scheme.{u}}`, `j : U ⟶ X`, `i : Z ⟶ X`: the three schemes and maps.
  `[IsOpenImmersion j]` and `[IsClosedImmersion i]` give precisely their stated kinds.
- `hcomplement : Set.range i = (Set.range j)ᶜ`: the closed/open complementary images.
- `LocalizationSheaves Λ X` is `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)`:
  ordinary module-valued sheaves on the small étale site, the encoding of the
  recorded six-functor declarations (as mandated by the project's coefficient convention).
- `hJinvL` and `hJinvC` assert preservation of finite limits and finite colimits
  by the recorded `openImmersionRestriction`, namely `j^{-1}`.
- `hIL` and `hIC` assert the same two properties for the recorded `upperStar`,
  namely `i^{-1}`.
- `hJL` and `hJC` assert the same two properties for the recorded
  `openImmersionLowerShriek`, namely `j_!`.
- `hIstarL` and `hIstarC` assert the same two properties for the recorded
  `lowerStar`, namely `i_*`. All four functors are additive; preservation of
  finite limits and colimits is the categorical exactness condition here.
- `hdegree` quantifies over `LocalizationBoundedComplexes Λ X` and all `n : ℤ`.
  This category uses `FiniteFiltered.DegreeBound _ true`: both a strict lower
  degree bound and a strict upper degree bound. The earlier stronger hypothesis
  on all complexes has been removed. Its two arrows are exactly the counit
  of `openImmersionLowerShriekAdjunction` followed by the unit of
  `upperStarLowerStarAdjunction`, evaluated at `B.obj.X n`. The existential
  proof of zero composite constructs `ShortComplex.mk`; `.ShortExact` gives
  `0 → j_!j^{-1}Bⁿ → Bⁿ → i_*i^{-1}Bⁿ → 0`.
- `[HasDerivedCategory.{u+2} (LocalizationSheaves Λ X)]` is the ordinary chosen
  localization model in the standard object/Hom universe; it is available by
  `HasDerivedCategory.standard`, not a geometric/exactness hypothesis. Every
  universe is explicitly bound (`universe u`, module size `u+1`, derived size `u+2`).
  No arbitrary filtered target or presentation is assumed.

### Conclusions, clause by clause

`LocalizationFiltrationDescentData Λ j i` states the following as conclusions.

- The actual prelocalization functor `T` goes from bounded ordinary complexes to
  `CochainComplex.FiniteFiltered.Complex (LocalizationSheaves Λ X) true`.
  This existing category consists of bounded cochain complexes with uniformly
  finite decreasing filtrations by subcomplexes. Filtration bounds are independent
  of cochain degrees. The underlying natural isomorphism `e` identifies `T(B)`
  with the given complex B on both objects and chain maps.
- The filtration has `F 0 = ⊤`, `F 2 = ⊥`. Its first step is pinned to the
  *actual counit subcomplex*: in every degree the image of its inclusion,
  transported by `e`, equals the image of the specified counit. The exactness
  assumption makes this counit monic, so this is precisely `F¹B=j_!j^{-1}B`.
  Antitonicity gives the constant endpoints for every `p≤0` and `p≥2`.
- Natural isomorphisms `T ⋙ graded true 0 ≅ inclusion ⋙ closedStepComplex` and
  `T ⋙ graded true 1 ≅ inclusion ⋙ openStepComplex` give the two graded complexes
  and their maps, not just a list of isomorphic graded objects. Other grades
  are `IsZero` before localization.
- For each bounded chain map `f`, `QuasiIso f.hom` implies
  `FiniteFiltered.quasiIso true (T.map f)`. By its existing definition, this
  quantifies over *every* associated-graded chain map, exactly the first conclusion
  in the node. No such preservation is added as a hypothesis.
- The ordinary derived category is Mathlib's `DerivedCategory.Bounded`, not
  `Plus`. The functor `q` is required to be a localization at the ordinary
  quasi-isomorphisms between bounded complexes; the natural isomorphism `a`
  identifies its composite with the inclusion into `DerivedCategory` with the
  usual `DerivedCategory.Q` on bounded complexes and maps.
- The filtered target is the concrete formal localization
  `CochainComplex.FiniteFiltered.Derived (A := LocalizationSheaves Λ X) true`.
  The Boolean `true` imposes both cochain bounds. There is no target parameter D.
- The functors `omega` and `gr p` into the bounded derived category are conclusions.
  Their natural factorization isomorphisms through `FiniteFiltered.Q true`
  identify them with the actual forgetful and quotient-complex functors composed
  with ordinary Q. Thus they are the canonical forgetful/graded functors on
  every chain map, not arbitrary maps with suitable domains.
- The actual section `S : DerivedCategory.Bounded _ ⥤ FiniteFiltered.Derived true`
  has a natural `sectionIso : S ⋙ omega ≅ 𝟭`. Crucially, `d : q ⋙ S ≅ T ⋙ Q`
  pins S to the canonical filtration assignment. The displayed equation involving
  `a`, `b`, `d`, `e`, and `sectionIso` normalizes the section isomorphism to the
  underlying identity on complexes. The earlier packet had no such link between
  its existential filtration representatives and S; that gap is removed.
- `closedD` and `openD` are ordinary bounded derived endofunctors normalized,
  by natural isomorphisms after q and inclusion, to the termwise composites
  `i_*i^{-1}` and `j_!j^{-1}` followed by Q. `S ⋙ gr 0 ≅ closedD` and
  `S ⋙ gr 1 ≅ openD` are the natural descended graded identifications. All
  other grades vanish after inclusion into the ordinary derived category.
- For every specified derived isomorphism `f : K ≅ L`, the conclusion supplies
  `f' : S.obj K ≅ S.obj L` with `f'.hom = S.map f.hom`; its underlying map
  agrees with f through `sectionIso`. Thus independence of representatives is
  functorial relative to the chosen identifications, including identity maps
  and nontrivial automorphisms; no uniqueness of unmarked isomorphisms is asserted.

The source was opened at https://arxiv.org/pdf/math/0505564, printed p.42,
Example 5.2.3: it constructs the section first on bounded complexes by the open
first step and then descends by exactness. Section 5.1.1(e) includes the bounded
variant and §5.1.2(a)–(b) specifies graded quasi-isomorphisms and the forgetful/graded
localizations. The theorem docstring now gives all four proof steps in the node,
including the finite filtered-cone induction for arbitrary graded quasi-isomorphisms.
The node's more general ordinary-sheaf statement already isolates the exactness
assumptions used by this construction; no constructibility condition is introduced.

### Dependencies and searches

The recorded declarations were read and retained:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`;
  Mathlib's `IsOpenImmersion`/`IsClosedImmersion` implement the morphism convention.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionRestriction`, `Etale.openImmersionLowerShriek`,
  `Etale.openImmersionLowerShriekAdjunction`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the general
  ringed-site interface; here the fixed-coefficient encoding is the ordinary
  module-valued sheaf category required by the recorded geometric functors.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`: `DecreasingFiltration`,
  `F`, `F_succ_le`, `gr`; its current source was also read with `scompile.py --source`.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`: `complexStep`,
  `complexQuotient`, `complexQuotientπ`, `gradedPiece` and `gradedMapSteps` through
  its imports, the actual filtration quotient objects and maps.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.TStructure`:
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Bounded` and its inclusion.
- `Sheaf.Algebra.Homology.FilteredDerivedHomCalculus`:
  `CochainComplex.FiniteFiltered.DegreeBound`, `Complex`, `forget`, `graded`,
  `quasiIso`, `Derived`, `Q`. Its owning node
  `lem-trf-filtered-derived-hom-calculus` is now added to `stmt_deps`, as permitted
  for an already landed interface. Its definitions, not its existence theorem or
  extra enough-injectives hypothesis, are used. A graph read confirmed it has no
  dependency path back to this item.
- Proof imports: `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
  (`mappingCone.quasiIso_iff_acyclic`), Mathlib `HomologySequence` and
  `Localization.Predicate` for the recorded proof dependencies.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` supplies the existing
  coefficient-category Grothendieck/abelian instances. Removing its old indirect
  import exposed missing instances; its direct import repairs that without hypotheses.

Searches (the msearch wrapper records the full responses in `searches.jsonl`):

- LeanFinder, `bounded filtered derived localization canonical open closed filtration
  section`: ordinary bounded-derived representative lemmas and unrelated local
  cohomology results; no matching section.
- LeanSearch, `canonical two step open closed localization filtration section bounded
  filtered derived category`: `HasDerivedCategory.standard`, `DerivedCategory.Q`,
  localization instances and bounded representative lemmas; no matching filtered section.
- Loogle, `DerivedCategory.Bounded`: exact existing category and inclusion found
  in Mathlib's `DerivedCategory.TStructure`; used directly.
- Grep, `localization.*filtration|filtered.*derived` in Mathlib/Algebra/Homology:
  zero hits. `rg` in upstream WeilConjectures and side `lean/Sheaf` found the
  existing filtered calculus and no declaration of this section. The saved packet's
  searches also found no matching section. Searching the node id upstream gave no match.
- `tools/blueprint_refs.py search 'bounded filtered'`: zero blueprint-node hits;
  direct DAG/name searches identified the already landed calculus node, which is reused.

Edge cases checked: zero complexes, zero coefficient ring and zero sheaves satisfy
both strict degree bounds and all endpoint conventions; an empty open or closed
component is permitted by the complement condition and gives respectively the
pure closed or pure open filtration. A bounded-below complex with nonzero terms
in arbitrarily large degrees is excluded by `DegreeBound _ true`, as it must be.
Every cochain degree and every filtration index is quantified over all integers.
Filtration bounds are per object, not a global interval imposed on all complexes
in the localization. The section's image alone has the specified two-step bounds.
Identity derived isomorphisms and arbitrary automorphisms are included in the
representative-independence clause. No `STATEMENT-DISPUTED` issue was found.

Only `lean` and the addition of the already landed calculus node to `stmt_deps`
change from the current read-only base. No mathematical statement correction,
new DAG node, dependency-record repair or live-source edit is needed.

## Second reading by Q62

Reread the node and the revised Lean file clause by clause after compilation.
The returned H3 defect is removed in both places: the source of S is now
`DerivedCategory.Bounded` and its target is the actual `FiniteFiltered.Derived true`.
No `D`, `Presentation` or `DerivedCategory.Plus` occurs in the statement module.
The only boundedness predicate is the existing two-sided `DegreeBound _ true`.
The short exact sequence assumption is restricted to bundled bounded B, exactly
as the node says. Each of the four sheaf functors has its two exactness hypotheses;
its two arrows remain the specified adjunction counit/unit.

This reading also checked the relation between the filtration and the descended
section: `T`, `e` and the counit-image equation fix the canonical prelocalization
assignment; `d` identifies its localization with `q ⋙ S`; the normalization equation
fixes the section isomorphism on complexes. Consequently, separately existing
unrelated representatives cannot satisfy the intended section clause by accident.
The preservation clause concerns the actual filtered maps `T.map f`, so it is
stronger evidence of descent than the old two ordinary endofunctor tests. The
natural graded comparisons, their termwise factorizations, and the final transport
equation render the graded and representative-independence clauses.

All helper definitions have real bodies and are listed in `lean.declarations`.
Only the item's theorem is postponed, with a complete four-step proof docstring.
The file has `autoImplicit false`, explicitly declared universes and no long lines.
Validation uses the prescribed per-file `scompile.py`, then the server preflight
and file compiles in `deliver2.py --no-push`; the delivered theorem remains a
stage-2 statement, not a proof delivery.
