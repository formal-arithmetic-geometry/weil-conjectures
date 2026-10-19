## Worker report

The module `lean/Sheaf/AlgebraicGeometry/EtaleAmbientAdjointLocality.lean` renders
`lem-amb-etale-adjoint-locality` on the ordinary, whole unbounded derived categories of
constant-ring module sheaves. Two definitions have real data: the degreewise derived
sum/evaluation adjunction, and the specified compact-support/sum-extension composition
comparison. The sole postponed theorem is
`AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`; its proof is `sorry`,
and its docstring carries all eight proof steps of this DAG node.

The previous draft's `Nonempty` conclusion failed to express canonicity. This continuation
repairs that defect. The theorem now asserts a unique natural isomorphism whose adjoint
transpose is the inverse specified composition comparison, followed by the sum/evaluation
counit and then the compact-support counit. Both supplied compact-support adjunctions
actually occur in this equation. Composing with an arbitrary natural automorphism no
longer preserves the conclusion. The previous prerequisite waits are resolved: both
`lem-amb-etale-compact-comparisons` and
`lem-asd-etale-compact-support-normalization` now have usable recorded declarations.
They are added to `stmt_deps`, as authorized for newly landed prerequisites.

Clause-by-clause statement check:

| Node clause or hypothesis | Lean rendering |
| --- | --- |
| A is a commutative ring | `(A : Type (u + 1)) [CommRing A]` |
| Ordinary unbounded D(T_et,A) of constant-ring module sheaves | `DerivedCategoryModule A T`, definitionally `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`; no `Plus`, boundedness, or constructibility predicate |
| u : U → X | `{U X : Scheme.{u}} (u : U ⟶ X)` |
| u is etale and separated | `[Etale u] [IsSeparated u]` |
| u is of finite type | `[LocallyOfFiniteType u] [QuasiCompact u]` |
| Sum extension on sheaves, rather than an unrelated extension functor | The recorded `etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance` |
| Sum extension is exact on sheaves | Existing `preservesFiniteLimits_etaleLowerShriek`; existing `isLeftAdjoint_etaleLowerShriek` gives preservation of finite colimits. These are listed in `lean.declarations`, not restated. |
| Its termwise descent is left adjoint to u* on the entire derived categories | `derivedEtaleLowerShriekUpperStarAdjunction` has type `(etaleLowerShriek ...).mapDerivedCategory ⊣ (upperStar ... u).mapDerivedCategory`; its body applies `mapDerivedCategoryAdjunction` to the actual sum/evaluation sheaf adjunction. No finiteness assumption on A occurs here. |
| For the compact-support assertion A is finite | `[Finite A]` on the comparison helper and locality theorem, but not on the preceding adjunction |
| f : X → S and fu : U → S | `(f : X ⟶ S)` and the actual composite `(u ≫ f)` |
| U, X, S are Noetherian | `[IsNoetherian U] [IsNoetherian X] [IsNoetherian S]`; Mathlib identifies this with the finite affine Noetherian-cover condition |
| Both morphisms are compactifiable | Arbitrary `(c : Compactification f)` and `(d : Compactification (u ≫ f))`; these carry the actual open/proper factorizations. Their ambient schemes are Noetherian by finite type over the Noetherian target. |
| f^× and (fu)^× are their ordinary compact-support right adjoints | Functors `F` and `G`, with `adjF : rightDerivedLowerShriekOfCompactification ... c ⊣ F` and the corresponding `adjG` for `d`; no fixed Brown choice and no arbitrary replacement functor |
| For every unbounded K | `(K : DerivedCategoryModule A S)` in the normalization equation |
| Natural isomorphism u* f^× K ≅ (fu)^× K | `e : F ⋙ (upperStar ... u).mapDerivedCategory ≅ G`, whose component at K is the displayed objectwise isomorphism |
| Canonical isomorphism | `∃! e`, with the explicit equality of counit transposes in the theorem's conclusion |
| Only ordinary etale compact supports | Both left functors are exactly the dependency's `rightDerivedLowerShriekOfCompactification`, on the ordinary small-etale module category; no pro-etale construction occurs |

For clarity, in the displayed equation put `L = u* (F K)` and let
`c_M : Rf_! Du_Σ! M ≅ R(fu)_! M` denote `etaleAmbientLeftComparison`.
The equation reads

`R(fu)_!(e_K) ≫ ε^(fu)_K = c_L⁻¹ ≫ Rf_!(ε^u_(F K)) ≫ ε^f_K`.

This is exactly the transpose in step 8 of the node's proof. The normalized family
`N : EtaleCompactSupportNormalization A` is universally quantified in the conclusion,
not assumed as an extra hypothesis. Its existence is the recorded theorem
`nonempty_etaleCompactSupportNormalization A`. Thus the theorem specifies the same
canonical map for every family satisfying that node's graph and homotopy normalization.
There is no choice from a bare `Nonempty` natural isomorphism.

The actual left comparison is constructed as follows. Given c for f and d for fu, use
`e = d.ofComp c`, the existing closure construction compactifying `u ≫ c.i`. The
compactification `e.restrict` is of u. Invert `N.comparison u e.restrict` and whisker by
`Rf_!^c`; compose with
`rightDerivedLowerShriekOfCompactificationCompIso A c e`; finally compose with
`rightDerivedLowerShriekOfCompactificationIso A (c.comp e) d`. These are actual canonical
constructions, not parameters standing for arbitrary maps. No K-flat, bounded-below,
or constructible subcategory has been substituted for the whole derived category.
The common-refinement and proper/open comparisons are the existing unbounded interfaces;
the bounded-below normalization is supplied by the recorded comparison prerequisite.

Dependency declarations read and used:

- `def-amb-etale-compact-support`: module
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, declaration
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`; its body is exactly
  degreewise open extension followed by total unbounded derived direct image.
- `def-asd-compactifiable`: module `Sheaf.AlgebraicGeometry.CompactifiableOverField`,
  whose defining clause reuses `AlgebraicGeometry.Compactification` and
  `AlgebraicGeometry.HasCompactification` from `WeilConjectures.Compactification.Defs`.
  Its additional field-existence theorem is not imposed on the present arbitrary schemes.
- `def-weil-pbc-derived-categories`: module `Sheaf.AlgebraicGeometry.DerivedCategories`,
  using `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `def-weil-scheme-morphism-properties`: the recorded convention fixes no separate
  declaration. Its named notions are the Mathlib `IsSeparated`, `LocallyOfFiniteType`,
  and `QuasiCompact` classes, used directly here.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`, read with its affine ring-map signature and docstring.
- `def-weil-pbc-etale-sum-extension`:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`,
  `AlgebraicGeometry.Etale.etaleLowerShriek`; the same module supplies its sum/evaluation
  adjunction and finite-limit preservation.
- `thm-amb-etale-exceptional-adjoint`: `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`,
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
  The theorem quantifies over any chosen adjunctions rather than choosing another datum.
- `lem-asd-etale-compact-support-normalization`:
  `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`, structure
  `AlgebraicGeometry.Etale.EtaleCompactSupportNormalization`, its `comparison`,
  `sheaf_normalization`, `derived_normalization`, refinement and adjunction clauses,
  and the recorded `nonempty_etaleCompactSupportNormalization` existence theorem.
- `lem-amb-etale-compact-comparisons`:
  `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`,
  `AlgebraicGeometry.Etale.etaleCompactSupport_refinementComparison_eq` and its recorded
  upstream composition/refinement interfaces. The unbounded comparison construction
  uses the full signatures of `rightDerivedLowerShriekOfCompactificationCompIso` and
  `rightDerivedLowerShriekOfCompactificationIso`, from
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` and
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded`.
- The generic degreewise adjunction construction is
  `CategoryTheory.Adjunction.mapDerivedCategoryAdjunction`, in
  `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`.

Every recorded proof-dependency module is imported. Mathlib leaves use their recorded
`mathlib_match` files, including exact derived descent, localization, stalk exactness,
Noetherianity and scheme base change. No statement dependency has been copied privately.
There are no new nodes, dependency repairs, or changes to the natural-language statement.

Edge cases checked before the repair:

- The zero ring is allowed: no `Nontrivial`, nonzero characteristic, or invertible-prime
  hypothesis appears. The normalization datum and counits still make sense.
- Empty schemes and empty etale maps are included. The functors and the counit
  characterization work in the corresponding zero derived category.
- Identity maps use the identity-normalized comparison of the prerequisite. The
  formula becomes the standard adjunction-preserving comparison of right adjoints.
- Disconnected etale maps and finite-sheet maps retain the sum/evaluation counit;
  the comparison does not replace sums by a chosen single sheet.
- Arbitrarily unbounded complexes and degree zero are included. There is no bound or
  cohomological condition on K. The first assertion allows arbitrary commutative A.
- Universes are explicit: `universe u`, `Scheme.{u}`, and `ModuleCat.{u + 1} A` with
  `A : Type (u + 1)`, exactly the recorded dependency convention. `autoImplicit` is false.
- Compactifications and adjunctions are arbitrary. The normalization equation changes
  correctly when a chosen adjunction changes, since both `adjF` and `adjG` occur in it.

Searches performed again in this continuation (the earlier search log is also retained
in the sandbox):

| Tool | Query | Result |
| --- | --- | --- |
| `msearch.py leansearch` | etale inverse image compact support exceptional right adjoint canonical locality | Service unavailable: Internal Server Error; recorded as unavailable, not a match verdict |
| `msearch.py leanfinder` | Canonical restriction of exceptional right adjoint along an etale map using compact support composition | Eight hits about ordinary scheme-module restriction and ringed-space maps; no matching ordinary-etale exceptional-locality theorem |
| `msearch.py loogle` | `CategoryTheory.Adjunction.rightAdjointUniq` | Twelve generic uniqueness/unit/counit lemmas; these require the specified left comparison and do not supply this locality statement |
| `msearch.py grep` in CategoryTheory | `etaleAmbient\|etaleLowerShriek.*Adjunction` | Zero hits |
| `rg` in upstream WeilConjectures and project `lean/Sheaf` | `derivedEtaleLowerShriekUpperStarAdjunction\|etaleAmbient\|lem-amb-etale-adjoint-locality` | Only the existing bounded-below `derivedEtaleLowerShriekUpperStarAdjunctionPlus` and its uses; no duplicate full unbounded locality declaration |
| `rg` in upstream Etale and Compactification sources | `etaleLowerShriekUpperStarAdjunction`, `preservesFiniteLimits_etaleLowerShriek`, `ofComp`, `restrict`, `CompIso`, compactification independence | Found the existing exact sheaf functor and the canonical constructions reused here; read their full relevant signatures and docstrings |

A full traversal of both statement and proof dependencies of the normalization prerequisite
visited 9746 nodes without reaching this item. Adding that prerequisite is acyclic.

Validation: the required `scompile.py NE lem-amb-etale-adjoint-locality` compiled the
module with all proof imports cleanly. It also compiled the two newly needed side-only
proof dependency overlays. The final library-file check took 4.4 seconds; no errors or
warnings were reported. The module has no file-local notation, private definitions, or
local instances; all lines are at most 100 characters. The node's `lean.statement` is
extracted verbatim from the final theorem signature. The delivery dry run is the final
validation step; no push or delivery by this worker is authorized.

This continuation addresses the earlier independent reader's canonicity objection;
it is not a second reading of the revised module. The next reader must independently
check the new left comparison and counit equation before delivering.

## Second reading by NE

I independently read the sandbox node and module, the blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md`, and Stacks
`etale-cohomology.tex`, Definition `definition-extension-zero` (03S3), Proposition
`proposition-describe-jshriek` (03S5), and Proposition
`proposition-finite-higher-direct-image-zero` (03QP). I also read
`sites-modules.tex`, Lemma `lemma-extension-by-zero-exact` (03DJ). The first assertion
of these sources allows any ring and imposes no Noetherian, finite-coefficient, or
invertible-characteristic hypothesis. The finite-coefficient and Noetherian hypotheses
belong to the node's second assertion. The sandbox node has no `statement_change`;
its natural-language statement agrees with the repository node.

My object, hypothesis and conclusion inventory, matched against the actual Lean:

| Node item | Lean rendering and verdict |
| --- | --- |
| A commutative ring, arbitrary for the first assertion | `A : Type (u + 1)` and `[CommRing A]` on `derivedEtaleLowerShriekUpperStarAdjunction`; no `[Finite A]` there. Correct. |
| Schemes U and X and the map u | `{U X : Scheme.{u}} (u : U ⟶ X)`. These are arbitrary schemes, with no base field. Correct. |
| u separated, etale and finite type | `[Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]` on the adjunction and main theorem. The last two classes express finite type. Correct. |
| Constant-ring module sheaves on the ordinary small etale site | Every coefficient category is `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`, through the recorded `DerivedCategoryModule`. Correct; no structure-sheaf modules or pro-etale category occurs. |
| The specified sum extension is exact on sheaves | The recorded `etaleLowerShriek` is precisely sheafification of the left Kan extension indexed by lifts. The existing `preservesFiniteLimits_etaleLowerShriek` and `isLeftAdjoint_etaleLowerShriek` supply finite limits and finite colimits. Correct; exactness has not been replaced by an assumption. |
| Its termwise derived functor is left adjoint to u* on the whole categories | `derivedEtaleLowerShriekUpperStarAdjunction` has exactly the type `(etaleLowerShriek ...).mapDerivedCategory ⊣ (upperStar ... u).mapDerivedCategory`. Its body applies the existing exact-functor descent to the actual sheaf adjunction. Correct, including its unit and evaluation counit. |
| A additionally finite for compact supports | `[Finite A]` on `etaleAmbientLeftComparison` and `existsUnique_etaleAmbientAdjointLocalityIso`. Correct; no nontriviality or invertibility restriction. |
| S and f : X → S, with fu the actual composite | `{U X S : Scheme.{u}}`, `(f : X ⟶ S)`, and `Compactification (u ≫ f)`. Correct; no independent map is substituted for fu. |
| U, X and S Noetherian | `[IsNoetherian U] [IsNoetherian X] [IsNoetherian S]`. Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with the node's finite affine Noetherian-cover convention. Correct. |
| f and fu compactifiable | Arbitrary `c : Compactification f` and `d : Compactification (u ≫ f)`. The structure contains the open immersion, proper map, and factorization equality. It implies separation and local finite type; Noetherian source schemes supply quasi-compactness, so no finite-type hypothesis is lost. Correct. |
| Their ordinary compact-support right adjoints | Arbitrary functors `F` and `G` with `adjF` and `adjG` to the actual fixed-compactification functors. Their existence follows from the recorded exceptional-adjoint node; ambient schemes are Noetherian because they are proper over S. Correct; no extra existence hypothesis or Brown choice is imposed. |
| Every unbounded K | The isomorphism is in a functor category on `DerivedCategoryModule A S`; the counit equation quantifies over every `K` in that category. No `Plus`, boundedness, or constructibility predicate occurs. Correct. |
| Natural isomorphism u* f^× K ≅ (fu)^× K | `e : F ⋙ (upperStar ... u).mapDerivedCategory ≅ G`. Its component at K is exactly the required objectwise isomorphism, with naturality included in `NatIso`. Correct order of functor composition. |
| Canonical, ordinary compact-support localization | The unique `e` satisfies the node's explicit adjoint-transpose equation for every normalized family `N`. Both left functors are `rightDerivedLowerShriekOfCompactification`; the equation uses both supplied adjunctions. Correct. |

I opened each statement dependency's record and the declarations it actually uses:
`Compactification` and `HasCompactification` in upstream `Compactification.Defs`,
the field-existence module `CompactifiableOverField`, `DerivedCategoryModule` in
upstream `Derived.Coefficients` and the project's `DerivedCategories`, Mathlib's
`Etale` class and finite-type/separated/Noetherian classes, upstream `EtaleMap`,
`EtaleExceptionalAdjoint`, `EtaleCompactSupportNormalization`, and
`EtaleCompactSupportComparisons`. The convention-only morphism-properties node
introduces no competing notion. In particular the field-existence theorem is not
being used as a definition for arbitrary compactifiable morphisms.

I checked the left comparison by following its three factors in the source:

1. Put `e = d.ofComp c`. Upstream `Compactification.Comp` constructs this by closure
   inside the product of the two compactifications. Its `restrict` is an actual
   compactification of u. No arbitrary auxiliary map is introduced.
2. `N.comparison u e.restrict` points from the compact-support candidate to sum
   extension. Inverting and whiskering it by the candidate for f gives
   `Du_Σ! ⋙ Rf_!^c ≅ Ru_!^(e.restrict) ⋙ Rf_!^c`.
3. `rightDerivedLowerShriekOfCompactificationCompIso A c e` then gives the
   candidate for the composite compactification `c.comp e`. Its source implements
   the proper/open exchange, open-extension composition, and direct-image
   composition in precisely this order. Finally
   `rightDerivedLowerShriekOfCompactificationIso A (c.comp e) d` changes to d
   through the canonical common refinement. Both interfaces are unbounded and
   require finite coefficients, which are supplied here.

Thus, writing this comparison as `c_M : Rf_! Du_Σ! M ≅ R(fu)_! M`, and
`L = u* (F K)`, the main equation is exactly

`R(fu)_!(e_K) ≫ ε^(fu)_K = c_L⁻¹ ≫ Rf_!(ε^u_(F K)) ≫ ε^f_K`.

This is the image of the identity under step 8's Hom bijections. In particular the
inverse on `c_L` is necessary and is present. The adjunction bijection makes this
equation determine each component of e uniquely. It also determines the unit by
transpose, so the natural isomorphism is normalized rather than merely nonempty.

The universal quantifier over `N` is sound: I read the structure's
`sheaf_normalization` and `derived_normalization`, not only its `comparison` field.
The first fixes the sheaf map inside the canonical inclusion into direct image,
and the second fixes its derived map on EVERY homotopy representative using the
total-right-derived unit. The inclusion is monic (extension-by-zero inclusion
followed by left-exact direct image), so these equations determine the comparison.
The localization is essentially surjective; hence this is also a determination on
all derived objects. The recorded `nonempty_etaleCompactSupportNormalization`
supplies a family for finite A. Consequently the quantifier neither hides an
assumption nor allows a twist by an arbitrary automorphism.

Edge cases: the zero ring and zero complex satisfy all binders; no `Nontrivial`
instance is requested. Empty schemes and the empty etale map remain allowed, with
zero sums and the same evaluation counit. Identity maps use the normalization's
identity clause. Multiple/disconnected sheets use the genuine sum functor, with
no selected sheet or nonempty-index requirement. All cohomological degrees,
including zero and arbitrarily negative degrees, are present. No characteristic,
torsion exponent, or invertible prime is added. Universes are explicitly bound by
`universe u`, `Scheme.{u}`, `A : Type (u + 1)` and `ModuleCat.{u + 1} A`, the same
size convention as the recorded category dependency; no additional equality of
object and morphism universes is imposed. The compiler runs with auto-implicit
variables disabled, and the source has no unbound variable.

Independent searches (2026-10-15):

- `msearch.py ... leanfinder "Etale extension by zero on unbounded derived
  categories adjoint to restriction and locality of exceptional pullback"`:
  eight generic derived-localization/essential-surjectivity hits; no locality
  statement.
- `msearch.py ... loogle "CategoryTheory.Adjunction.comp"`: twelve generic
  composition/counit/mate lemmas. They do not supply the specified geometric left
  comparison or this theorem.
- `msearch.py ... leansearch "Exceptional inverse image along a separated etale
  morphism equals ordinary inverse image on the full derived category"`:
  unavailable (Internal Server Error); no match verdict inferred from that failure.
- Independent `rg` searches in Mathlib, upstream `WeilConjectures`, and project
  `lean/Sheaf` used `exceptional.*restrict`, `restriction.*exceptional`,
  `derived.*shriek.*(upperstar|adjunction)`, `etaleAmbient`, and `adjointLocality`.
  The relevant existing etale sum adjunction is only
  `derivedEtaleLowerShriekUpperStarAdjunctionPlus` on bounded-below categories;
  open-immersion adjunctions and ringed-space restriction statements are special
  cases or different coefficient categories. I opened that `Plus` declaration
  in `SmoothBaseChange.HigherDirectImage.FreeSheaf` and the upstream
  `Derived.UpperShriek` declarations; neither states this full locality theorem.
  The source's generic `Adjunction.mapDerivedCategoryAdjunction` is reused by
  the definition, not reimplemented.

No remaining mathematical mismatch was found in the revised draft. I preserved
the Lean declarations and node record, and appended this independent reading only.
There are no new nodes or dependency modules in this delivery, and no statement
correction or citer audit is required. The sole new theorem remains `sorry`; both
definitions have real compositional data. The theorem docstring contains all
eight node proof steps, and every declaration has its source/blueprint docstring.

Validation: `scompile.py NE lem-amb-etale-adjoint-locality` compiled the delivered
module cleanly (4.3 seconds for the library check), without errors or warnings.
The stored `lean.statement` was checked verbatim against the theorem signature.
The prescribed delivery dry run and delivery are recorded below when completed.

The prescribed `deliver2.py NE lem-amb-etale-adjoint-locality --no-push` returned
`OK (dry run)`: preflight and compilation passed, with exactly the module, item
node, and report staged. Delivery uses the same wrapper and repeats these checks.
