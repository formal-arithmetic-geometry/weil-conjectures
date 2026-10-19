## Worker report

The module `Sheaf.Paper.SmoothPurityTowerInjectiveComponents` states every clause of
`det-sp-tower-injective-components`, using the recorded coefficient towers and exact
normalized evaluation. All theorem proofs are `sorry`. All definitions have real data.
No natural-language statement, proof, or proof-dependency field is changed.

The source read is the current main-20261015 blueprint:
`sec-smooth-purity/sk-lem-sp-tower-levels/sk-lem-sp-tower-levels-acyclic.md` and its
`.proof.md`. The existing DAG statement already corrects the blueprint's shorthand
“I_n computes Rg_* C_n” to the correctly typed “g_* I_n computes Rg_* C_n”. This
packet retains that correction verbatim. The definition and abelian-category nodes,
every statement dependency and its full published declaration/docstring were read.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Its ring of
  integers and ell-power ideals are the recorded `Padic.coefficientExtensionIntegers`
  and `spEllIdeal`, not a replacement ring or a chosen characteristic-zero algebra.
- The schemes are `T S : Scheme.{t}` and the completely arbitrary morphism is
  `g : T ⟶ S`. Their sites are the original `T.ProEt` and `S.ProEt`, with object
  universe `t+1`, morphism universe `t`. Coefficients and module sections live in
  `max u (t+1)`. There is no equality imposed between the site universes or between
  the site and coefficient universes. The published larger-coefficient sheafification
  transport is reused, as in `SmoothPurityCoefficientTowersAbelian`; the inherited
  high-priority small-coefficient instance is disabled during elaboration and restored
  at the end, with no change to importing modules' instance environment.
- The sheaves `R_(n+1)` are exactly `spCoefficientRing l E T n`. The constant-section
  maps of `Scheme.coefficientProEtaleDirectRingMap` are the structural maps adjoint
  to the canonical inverse-image coefficient identifications. `spTowerRingMapApp`
  uses those maps, and `spTowerRingMap_naturality` states their compatibility with
  both site restrictions and the recorded quotient reductions. No arbitrary
  coefficient identification is passed as an extra hypothesis.
- `Tow(T,O_E)` is the recorded `spCoefficientTowers l E T` (product-site module
  presheaves with the levelwise sheaf condition). The arguments `dT` and `dS` are
  witnesses of the published `SpCoefficientTowersAbelian` structure. They only
  expose its existing evaluation equivalence and exactness: the existing theorem
  `sp_coefficient_towers_abelian` supplies them for every allowed T and S. No new
  property of E, schemes, towers or maps is assumed. The statement is valid for
  every such sectionwise normalized witness.
- “I is an injective object” is `(I : spCoefficientTowers l E T) [Injective I]`
  in `sp_tower_injective_components`, using Mathlib's actual `Injective`.
- For each paper level r>=1, the Lean index is `r-1`; equivalently the bound
  variable `r : ℕ` in the statement denotes paper level `r+1`. The finite family
  `J : (n : Fin (r+1)) → systemLevel (spCoefficientCommRings l E T) n.val`
  ranges over precisely paper levels 1 through r+1. The conjunct
  `∀ n, Injective (J n)` gives injectivity over its own coefficient ring.
- The finite product has factors
  `(systemRestriction (spCoefficientCommRings l E T)
  (Nat.le_of_lt_succ n.isLt)).obj (J n)`.
  These are the existing restriction-of-scalars functors for the actual composite
  quotient maps R_(r+1) -> R_(n+1), including the identity case n=r.
  `Nonempty (Retract ((spCoefficientEvaluation ... r).obj I) (∏ᶜ ...))`
  gives actual module-sheaf maps whose composite is the identity, exactly a direct
  summand. No injectivity of a restricted J_n is claimed.
- Section acyclicity is the second conjunct, quantifying over every `U : T.ProEt`:
  `(SheafOfModules.evaluation (spCoefficientRing ... r) (op U)).rightAcyclic
  ((spCoefficientEvaluation ... r).obj I)`.
  The reused `rightAcyclic` means vanishing of all positive right-derived section
  functors, not acyclicity of an unspecified complex.
- Direct-image acyclicity is the third conjunct
  `(spLevelPush l E g r).rightAcyclic ((spCoefficientEvaluation ... r).obj I)`.
  `spLevelPush` abbreviates the published `coefficientProEtaleModuleDirectImage`
  for `ULift (O_E / (ell)^(r+1))`. Its values on sections are exactly
  `M(T ×_S V)` and its scalar action is through the canonical constant-section map.
  Thus this is ordinary uncompleted module direct image, not a different functor
  or a completion.
- `spTowerPush` defines the statement's g_(star,bullet) using the actual
  `PresheafOfModules.pushforward (spTowerRingMap ...)` and the full-subcategory
  inclusion. Both objects and maps, in both level and site variables, are given
  by that real construction. `spTowerPush_sheaf` supplies only the sheaf-condition
  proof. The original transitions are precomposed with base change and restricted
  through the specified coefficient maps; no transitions are chosen independently.
  `spTowerPush_properties` states additivity and left exactness, and the two
  proof-only instances expose these fields.
- `spTowerEvaluationIso` is selected from a unique-existence construction theorem,
  with each component explicitly required to be the identity on underlying sections
  (`HEq ... x`). This is a uniquely specified ordinary evaluation identity, not a
  choice of an unspecified natural isomorphism. Its bounded-below homotopy lift is
  the real `Functor.mapHomotopyCategoryPlusCompIso` construction in
  `spTowerEvaluationHomotopyIso`.
- The statement's total right-derived tower direct image on D+ is the recorded
  Mathlib construction `(spTowerPush ...).rightDerivedFunctorPlus`. The two tower
  and level enough-injectives instances are derived from the published
  Grothendieck theorems; `HasDerivedCategory.standard` supplies real localizations.
  There are no additional enough-injectives hypotheses on schemes or coefficients.
- A bounded-below injective resolution has
  `I : CochainComplex.Plus (spCoefficientTowers l E T)` and
  `hI : ∀ k : ℤ, Injective (I.obj.X k)`. Arbitrary integer lower bounds are retained.
  `sp_tower_injective_complex_computes` asserts invertibility of the finite-level
  derived unit on its evaluated complex, the acyclic-resolution computation.
- The source `C : DerivedCategory.Plus (spCoefficientTowers l E T)` and its specified
  injective resolution are explicit in `sp_tower_injective_resolution_computes`.
  Here `ρ : C ≅ Qh(quotient I)` is the image of the resolution quasi-isomorphism
  in D+; an arbitrary supplied resolution induces exactly such a ρ. The conclusion
  is an isomorphism from Q(g_* I_n) to Rg_*(C_n). Its equation is the finite-level
  derived unit followed by the evaluated derived unit and the derived image of
  `ρ.inv`. Thus it identifies the indicated complex for the given resolution,
  not merely an existentially selected resolution. The converse representation
  of a D+ resolution by a bounded-below complex is already the localization model.
- The notation C_n uses exact evaluation as specified in the abelian-tower node.
  `sp_tower_evaluation_derived_unit` states that its right-derived-plus unit is an
  isomorphism on every bounded-below complex. Thus the use of evaluation's
  `rightDerivedFunctorPlus` in the formulas is its canonical termwise D+ evaluation,
  including the same normalization, rather than an added derived operation.
- Finally `sp_tower_derived_direct_image_evaluation` supplies a unique natural
  isomorphism of functors
  `R(g_(star,bullet)) ⋙ evaluation_n ≅ evaluation_n ⋙ R(g_star,n)` on D+.
  Naturality is part of the natural-isomorphism type. The quantified equation on
  every `L : HomotopyCategory.Plus ...` requires agreement with both derived units
  and `spTowerEvaluationHomotopyIso`. It specifies exactly the comparison induced
  by the underived identity and guarantees resolution independence; it does not
  replace that comparison by an arbitrary isomorphism.

Dependencies used:

- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`,
  `spCoefficientRing`, `spCoefficientPresheaf`, `spCoefficientTowerSheafCondition`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `SpCoefficientTowersAbelian`, `sp_coefficient_towers_abelian`,
  `spCoefficientCommRings`, `spCoefficientEvaluation`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`.
  `InjectiveResolution` was also read in its recorded resolution module; a D+
  resolution of a complex here uses `CochainComplex.Plus`, rather than the
  N-indexed object-resolution structure.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`:
  `Functor.rightAcyclic`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded ordinary
  identified-coefficient interface is publicly imported, without duplicating it.
  Its coefficient-sized published extension
  `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses` supplies
  `Scheme.coefficientProEtaleDirectRingMap` and
  `Scheme.coefficientProEtaleModuleDirectImage`, which have the same sectionwise
  normalization and preserve the independent site/coefficient universes.
  The already landed node `def-weil-proetale-inverse-image` owns this ordinary
  inverse/direct-image construction and is added to `stmt_deps` (the permitted
  addition of a landed definition node). No dependency record is changed.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`: the existing `systemLevel` and
  `systemRestriction` for precisely the published coefficient ring tower.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus` and `rightDerivedFunctorPlusUnit`.
  Its entire recorded signature and unit docstring were read locally and confirmed
  with `scompile.py --source` against the current server source.

Proof-only imports retain the recorded stage-3 plan: the independent-universe
ringed-site Grothendieck theorem; Mathlib's Grothendieck enough-injectives theorem;
`WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`;
`Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`;
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`;
the ordinary right-derived functors and bounded-below K-injective construction.
`det-sp-tower-evaluation-adjoint` has no published Lean module to import, so its
future use remains explicitly named in the proof docstring. No prerequisite is
redefined for a proof that this stage is not proving.

All nine postponed statements belong to the item's coefficient direct-image
construction or its stated conclusions: `spTowerRingMap_naturality`,
`spTowerPush_sheaf`, `spTowerPush_properties`, `spTowerEvaluationIso_existsUnique`,
`sp_tower_injective_components`, `sp_tower_injective_complex_computes`,
`sp_tower_injective_resolution_computes`, `sp_tower_evaluation_derived_unit`, and
`sp_tower_derived_direct_image_evaluation`. Each has the item's blueprint tag,
source and a complete natural-language proof. The main proof reproduces all seven
steps of the DAG's argument across these declarations. No independent new notion
or new DAG node is needed.

Edge cases checked before and while writing:

- Lean level zero is paper level one; the product is `Fin 1`, never the empty
  product. Paper level zero is not smuggled into the coefficient system.
- The equal-index restriction is included by `n=r`; the coefficient tower's actual
  identity ring map is used. Larger levels are not asserted to survive the product.
- The zero injective tower and empty scheme are permitted. Zero J_n give the zero
  retract, and neither site-object nonemptiness nor nonempty schemes are assumed.
- Every morphism g, including identity maps and nonproper/nonquasicompact maps,
  is permitted. The constant-section structural map is used also for the identity.
- No scalar-restriction flatness is assumed (the quotient ring maps generally are
  not flat), and no assertion that restricted injectives remain injective occurs.
- All integer lower bounds are allowed, with no uniform bound across unrelated
  towers required. The complex is bounded below in the tower category, as stated.
- Finite products alone are used for the retract/section-acyclicity claim; no exactness
  of arbitrary products is added.
- Site object and morphism universes and the coefficient universe stay independent.
  No finiteness of the residue ring, ramification bound or extra topology on E is
  added beyond the existing finite Padic-extension data.

Searches (2026-10-18):

- `msearch.py ... leanfinder "Components of injective towers of sheaves of modules
  over varying quotient rings are acyclic for sections and direct image"`: eight
  generic hits concerning locally injective presheaves, module-sheaf abelianness,
  K-injective resolutions and vanishing for injective objects; none states this node.
- `msearch.py ... leansearch "An injective inverse system of module sheaves has
  components acyclic for direct image"`: eight hits including `InverseSystem.mk`,
  module-sheaf constructors and locally injective presheaves; no matching statement.
- `msearch.py ... loogle '"rightDerivedFunctorPlus"'`: twelve generic declarations,
  including the required total derived functor and unit; none supplies the
  varying-coefficient finite-product retract or the tower evaluation comparison.
- `msearch.py ... grep 'injective.*tower|tower.*injective|acyclic.*retract'
  CategoryTheory`: no Mathlib hits. Direct `rg` inspected the Mathlib definitions
  of injectivity, object resolutions, right-derived-plus functors, product-site
  module pushforward, sheaf evaluation and homotopy-category composition lifts.
- `rg`/`grep` of the upstream `WeilConjectures` tree for the exact node id and
  tower/injective names found no statement of the node. Searching `lean/Sheaf`
  found generic constant-ring strict-tower and abelian-group tower lemmas, not this
  varying-quotient-ring coefficient tower statement. The newly selected declaration
  names were checked against both source trees and have no collisions.

Validation uses only `scompile.py` for file-only compiles against the published
library, followed by the required `deliver2.py --no-push` and delivery wrapper.
No direct Git command, source-checkout edit, global build or forbidden local
preflight tool is run. The sandbox contains only this module, the item's node copy,
and this report. The independent review is the maintainer's review, as in the brief.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
