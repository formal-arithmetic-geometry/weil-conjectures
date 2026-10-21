## Worker report

The module `Sheaf.CategoryTheory.UnitPowerCompleteness` states
`CategoryTheory.unit_power_localDerivedComplete`, with `sorry` as its entire proof.
There are no new definitions, helper theorems, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- A small site is `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`;
  its commutative ring sheaf is `O : Sheaf J CommRingCat.{u}`. These are the standard
  small-site universes of the recorded localization, completion-unit and ideal-completeness
  interfaces. The module universe is `u`; derived morphisms have independently chosen
  universe `w`. The two `HasDerivedCategory` instances specify the derived localization
  on the site and on every slice. They impose no mathematical finiteness or exactness
  hypotheses, and the standard derived-category construction supplies them.
- The global sections are `a b unit : (O.obj ⋙ forget CommRingCat).sections`.
  `hu : ∀ U : Cᵒᵖ, IsUnit (unit.val U)` says that the last global section is invertible.
  This is equivalent to having an inverse global section: restriction preserves inverses,
  which are unique, so the local inverses form a compatible family. In particular it does
  not assume a nonzero ring or a terminal object of the site.
- The positive exponent is `e : ℕ` and `he : 1 ≤ e`. The equality of global sections is
  `hab : ∀ U : Cᵒᵖ, a.val U = unit.val U * b.val U ^ e`.
- The first conjunct quantifies over every `N : ringedSiteDerived O`, with no boundedness
  assumption, and states an iff between `IsLocallyDerivedRingedIdealComplete` for the two
  principal ideal sheaves.
- The ideal `(c)O` is represented by `image (ringedKoszulScalar O c)` with its actual
  inclusion `image.ι (ringedKoszulScalar O c)`. The scalar map is multiplication by `c` on
  the ring module. Categorical images in module sheaves sheafify the sectionwise image,
  so sections of this image are locally multiples of `c`; they need not admit a single
  coefficient on the object itself. No arbitrary ideal or extra ideal-generation premise
  has replaced the prescribed principal ideal. The definition of local completeness
  quantifies over every section of this image on every slice, applying the specified
  slice restriction and RHom from the sheafified sectionwise localization in degree zero.
- The second conjunct supplies an actual natural isomorphism `alpha` between
  `ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O a)` and its `b` counterpart.
  These are the recorded derived internal-Hom functors with first argument the actual
  complexes `[O → O[1/c]]` in degrees zero and one.
- Its displayed equation is the equality of the actual augmentation-induced units:
  `ringedCechCompletionUnit ... a ... N ≫ alpha.hom.app N =
  ringedCechCompletionUnit ... b ... N`. The augmentations are exactly
  `ringedLocalizationTwoTermAugmentation`, with degree-zero identity and zero elsewhere.
  The unit construction first uses the fixed evaluation-at-one map and then applies
  derived internal Hom contravariantly to this augmentation.
- The final conjunct quantifies over `c = a` or `c = b` and states both reflection clauses:
  the corresponding functor's output is locally derived `(c)`-complete for every `N`;
  and precomposition with its specified unit is a bijection of Hom sets into every
  locally complete target `L`. The clause is restricted to these two sections and does
  not silently strengthen the statement to every generator.
- There are no regularity, Noetherian, nonzerodivisor, exact-products, or nontriviality
  hypotheses. Every universe and variable is explicitly bound; no file-local notation,
  private definition, local instance, `let` binder or `show ... from` occurs in the statement.

Recorded dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent general-site specialization of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the recorded generic
  `CategoryTheory.derivedInternalHomOfUniverses` and its retained public import of
  `WeilConjectures.Algebra.Homology.DerivedInternalHom`. The completion and slice
  predicates use the retained `CategoryTheory.derivedInternalHom` interface on a small
  site; this is the original K-injective/localization construction, with the same
  signature and docstring, not a private or alternative internal Hom.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`: retained
  `CategoryTheory.ringedSectionLocalization` from `RingedSectionLocalization` and its
  independent-universe generalization. The existing two-term complex and local-complete
  predicate use the original small-site specialization, which sheafifies `Localization.Away`.
- `Sheaf.CategoryTheory.RingedExtendedCech`: `ringedSiteComplex`,
  `ringedSiteRingComplex`, `ringedLocalizationTwoTerm`, and
  `ringedLocalizationTwoTermAugmentation`; their full constructions, term identifications,
  and differential/augmentation descriptions were read.
- `Sheaf.CategoryTheory.RingedCompletionUnit`: `ringedCechCompletionFunctor`,
  `ringedCechCompletionUnit`, `ringedDerivedHomUnit`, and `ringedHomUnitEvaluationIso`.
- Added already-landed statement dependency
  `def-weil-pbc-locally-derived-ringed-ideal-complete`, using
  `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete` /
  `CategoryTheory.IsLocallyDerivedRingedIdealComplete` exactly, not a copied predicate.
- Added already-landed statement dependency `def-weil-pbc-ringed-koszul-system`, using
  `Sheaf.CategoryTheory.RingedKoszulSystem` / `CategoryTheory.ringedKoszulScalar`.
  This is the recorded canonical multiplication map, with real data, whose categorical
  image is the principal ideal. No Koszul-tower assumption enters the statement.
- Proof-only imports are the recorded modules
  `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`,
  `Sheaf.CategoryTheory.RingedCechKoszulDualLimit`, and
  `Sheaf.Paper.WeilCompletedTensorReflector`. The last publicly retains the generic
  `RingedKoszulCompletionReflector` theorem. Their existing proof plans provide the
  complete-elements ideal, unit-compatible Koszul comparison, and generic reflector.

Source checked: `literature/stacks-project/algebraization.tex`,
`lemma-ideal-of-elements-complete-wrt` (0998), `definition-derived-complete` (0999),
`lemma-derived-completion` (099B, including the displayed augmentation), and
`lemma-derived-completion-koszul` (0A0E). The unit-times-power argument is explicitly
expanded in the item's five proof steps; all five are rendered in the theorem docstring,
including both localization fraction formulas and the actual augmentation equality.

Edge cases checked mathematically before writing:

- `e = 1` includes multiplication by a unit; `e = 0` is deliberately excluded because
  it would allow `a` invertible with arbitrary `b`, and the completeness classes can differ.
- `b = 0` forces `a = 0`; both generated ideals are zero and all objects are complete.
  Localization at zero is the zero sheaf, as the recorded ideal theorem checks.
- A nilpotent `b`, zero divisors, and rings with torsion require no cancellation; the
  explicit inverse `u b^(e-1) a⁻¹` only uses `e ≥ 1`.
- If `b` is a unit, both ideals are the unit ideal, and the complete subcategory consists
  of zero objects. The localization complex is acyclic and both functors are zero.
- The zero ring, empty site and objects with empty covering sieves are allowed; there is
  no `Nontrivial`, `Nonempty`, or terminal-object assumption. The canonical image uses
  sheafification, so it also handles coefficients available only locally.

Searches actually run with `msearch.py NG lem-pur-unit-power-completeness`:

- LeanFinder: `local derived completeness for a sheaf of rings unchanged under a unit times
  a positive power and natural isomorphism of completion functors`. Eight hits: perfectoid
  BDeRham, module generators/quasicoherence and ordinary adic completion; no exact theorem.
- Loogle: `IsLocalization.Away, IsDerivedComplete`. Zero hits; diagnostic says unknown
  identifier `IsDerivedComplete`. This provides no candidate for the desired theorem.
- Mathlib grep: `unit.*power|power.*complete|IsDerivedComplete|LocallyDerivedComplete`
  in `RingTheory`. Twenty-five hits about ordinary units, power series, valuations and
  ordinary adic completion; none states the local ringed-site derived comparison.
- Source/project ripgrep: `unit.power|UnitPower|unitPower|Local.*Complete|locally.*Complete|
  ringed.*Complete` over `lean/WeilConjectures` and `lean/Sheaf` located the existing
  completeness and completion infrastructure used here. Searches for the exact item id
  and `UnitPower|unit_power|unitPower` found no exact theorem (only unrelated tensor-unit
  powers and Popescu denominator arguments upstream).
- Name collision check: `UnitPowerCompleteness|unit_power_localDerivedComplete` over
  Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hits.

No STATEMENT-DISPUTED issue or node correction was found. Only `lean` and the two
already-landed statement-dependency additions change in the node copy.

## Second reading by NG

This is the worker's final rereading, not an independent-agent review: the dispatcher's
brief expressly forbids starting other agents and assigns independent review to the
maintainer. Reread the node's complete statement and the Lean signature side by side.
All mathematical hypotheses are the small site, commutative ring sheaf, compatible global
sections, pointwise invertible `unit`, positive exponent, and pointwise equality `hab`.
The first conjunct uses all local sections of the sheaf-theoretic image ideal. The second
quantifies over a natural isomorphism and compares the actual units, rather than arbitrary
maps into isomorphic objects. The third includes both output-completeness and the complete
universal mapping property for each of the two functors. In particular, the principal ideal
was represented canonically by an image to avoid an unnecessary chosen ideal/presentation
hypothesis, and the reflector clauses were included explicitly. No mismatch remains in this
rereading. The maintainer's independent delivery review remains separate.

Validation: `scompile.py NG lem-pur-unit-power-completeness` compiled the delivered file
cleanly as both a sandbox and its library module. `deliver2.py ... --no-push` returned
`OK (dry run): commit 60b60d8f593 passes the preflight and compiles; nothing pushed`.
The file has no line exceeding 100 characters, and `lean.statement` is the verbatim
signature. Only the theorem proof is postponed with `sorry`.
