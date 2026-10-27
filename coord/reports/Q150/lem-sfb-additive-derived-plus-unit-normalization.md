## Worker report

The module `Sheaf.CategoryTheory.AdditiveDerivedPlusUnitNormalization` states
`CategoryTheory.Functor.additiveDerivedPlus_unit_normalization`, with one `sorry`
and no new definitions. The node is unchanged except for `lean`. No dependency
repair, new node, or statement correction was necessary.

Sources read: `literature/stacks-project/derived.tex`, labels
`lemma-enough-K-injectives-implies` (070K), `lemma-K-injective` (070I),
`lemma-bounded-below-injectives-K-injective` (070J), and
`lemma-injective-resolutions-exist` (013K). The node's eight proof steps are
included in the theorem docstring, including the unit calculation on arbitrary
bounded-below complexes, uniqueness, representative independence, and full
resolution naturality. The node is the source-based assembly of these results,
not a change of the blueprint unit.

Hypotheses and clauses, matched to Lean:

- Abelian categories A and B: the explicit object universes `uA`, `uB`, hom
  universes `vA`, `vB`, `Category` and `Abelian` instances. Ordinary derived
  localizations are the independent `HasDerivedCategory.{wA} A` and
  `HasDerivedCategory.{wB} B` instances; no universes are equated.
- Enough injectives in A: `[EnoughInjectives A]`.
- Every complex admits a quasi-isomorphism towards a K-injective complex: `h`,
  exactly `∀ K, ∃ I s, I.IsKInjective ∧ QuasiIso s`. No monomorphism is required.
  Mathlib's `IsKInjective` is explicitly the null-homotopy property in the node.
- F is additive: `(F : A ⥤ B) [F.Additive]`. There is no finite-limit,
  kernel-preservation or left-exactness assumption. The degreewise homotopy
  functor is `F.mapHomotopyCategory (ComplexShape.up ℤ)`.
- The total right derived pair is the recorded
  `F.rightDerivedFunctorOfQuasiIsoResolutions h` and its recorded unit. The first
  conjunct states its universal property, the bijection given by composing with
  the unit and whiskering by `DerivedCategory.Qh`. These actual functor and unit
  definitions already exist; their existence is not replaced by arbitrary data.
- For every K-injective I, the second conjunct supplies `hη : IsIso (η.app (π I))`.
  For every quasi-isomorphism `s : K ⟶ π I`, it asserts `IsIso (RF.map (Qh.map s) ≫
  η_I⁻¹)`. This is precisely the value isomorphism in the node. The target of this
  morphism is `(F.mapHomotopyCategory _ ⋙ Qh).obj (π I)`, namely Q(FI), with the
  localization identifications stated in the node understood.
- The full formula's representative independence and naturality are the
  following universally quantified equality. For another K-injective J,
  resolution t and *arbitrary derived morphism* u, every homotopy lift f satisfying
  `Qh.map s ≫ Qh.map f = u ≫ Qh.map t` satisfies
  `c_s ≫ Qh.map (F_K.map f) = RF.map u ≫ c_t`. Existence and uniqueness of such a
  lift follow from the imported K-injective Hom bijection. Setting u to identity
  compares any two representatives. This is step 8 of the node, in Lean's
  composition order. Its hη' quantifier ranges over all proofs of invertibility,
  so it introduces no proof-choice dependence.
- `(Rplus, α)` is *any* bounded-below right derived pair, not just a selected one:
  the binders have exactly the functor and unit types in the node, and
  `[Rplus.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)]` is its left
  Kan extension universal property. Mathlib's recorded `F.rightDerivedFunctorPlus`
  and `F.rightDerivedFunctorPlusUnit` supply such a pair with no extra hypotheses.
- The conclusion supplies the natural isomorphism
  `θ : DerivedCategory.Plus.ι ⋙ RF ≅ Rplus ⋙ DerivedCategory.Plus.ι`.
  The first clause states `η_K ≫ θ_(Q⁺K) = ι_B.map (α.app K)` for every
  `K : HomotopyCategory.Plus A`. The next clause quantifies over every other
  natural isomorphism satisfying *only* this equation and concludes `θ' = θ`.
- Preservation of D⁺ is explicitly the next clause:
  `(DerivedCategory.TStructure.t (C := B)).plus (RF.obj X.obj)` for every X in D⁺A.
- For every bounded-below degreewise injective J, rendered by
  `J : HomotopyCategory.Plus A` and `∀ n, Injective (J.obj.as.X n)`, both units
  are explicitly asserted invertible. The equality
  `θ_(Q⁺J) = η_J⁻¹ ≫ ι_B.map (α.app J)` is exactly the node's injective formula.
  The two invertible units identify both derived values with Q(FJ): their common
  source is Q(FJ), by the definitions of the degreewise functor, Qh and inclusions.
- For every bounded-below injective resolution s, rendered as
  `s : K ⟶ J` with `HomotopyCategory.Plus.quasiIso A s`, the statement supplies
  invertibility of `ι_B.map (Rplus.map (Q⁺.map s))` and gives
  `θ_(Q⁺K) = RF(Qs) ≫ η_J⁻¹ ≫ ι_B(α_J) ≫ ι_B(Rplus(Q⁺s))⁻¹`.
  This reverses the displayed mathematical composition into Lean's order.
- Independence from all injective representatives, including presentations of
  derived objects not already of the form Q⁺K, is explicit in the last clause:
  for *every* `q : X ≅ Q⁺J`, the same component is
  `RF(ι_A(q.hom)) ≫ η_J⁻¹ ≫ ι_B(α_J) ≫ ι_B(Rplus(q.inv))`.
  Since θ is a natural isomorphism on D⁺, its naturality includes every derived
  morphism, including ones not given initially by chain maps.

All resolution arrows in the formulas are homotopy classes. The homotopy
quotient is full and its quasi-isomorphism property pulls back to `QuasiIso` on
chain maps. Thus these quantifiers include every chain resolution and do not
require functorial choices of resolutions. `Q⁺ ⋙ ι_A` and `ι_K ⋙ Qh` are identified
by Mathlib's `DerivedCategory.Plus.QhCompιIsoιCompQh`; the same holds after F.
Explicit `@CategoryTheory.inv ... hη` terms make the inverse evidence visible
without local notation, local instances or hidden `let` binders.

Dependency declarations used (full signatures and docstrings read):

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Qh`, `DerivedCategory.Q`, `quotientCompQhIso`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` and
  `CategoryTheory.EnoughInjectives`, `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. Only its additive clause is used.
- `def-sfb-right-derived-functor`: the recorded functor, unit, universal property,
  inverse-unit theorem and object-value isomorphism in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
- `lem-weil-pbc-right-derived-plus-injective`: `rightDerivedFunctorPlus`,
  `rightDerivedFunctorPlusUnit` and their `IsRightDerivedFunctor` instance in
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`; its universal
  property is `CategoryTheory.Functor.IsRightDerivedFunctor` from
  `Mathlib.CategoryTheory.Functor.Derived.RightDerived`.
- `def-weil-pbc-bounded-derived-subcategories`: `DerivedCategory.Plus`,
  `DerivedCategory.Plus.ι` and `DerivedCategory.TStructure.t.plus`,
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- Proof dependencies are all available transitively through the two imports:
  `exists_rightDerived_of_enough_isKInjective` in
  `Sheaf.CategoryTheory.KInjectiveTotalDerived`;
  `CochainComplex.isKInjective_of_injective` in
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`;
  `DerivedCategory.Plus.exists_injective_nonempty_iso` and unit invertibility on
  injectives in `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`;
  `CochainComplex.IsKInjective.Qh_map_bijective` in
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective` and its bounded-below form
  in `Mathlib.Algebra.Homology.DerivedCategory.Plus`. The homotopy triangulation
  and exactness of Qh are imported by the derived-category infrastructure. No
  separate proof import is needed: none of these modules is absent from the
  transitive imports, and there is no import cycle.

Edge cases checked before writing: the zero functor and zero complex, identity
resolutions, arbitrary shifts (lower bound need not be zero), a bounded-below
complex whose units are not invertible, non-left-exact additive functors, and
arbitrary localization hom universes. Inverses of the units occur only at
K-injective or bounded-below degreewise injective objects. The unit equation at
an arbitrary bounded-below K does not invert η_K or α_K. The map s is never
assumed monic. An explicit second check tightened uniqueness to cover all
unit-normalized comparisons, and generalized the bounded-below pair from the
selected Mathlib pair to an arbitrary derived pair. No statement is disputed.

Searches actually run with the prescribed msearch wrapper (logged in searches.jsonl):

- LeanFinder: `Unit compatible natural isomorphism between full right derived functor
  and bounded below right derived functor of additive functor`. Eight hits, including
  `mapDerivedCategoryFactorsh`, `mapDerivedCategoryFactorsh_hom_app` and classical
  `rightDerivedZeroIsoSelf`; no exact theorem for the node's arbitrary additive F.
- Loogle: `"rightDerivedFunctorPlusCompatibility"`. Zero hits.
- Mathlib grep: `rightDerivedFunctorPlusCompatibility|rightDerivedUnique` in
  `Algebra/Homology`. Zero hits (rightDerivedUnique lives in CategoryTheory).
- Direct project rg for `rightDerivedFunctorPlusCompatibility`, `UnitNormalization`,
  and the node id in `lean/WeilConjectures` and `lean/Sheaf`. Read upstream
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
  its comparison assumes `HasKInjectiveResolutions`, whose replacements are monic,
  and uses the different `F.rightDerivedFunctor`. It does not directly state this
  node for arbitrary quasi-isomorphism replacements. Reusing that declaration
  would impose the unwanted stronger replacement interface. The recorded Sheaf
  pair already handles the exact h, and is reused rather than copied.
- Direct Mathlib reads/searches located `rightDerivedUnique`, the Plus inclusion,
  K-injective Hom bijections and bounded-below unit invertibility. These provide
  the ingredients, but none states the complete unit-normalized assembly.

Validation: the prescribed scompile.py compiled both the sandbox file and its
library module successfully, with no errors or unexpected warnings. The only
postponed proof is `additiveDerivedPlus_unit_normalization`.

## Second reading by Q150

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
