## Worker report

The module `Sheaf.Paper.PrimePowerTraitResidueModel` states the prime-power trait residue model for coefficients `ZMod (ell ^ n)`. It reuses the landed completed tame group algebra and its canonical action, and states the tame character and wild invariant stalk data, the exact three-term residue row, the Tate line and its character formula, the generator-normalized residue cochain with unique natural homotopies, the derived supported-section comparison, and the generic-factor comparison. The main statement is `AlgebraicGeometry.Etale.exists_primePowerTraitResidueModel`; its proof is `sorry` as required for stage 2. The coefficient-annihilation theorem is also named and remains `sorry`.

The hypotheses of the node are rendered as follows: `ell n : ℕ` with `[Fact ell.Prime]` and `hn : 1 ≤ n`; `R` has `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsStrictlyHenselianLocalRing R]` and `(hell : IsUnit (ell : R))`; `K Ks Ω : Type u` carry the field, fraction-field, separable-closure, scalar-tower and algebraic-closure assumptions; `Ωs` is an algebraically closed residue-point field; and `s` is the specified geometric closed point with `hs` identifying its image with `closedPoint R`. No additional hypothesis occurs in the main theorem.

The first conclusion clause is the existential tuple `(hqp, t, D, N, F, av, T, c, E)`. `hqp` records positivity and coprimality of `ell ^ n` with `ringExpChar (IsLocalRing.ResidueField R)`; `t` is the canonical tame character; `D` is `TraitPrimePowerStalkData`; `N` is `TraitPrimePowerWildData`, identifying the descended tame representation and its published completed action with the actual wild invariants; `F` is the row complex; `av` is the normalized wild averaging projector; `T` is the Tate line with its annihilation equation; `c` is the generator-normalized residue cochain; and `E` is the derived supported-section model. The completed algebra, augmentation ideal and group elements are exactly `Rep.CompletedAugmentation.Algebra`, `.Ideal`, and `.groupElement`, imported through `Sheaf.Paper.TraitResidueModel`. Its canonical `.action` is used verbatim in `N.completed_action`. There is no existential algebra `B`. The remaining structures state stalk specialization, the exact row, Tate coordinates, generator formulas, totalization, and the derived comparison clauses from the node.

The final clause is the natural transformation `sp` from the derived generic stalk to supported sections followed by tensor with the actual Tate line and shift by `2`. Its universal equation is quantified over every generator `σ` and every bounded-below complex `L`; `traitResidueGenericFactors` gives the representative-to-derived comparison, `c.positiveResidue` gives the termwise residue map, `E.factors` and `E.comparison` give the canonical supported comparison, and `leftDerivedFunctorIsoMapDerivedCategory` supplies the derived tensor transport. The cochain and totalization equations in `TraitResidueCochain` express generator independence by a `Homotopy` that is both nonempty and subsingleton, hence the resulting map is independent of the generator and representative. `traitResidueUniformizer` is a real noncomputable choice from Mathlib's `IsDiscreteValuationRing.exists_irreducible`, used only to present the generic open complement; no proposition is used as definition data.

Dependencies used are: `WeilConjectures.Mathlib.RingTheory.Henselian.IsStrictlyHenselianLocalRing`; Mathlib `IsDiscreteValuationRing`; Mathlib `IsAlgClosed` and `Scheme.SpecToEquivOfField`; `Sheaf.AlgebraicGeometry.EtaleSupportedSections` (`supportedEtaleSections`, `supportedEtaleSectionsι`, `derivedSupportedEtaleSections`); `WeilConjectures.AlgebraicGeometry.DerivedCategories` (`DerivedCategory`, `DerivedCategory.Plus`); `WeilConjectures.SixFunctors.Etale.Derived.Tensor` (`derivedTensor`, `tensorRight` and derived-tensor comparison); `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf` (`finiteEtaleTateSheaf`, `finiteEtaleTateOneGenerator`); and `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback` (import retained for instance availability and the stated proof dependency; `etaleFiniteTwistPullback` and its structured data are not directly referenced by this module). The gluing and tame-character interfaces used by the auxiliary records are the published `Sheaf.AlgebraicGeometry.TraitSheafGluing` and `Sheaf.FieldTheory.CanonicalTraitTameCharacter` declarations.

Edge cases checked were `p = 1` (the wild kernel is trivial), `d = 1`, constant and closed-supported sheaves, `j_!V`, the zero object, `ell = 2` with `n = 2` (so the norm calculation uses `ell^n = 4`), and arbitrary generator changes. The finite quotient formula uses `ell^n N_d = 0` and the averaging denominators are units because `ell` is invertible in the trait. The Tate line is free of rank one over `ZMod (ell^n)`, so ordinary tensor agrees with the derived tensor used in the final clause.

Existing-declaration searches were performed before writing: `msearch.py` LeanFinder, Loogle, LeanSearch and grep queries for prime-power trait residue models, tame/wild inertia, augmentation ideals, supported etale cohomology, and generator-independent residue maps; `rg` over `WeilConjectures/` and `lean/Sheaf`; and DAG searches for the item and candidate notions. The searches returned only unrelated augmentation ideals, local cohomology, perfectoid constructions, and finite Tate-sheaf interfaces; no declaration states the full prime-power trait residue model. The repair additionally read the landed `Sheaf.RepresentationTheory.CompletedAugmentationAlgebra` and `Sheaf.Paper.TraitResidueModel` in full, including the declarations and docstrings of `Algebra`, `Ideal`, `groupElement`, `action`, `traitIsGenerator`, `TraitSheaves`, and the sibling stalk record. Those notions are reused wherever their interfaces apply; the sibling stalk record requires a field coefficient ring and its fixed fraction-field/geometric-point presentation, so the prime-power stalk record retains its original general commutative coefficient interface under a distinct name. The retained search log is `searches.jsonl`.

No statement correction was made, no dependency module or new definition node was needed, and no `STATEMENT-DISPUTED` condition was found.

## Second reading by NJ

I reread the item JSON, its source place (ILO XVII 1.2.1--1.2.3), and the complete module. Every node hypothesis is bound explicitly in the theorem. The completed algebra, ideal and action now come from `Rep.CompletedAugmentation`, rather than a second inverse-limit model. The generator subtype uses the sibling predicate `traitIsGenerator`; its closure-of-powers condition is precisely the original dense-range condition. The tame quotient, wild invariants, exact three-term row, Tate twist, averaging, totalization, derived supported comparison, generator homotopy, and final natural transformation each occur in the corresponding structure field or quantified clause. The main theorem does not add a uniformizer hypothesis: the chosen uniformizer is internal data obtained from the Mathlib DVR existence theorem. The final equation is quantified over all topological generators and all bounded-below complexes, and the module has no remaining compiler warnings or lines over 100 characters. The repair changes the interfaces identified by the return, and preserves every mathematical hypothesis and conclusion of the pinned statement.

## Repair of return 29501644879f

H4: removed `TraitCompletedAlgebra`, `traitResidueIdeal`, `TraitGenerator`,
`traitCharacteristicExponent`, and the duplicate tame-limit topology instance. The main
existential no longer contains `B`. `traitResidueHom` uses the actual published algebra,
ideal, and scalar map. `TraitResidueCochain.generatorIdeal` has source that actual algebra
and target that actual ideal; its formula uses the actual published group element.
`TraitPrimePowerWildData` records descent to a discrete tame representation and a
module-category realization: `completed_action` identifies its scalar action with
`Rep.CompletedAugmentation.action`, transported through the displayed underlying-module
isomorphisms. It supplies no alternative definition of completed action. Its topology and
finite-coefficient class fields are conclusions already supplied by the profinite tame
group and the finite coefficient ring, not new assumptions on the main theorem.
`TraitSheaves` is also reused instead of repeating the sheaf-category abbreviation.

H9: `TraitResidueStalkData` was renamed to `TraitPrimePowerStalkData`; the other colliding
names were removed, not renamed. The module now publicly imports
`Sheaf.Paper.TraitResidueModel`, so its successful compile checks coexistence with the
sibling's entire interface, including generated structure declarations. The sibling's
field-coefficient stalk bundle cannot be applied to `ZMod (ell^n)` for general n.

H10 advisory: enabled `genInjectivity false`, `genSizeOfSpec false`, and
`linter.all false`, as suggested by the return, to avoid unused generated dependent-bundle
lemmas and their linting. The required `scompile.py` checks of the repaired module both
passed without diagnostics: sandbox 30.8 s, library 31.2 s. The report's erroneous claim
that `etaleFiniteTwistPullback` itself is used was corrected above.

Additional clause check after the interface repair:

- The profinite tame quotient, root-family normalization, pro-p kernel, characteristic-zero
  case, and generator existence are `TraitResidueTameCharacter.character`,
  `continuous_character`, `surjective_character`, `roots_exist`, `root_formula`, `pro_p`,
  `char_zero`, and `generator`; p is Mathlib's `ringExpChar` of the closed residue field.
- The real generic and closed stalks, their Galois action, specialization and invariant
  image are `TraitPrimePowerStalkData.genericIso`, `action_germ`, `specialization`,
  `specialization_germ`, and `invariant`. The actual invariant submodule is the published
  restriction-and-invariants composite `traitResidueWild`.
- The tame action on that submodule is pinned by `TraitPrimePowerWildData.descent` and
  `tameUnderlying`; its completed action is pinned by `completed_action` to the landed
  canonical action, on every algebra element and every vector.
- The row's three degrees and arrows are `TraitResidueRow.closed`, `wild`, `hom`,
  `outside`, `first_differential`, and `last_differential`; exactness is `additive`,
  `exact_limits`, and `exact_colimits`. `quasi_isomorphisms` and `bounded_below` express
  preservation of quasi-isomorphisms and bounded-below complexes.
- `TraitResidueTotal.coproduct`, `differential`, and `map_inclusion` specify direct-sum
  totalization, the sign, and its functorial map. `TraitResidueDerived.comparison`,
  `augmentation_formula`, and `comparison_normalization` identify it with supported
  cohomology, using the canonical right-derived unit.
- `TraitResidueAverage.fixes` and `finite_formula` give the normalized averaging projector
  on every finite wild quotient fixing the vector.
- `TraitResidueTate.stalk`, `roots`, `germ`, `coordinate_formula`, `characters`, and
  `character_formula` specify the actual Tate stalk and non-equivariant continuous Hom;
  `free_rank_one` and `twist_limits` ensure exact tensor with that line.
- `TraitResidueCochain.generatorIdeal_formula` specifies multiplication by 1-sigma.
  `residue_formula` specifies evaluation at sigma, averaging, and inverse evaluation at
  1-sigma. `unique_natural_homotopy` quantifies over homotopies in the functor category.
  `totalResidue_formula`, `evaluation_formula`, and `positiveResidue_formula` specify
  totalization and untwisting. `TraitResidueDerived.negativeResidue_normalization` and
  the final universal equation for `sp` identify the descended map for every generator
  and every bounded-below representative, giving independence of both choices.

Rechecked edge cases after the repair: p=1 uses the same `ringExpChar` convention;
normal versus arbitrary open subgroups give the same indexing for the commutative tame
group; the coefficient ring is finite also for ell=2, n=2; the main theorem still covers
every n>=1 and keeps the original closed geometric point and field-tower binders.
The node's statement and all its non-Lean fields are unchanged from the current shared
DAG. No statement correction, dependency repair module, new node, or new postponed theorem
is introduced. Both existing named theorem proofs remain `sorry` for stage 2.
