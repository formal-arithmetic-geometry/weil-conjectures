## Worker report

The new module `Sheaf.CategoryTheory.RationalizationLocalizationHomCriterion` states
`CategoryTheory.Rationalization.localization_hom_criterion`. It has one theorem, with
`sorry` as its entire proof; it defines no notions or maps. The item's only changed field
is `lean`. No dependency repairs, new nodes, or statement correction are required.

Source read: the complete main-20261015 blueprint file
`sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md`,
in particular its morphism-fraction argument, full-faithfulness argument, and final
localization conclusion. The DAG extracts the generic scalar-fraction assembly from
that coefficient specialization. All nine steps of the node's proof are reproduced in
the theorem's proof-plan docstring, including conjugation by the factorization isomorphism,
the three denominators in the injectivity argument, transport to arbitrary objects,
and the functor-category universal property.

Hypotheses and conclusions, matched clause by clause:

- A commutative ring is `{R : Type w} [CommRing R]`.
- The R-linear category C is `{C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [Linear R C]`. Its triangulated structure is `[HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]`.
  These are precisely the dependency's Mathlib encoding of the triangulated axioms;
  finite biproducts follow from that encoding. R-linear integer shifts are the additional
  binder `[∀ n : ℤ, (shiftFunctor C n).Linear R]`.
- The submonoid is `(M : Submonoid R)`. The canonical rationalization and quotient functor
  are the recorded upstream `Rationalization M C` and `Q M C`. The class W_M is exactly
  the upstream `W M C`, defined by the torsion-cone condition; no substitute class is used.
- The target is `{D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]`.
  It has no zero-object, shift, pretriangulated, or triangulated binder.
- The additive R-linear functor is `(F : C ⥤ D) [F.Additive] [F.Linear R]`.
- Essential surjectivity is `[F.EssSurj]`.
- Inversion is `(hInv : (W M C).IsInvertedBy F)`.
- Target scalar invertibility is
  `(hUnits : ∀ m ∈ M, ∀ Y : D, IsIso (m • 𝟙 Y))`.
- Hypothesis (i), for all objects and all arrows, is
  `(hSurj : ∀ (A B : C) (h : F.obj A ⟶ F.obj B),
    ∃ m ∈ M, ∃ u : A ⟶ B, m • h = F.map u)`.
- Hypothesis (ii) is
  `(hEq : ∀ (A B : C) (u v : A ⟶ B), F.map u = F.map v →
    ∃ n ∈ M, n • u = n • v)`.
- The induced G is the actual `Localization.lift F hInv (Q M C)`. Mathlib's
  `Localization.fac` supplies `Q M C ⋙ G ≅ F`; the statement needs no extra factorization
  hypothesis or arbitrary map. Full faithfulness and essential surjectivity are its
  `.Full ∧ .Faithful ∧ .EssSurj`, the first three conjuncts.
- The last conjunct, `F.IsLocalization (W M C)`, is the localization universal property
  used by the recorded dependency. Mathlib's predicate identifies the target with the
  constructed localization and supplies the equivalence on functor categories for every
  category E (`Localization.functorEquivalence`), as well as inversion. It is not merely
  a fraction-surjectivity property.
- All five universes are explicitly declared; the ring, source and target object and
  morphism universes are independent. Every variable is bound explicitly.

Dependency declarations read and used:

- `def-weil-linear-category`: `CategoryTheory.Linear`,
  `Mathlib.CategoryTheory.Linear.Basic`, including its Hom modules and bilinearity fields.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated`,
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, and
  `CategoryTheory.IsTriangulated`, `Mathlib.CategoryTheory.Triangulated.Triangulated`.
  The recorded exact-functor signature `Functor.IsTriangulated` and its additive instance
  in `Mathlib.CategoryTheory.Triangulated.Functor` were also read; F does not assume them.
- `def-weil-linear-functor`: `CategoryTheory.Functor.Linear`,
  `Mathlib.CategoryTheory.Linear.LinearFunctor`, together with `Functor.Additive`.
- `sk-def-sfb-rationalization`: `CategoryTheory.Rationalization`, its `torsion`, `W`, `Q`,
  triangulated-torsion instance, `W_smul_id`, `isIso_smul_id`, `linear`, and
  `algebraMap_smul`, from
  `WeilConjectures.CategoryTheory.DerivedCategory.Rationalization`. The whole source was read.
- `lem-weil-pbc-localization-universal-property`: `Localization.lift`, `fac`, `Lifting`,
  `liftNatTrans`, `liftNatTrans_app`, `comp_liftNatTrans`, `liftNatIso`, `natTrans_ext`,
  `fullyFaithfulWhiskeringLeft`, `essSurj`, and `Functor.IsLocalization`,
  from `Mathlib.CategoryTheory.Localization.Predicate`.
- Proof dependencies `lem-sfb-additive-localization-linear` and
  `lem-sfb-linear-localization-descent`: `Localization.linear`, `functor_linear`, and
  `functor_linear_iff` in `Mathlib.CategoryTheory.Localization.Linear`, with inversion
  and essential surjectivity from Predicate. Their full displayed signatures were read.
- Proof dependency `lem-sfb-rationalization-scalar-fractions`:
  `Rationalization.exists_smul_eq_map` and `map_eq_map_iff`,
  `WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap`; both signatures,
  their common context, and docstrings were read. This is a proof-only import.
- Proof dependency `lem-trf-fully-faithful-ess-surj-equivalence`: `Functor.asEquivalence`
  and the `Functor.IsEquivalence` fields in `Mathlib.CategoryTheory.Equivalence`;
  this is a proof-only import. All statement dependencies are public imports directly
  or through the canonical Rationalization module. No stale Complete.Rationalization
  module or duplicate Sheaf rationalization is imported.

Edge cases checked mathematically before writing: M = {1} gives the usual fully faithful,
essentially surjective equivalence criterion; no assumption excluding this case appears.
If 0 belongs to M, target scalar invertibility makes every target object a zero object,
and the rationalization likewise collapses; the hypotheses and conclusion remain valid.
The zero ring and zero source category are included. The source cannot be empty because
it is triangulated and has a zero object, exactly as the node assumes. An empty target
cannot receive a functor from that source. No extra nonemptiness, nontriviality, nonzero
scalar, invertibility-in-R, or size equality is imposed. With R = ℤ and M the powers of
ℓ, the statement specializes to the source's intended application. The supplied
`hUnits` is retained even though it can follow from the inversion and linearity assumptions:
it is explicitly present in the node.

Searches actually run using msearch.py, with group Q10 and this item's id:

- LeanFinder query: `An essentially surjective R linear functor is a rationalization
  localization when morphisms lift after scalar multiplication and equalities are
  detected after scalar multiplication`. Eight hits: `Localization.functor_linear_iff`,
  `Localization.instLinearLocalizationQ`, `Localization.linear`,
  `Functor.linear_of_full_essSurj_comp`, `Localization.instLinearLocalization'Q'`,
  `Functor.linear_comp_iff_of_full_of_essSurj`, `Localization.instLinearLocalization'`,
  and `Localization.functor_linear`. These give linearity ingredients, not the criterion.
- Loogle query: `"IsLocalization", "IsEquivalence"`. Three hits:
  `Functor.IsLocalization.isEquivalence`, `Functor.IsLocalization.instCompOfIsEquivalence`,
  and `Functor.IsLocalization.of_isEquivalence`; none has the scalar-fraction hypotheses
  and comparison conclusion.
- Mathlib grep query: `exists_smul_eq_map|homBijective|localization_of_hom`, subdirectory
  `CategoryTheory`. The wrapper returned zero hits.
- Direct `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `exists_smul_eq_map|homBijective|localization_of_hom|lem-sfb-rationalization-localization-hom-criterion`.
  This found the recorded scalar-fraction declarations, RationalizationLift's
  `homBijective_lift_obj`, and the private `rationalization_localization_of_hom` in
  `Sheaf/UpstreamExtra/WeilConjectures/CategoryTheory/ModuleObjects/EllAdicRationalization.lean`.
  The latter's signature and full proof were read: it has the same generic hypotheses
  but concludes only `F.IsLocalization`, and is private; it cannot be attached as a public
  declaration asserting all the node's conclusions. Its proof already performs the same
  generic Hom comparison. `homBijective_lift_obj` requires a triangulated target and an
  auxiliary coefficient-localization setup and only treats selected source image objects,
  so it also does not state the item. No existing complete public match was found.
- Direct `rg -n` for the item id in `lean/WeilConjectures` returned no hits.
- Direct `rg -n` for `rationalization_localization_hom_criterion|localization_hom_criterion`
  in Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json` returned no hits.

No statement fault or dispute was found. No theorem was proved. Validation:
`scompile.py Q10 lem-sfb-rationalization-localization-hom-criterion` on the delivered module
compiled both the sandbox check and library module successfully, with no warnings or errors
(1.6 seconds each). The node's `lean.statement` was extracted verbatim from the source
signature; all Lean lines are at most 100 characters.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
