## Worker report

This repair removes the duplicate predicate introduced by the earlier packet. The
item now imports the already landed Q03 module
`Sheaf.AlgebraicGeometry.PunctualPurity` and states the theorem with its exact
`AlgebraicGeometry.Etale.IsPunctuallyPureAt` and `IsPunctuallyPure` declarations.
The deleted `PunctualCohomologicalPurity.lean` module and its
`def-per-punctual-cohomological-purity` node are not part of this delivery. The
item's statement, source, proof plan, and all fields other than `stmt_deps` and
`lean` are unchanged from the supplied node.

### Statement rendering

The theorem is
`AlgebraicGeometry.Etale.punctual_cohomological_purity_etale_locality` in
`lean/Sheaf/AlgebraicGeometry/PunctualPurityEtaleLocality.lean`.

- `(ℓ : ℕ) (hℓ : ℓ.Prime)` is the fixed prime and its primality proof.
- The first conjunct universally binds schemes `X Y : Scheme.{u}` and their
  `[IsNoetherian X] [IsNoetherian Y]` instances, then assumes
  `IsRegularScheme X` and `IsRegularScheme Y`.
- It binds `f : Y ⟶ X` with `[Etale f]`, and assumes
  `IsUnit (ℓ : Γ(X, ⊤))` and `IsUnit (ℓ : Γ(Y, ⊤))`.
- For every `y : Y`, the first conclusion is exactly
  `IsPunctuallyPureAt ℓ hℓ Y y ↔ IsPunctuallyPureAt ℓ hℓ X (f y)`; the point on
  `X` is the image `f y`.
- The second conjunct universally binds `X : Scheme.{u}` with
  `[IsNoetherian X]`, assumes `IsRegularScheme X` and
  `IsUnit (ℓ : Γ(X, ⊤))`, then binds an arbitrary index universe
  `I : Type v` and family `Y : I → Scheme.{u}` with
  `[∀ a : I, IsNoetherian (Y a)]` and assumes
  `(∀ a : I, IsRegularScheme (Y a))`.
- It binds `f : ∀ a : I, Y a ⟶ X` with `[∀ a : I, Etale (f a)]` and assumes
  joint surjectivity in the literal form
  `∀ x : X, ∃ (a : I) (y : Y a), f a y = x`.
- Its conclusion is exactly
  `IsPunctuallyPure ℓ hℓ X ↔ ∀ a : I, IsPunctuallyPure ℓ hℓ (Y a)`.

The imported Q03 definitions supply the canonical level-one coefficient class,
closed-support map, and the pointwise/every-point predicates. In particular,
`IsPunctuallyPureAt` is the existential finite-dimension, regular closed-point,
unit, and `IsIso` clause from the recorded dependency; this theorem adds no
replacement predicate or extra hypothesis.

### Dependency declarations

The statement uses these recorded interfaces:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme`;
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and the derived-category
  conventions exported there;
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`,
  `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`;
- `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`,
  `AlgebraicGeometry.Etale.regular_immersion_class_calculus` and its published
  `regularClassCoefficients`/`regularClassTwist` family;
- Mathlib `AlgebraicGeometry.Scheme.residueField`, `AlgebraicGeometry.Spec`
  and `AlgebraicGeometry.Spec.map`, `ringKrullDim`, and the `Etale` class;
- `Sheaf.AlgebraicGeometry.PunctualPurity`,
  `AlgebraicGeometry.Etale.IsPunctuallyPureAt` and
  `AlgebraicGeometry.Etale.IsPunctuallyPure` (the repaired dependency replacing
  the duplicate definition).

The remaining imports in the theorem module are the recorded proof-dependency
interfaces for strict henselization, etale base change, exact inverse image,
and geometric stalk conservativity; they are not added statement dependencies.

### Edge cases and searches

The statement keeps the empty scheme and empty indexing family (both are
vacuous where appropriate), dimension zero, nontrivial residue extensions,
non-surjective individual etale maps, and an independent index universe `v`.
No excellence, finite-type, or extra invertibility hypothesis is introduced.
The pointwise clause uses `f y`, and the cover clause uses literal joint
surjectivity, so neither silently changes the source statement.

The earlier packet's searches were rechecked with `msearch.py` (`leanfinder`
for punctual purity and etale locality, `loogle` for `costalk`, `grep` for
`punctual.*pur|PunctualPur|costalk`, and `rg` over the project and Mathlib).
They found no second punctual-purity predicate in Mathlib or the project. The
recheck found the landed Q03 declaration in
`lean/Sheaf/AlgebraicGeometry/PunctualPurity.lean`, which is the same ILO XVI
3.2.1--3.2.2 notion and therefore is used here. The old duplicate node and
module have been removed as required by the return review.

No `STATEMENT-DISPUTED` marker or node fault remains. The theorem proof remains
`sorry` as required for stage 2.

### Validation

`scompile.py` compiled
`lean/Sheaf/AlgebraicGeometry/PunctualPurityEtaleLocality.lean` cleanly against
the live library (no errors or warnings). The node's `lean.statement` is the
verbatim theorem signature from that file, with `by: Q30` and date `2026-10-19`.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
