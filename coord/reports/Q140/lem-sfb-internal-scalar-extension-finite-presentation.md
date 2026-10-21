## Worker report

Existing match: `AlgebraicGeometry.ProEtale.fp_extend` in
`Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`, lines 102–107.
No module or new definition is delivered. Only the item's `lean` field changes.
The current source was read locally and confirmed using
`scompile.py --source Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`.
The signature was extracted with `tools/stage2_delivery.py signature`.

Source read: the node's six proof steps and
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/` +
`sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-subfield-constructible.proof.md`,
second sentence. This sentence tensors the finite presentation on each stratum.
The item's formulation isolates the corresponding global internal-module assertion.

Hypothesis and conclusion correspondence:

- Any scheme X: the lemma's implicit `{X : Scheme.{u}}`, with arbitrary universe `u`.
  There is no finiteness, separation, nonemptiness, or characteristic assumption.
- The category C is precisely `Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}`.
  The site keeps its object universe `u + 1` and morphism universe `u`.
  The sheaf monoidal instance is sheafified objectwise tensor over the integers,
  supplied by the upstream Grothendieck-abelian monoidal framework and
  `WeilConjectures.CategoryTheory.RingObjects.Ab`. It is the same localized
  `Sheaf.monoidalCategory` used by the recorded `sfbSheafTensorStructure`.
- R and S are the section parameters
  `(R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [MonObj S]`.
  Commutativity of R is `[IsCommMonObj R]`. The existing lemma explicitly has
  `omit [IsCommMonObj S] in`; applying it to the node's commutative S is immediate.
  This is an existing theorem with fewer assumptions and identical conclusion,
  permitted by coord/STATE.md's 2026-10-11 14:36 UTC ruling. No node correction is needed.
- A ring-object morphism is `(φ : R ⟶ S) [IsMonHom φ]`, expressing preservation
  of both multiplication and unit.
- An R-module object is
  `{M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}`.
- The finite-presentation hypothesis is `(h : Mod.IsFinitelyPresented R M)`.
  Reading `WeilConjectures.CategoryTheory.ModuleObjects.Free` shows it is exactly
  `∃ (n m : ℕ) (f : finiteFree R m ⟶ finiteFree R n), Nonempty (M ≅ cokernel f)`.
  Here `finiteFree R n` is the biproduct of `Fin n` copies of `Mod.regular R`.
- The conclusion is exactly
  `Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M)`.
  `extendScalars` is the recorded internal balanced tensor functor, with S acting
  on the first factor, not the ordinary ModuleCat scalar extension.
- No flatness hypothesis is required: neither `PreservesFiniteLimits` nor an
  exactness or flatness assumption occurs in `fp_extend`. The finite-limit
  hypothesis of the later theorem `boundedConstructible_leftDerivedExtendScalars_obj`
  occurs after this lemma and does not enter its section parameters.

Dependency declarations read and used:

- `sk-def-sfb-sheaf-tensor`: `CategoryTheory.sfbSheafTensor_properties`, module
  `Sheaf.CategoryTheory.SheafTensor`, and `sfbSheafTensorStructure` in its structure
  dependency. Its monoidal field is the localized `Sheaf.monoidalCategory`.
  The existing lemma uses the same upstream instance
  `AlgebraicGeometry.ProEtale.sheafMonoidalCategory` in
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`.
- `sk-def-sfb-ring-object`: the recorded
  `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf` imports the Mathlib
  `MonObj`, `IsMonHom`, `IsCommMonObj` interfaces used by the lemma. Their full
  structures were read in Mathlib's `CategoryTheory/Monoidal/Mon.lean`.
- `sk-def-sfb-module-objects`: `CategoryTheory.Mod` and `Mod.regular`, module
  `Mathlib.CategoryTheory.Monoidal.Mod`. The category's objects carry a unital,
  associative action and its morphisms preserve that action.
- `def-sfb-finitely-presented-module`: its closed upstream audit records
  `CategoryTheory.Mod.IsFinitelyPresented`, module
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`. This is usable even though
  this node has no separate `lean` record; no repair or duplicate definition is needed.
- `sk-def-sfb-change-of-scalars`: `CategoryTheory.Mod.extendScalars`, module
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`. Its docstring and
  definition give exactly the relative coequalizer and first-factor action.

The existing proof was also read: `fp_map` transports a finite-free cokernel
presentation under an additive finite-colimit-preserving functor;
`extendScalarsRegularIso` uses the mixed-bimodule right unitor to identify the
extended regular module with S. These are the same steps as the node's proof.
The recorded right-exactness declaration
`Mod.preservesFiniteColimits_extendScalars` in `ModuleObjects.ChangeOfScalarsSquare`
and `Bimod.rightUnitorBimod` in Mathlib match those inputs.

Edge cases checked: `m = 0` and `n = 0` are included by the natural-number
existentials and empty biproduct; zero modules and zero ring objects are allowed;
`φ = 𝟙 R` is allowed without an isomorphism hypothesis; the empty scheme is not
excluded. A nonflat map such as the constant-ring map Z → Z/2 is allowed: only
cokernels and finite sums are preserved, not injectivity of the presentation map.

Searches performed using `msearch.py Q140` for this item:

- LeanFinder: “Extension of scalars preserves finite presentations of internal
  module objects over commutative ring objects in abelian sheaves”. Eight hits,
  including `SheafOfModules.Presentation.map`; these use another encoding.
- Loogle: `"extendScalars", "IsFinitelyPresented"`. Zero hits.
- Mathlib grep: `IsFinitelyPresented|extendScalars` in `CategoryTheory/Monoidal`.
  Zero hits.
- LeanSearch: “Scalar extension preserves finite cokernel presentations of internal
  module objects”. Eight hits, including `instFinitePresentationTensorProduct`
  and `ModuleCat.extendScalars`, which concern ordinary modules.
- Project rg: `IsFinitelyPresented|finiteFree|` followed by the item id in the
  category-theory and pro-etale sources. Found the exact public `fp_extend` above.
  The broader search `IsFinitelyPresented.*extendScalars|fp_extend` in
  `lean/WeilConjectures` found no declaration. Searching
  `IsFinitelyPresented.*extendScalars|isFinitelyPresented.*extendScalars|` +
  `extendScalars.*[Ff]initely|` + the item id in both project roots found this lemma
  and private helpers in other modules. The public lemma suffices.
- Source confirmation: `scompile.py --source` returned the live module with the
  same public declaration and section parameters. The existing declaration is
  checked on the server through the prescribed compiler wrapper and again by
  the delivery wrapper's existing-declaration probe.

No statement dispute, missing notion, dependency repair, or statement correction.
The maintainer's independent review is the delivery's second reading.

## Second reading by Q140

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
