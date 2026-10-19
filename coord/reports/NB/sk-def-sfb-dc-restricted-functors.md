## Worker report

This is an existing-declaration delivery.  The item is realized jointly by the
published module `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
no replacement module is written.  The node's `lean` record names
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar` as the
primary declaration and lists the declarations that realize every other clause.
I read the complete source through `python3 /home/ubuntu/weil-launcher-nt/scompile.py
--source WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
The source module is the current published side-overlay framework and its module
docstring explicitly describes this exact aggregate definition.

The primary signature recorded verbatim is
`noncomputable def boundedConstructibleUpperStar : Dᵇc(Y.left)⟦Λ⟧ ⥤
Dᵇc(X.left)⟦Λ⟧ :=`.  The scoped `Dᵇc` notation in the source is the full
subcategory `AlgebraicGeometry.ProEtale.BoundedConstructible` of the ambient
module-object derived category.

### Hypothesis and clause correspondence

- The prime and characteristic hypotheses are the source binders
  `(ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.  Thus `p = char(k)` is
  positive and distinct from `ℓ`; no equality of unrelated universes is added.
- The coefficient is the arbitrary commutative condensed ring
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]`.  Its pulled-back coefficient object is the recorded
  `condensedRingObj Λ X.left`/`condensedRingObj Λ Y.left`.
- The schemes are the source's `X Y : Over (Spec (.of k))`, with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]` and
  the corresponding three instances for `Y`.  Morphisms are `f : X ⟶ Y` in
  `Over`, so they are exactly morphisms of the separated finite-type
  `k`-schemes in the node setting.
- `boundedConstructible_leftDerivedUpperStar_obj` states that `L((f.left)^*⟦Λ⟧)`
  preserves bounded constructibility for every `Λ`; its definition
  `boundedConstructibleUpperStar` is the restriction through the full
  subcategory lift.  This is the node's `Lf^*` functor.
- `boundedConstructible_rightDerivedLowerStar_obj` and
  `boundedConstructibleLowerStar` give `R((f.left)_*⟦Λ⟧)` and its restriction
  under `[IsFinitenessCoefficient ℓ Λ]`, the node's coefficient scope together with the finite ℓ-power torsion rings (the scope of the restated lem-sfb-dc-lower-star-preserves)
  for `Rf_*`.
- For an open immersion `j : U ⟶ X`,
  `boundedConstructible_openImmersionLowerShriek_obj` and
  `boundedConstructibleOpenImmersionLowerShriek` give the levelwise exact
  `D((j.left)_!open⟦Λ⟧)` restriction for every commutative condensed `Λ`.
  This is the node's `j_!` clause, including its source and target categories.
- `isMonoidal_boundedConstructible` and
  `isMonoidalClosed_boundedConstructible` (in the same source module) state
  closure under derived tensor and derived internal hom under
  `[IsEllAdicFinitenessCoefficient ℓ Λ]`; the definitions
  `boundedConstructibleTensor` and `boundedConstructibleHom` are respectively
  the full-subcategory monoidal tensor and internal hom.  Their curried types
  are exactly `D_cons(X,Λ) × D_cons(X,Λ) → D_cons(X,Λ)` and
  `D_cons(X,Λ)^op × D_cons(X,Λ) → D_cons(X,Λ)`.
- `boundedConstructibleUpperStarCompatibility`,
  `boundedConstructibleLowerStarCompatibility`, and
  `boundedConstructibleOpenImmersionLowerShriekCompatibility` are the canonical
  `liftCompιIso` comparisons.  They state the required commutation with the
  fully faithful ambient inclusions, with identity components as prescribed by
  the full-subcategory restriction.
- `boundedConstructibleUpperStarLowerStarAdjunction` is
  `Lf^* ⊣ Rf_*`, obtained by `Adjunction.restrictFullyFaithful` from the ambient
  derived adjunction, under the finiteness-coefficient hypothesis.
  `boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction` is
  `j_! ⊣ Lj^*`, for arbitrary commutative condensed `Λ`, using the source's
  canonical identification of levelwise `D(j^*)` with derived pullback.
  `boundedConstructibleTensorHomAdjunction₂` and its fixed-parameter companion
  `boundedConstructibleTensorHomAdjunction` are the tensor--internal-Hom
  adjunctions on the restricted category, with the stated ℓ-adic (`IsEllAdicFinitenessCoefficient`) coefficient
  scope and arbitrary fixed `K` in the bounded constructible category.
- `boundedConstructibleUpperStarComp` is the specified natural isomorphism
  `L(g ∘ f)^* ≅ Lf^* ∘ Lg^*` (with the source's categorical composition
  orientation); its components are preimages of the ambient comparison under
  full faithfulness.  This is the final composition clause of the node.

The source module's docstrings explicitly explain that these are restrictions
of the ambient operations, so no newly derived operation or arbitrary
isomorphism is introduced.  The same module also records the exact preservation
lemmas as `sorry` where the node's proof postpones Deligne finiteness; this
existing record does not claim those proofs are complete.

### Dependency declarations used

- `sk-def-sfb-dc-setting`: `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`
  and the published `BoundedConstructible` interfaces in the same module.
- `sk-def-sfb-module-derived-pushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`
  from `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`.
- `sk-def-sfb-module-lower-shriek`: the published module-object lower-shriek
  interfaces, including `AlgebraicGeometry.ProEtale.CondensedRing.lowerShriek`.
- `sk-def-sfb-derived-tensor-hom`: `derivedTensor` and `derivedHom`, their
  monoidal closed structures, and the ambient tensor--Hom adjunctions from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and `.Tensor`.
- `sk-def-sfb-bounded-constructible`: `boundedConstructible`, its full
  subcategory inclusion, and the constructible membership characterization.
- `sk-def-sfb-condensed-ring`: `Profinite.continuousCoefficientRingObj` and
  `Profinite.isCommMonObj_continuousCoefficientRingObj`, which provide the
  commutative condensed coefficient ring object.
- `sk-def-sfb-qlbar-condensed`: the closed upstream declarations
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`.
- `def-sfb-dc-open-lower-shriek`:
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriek`
  and its inclusion compatibility.

### Edge cases checked

I checked the source signatures for empty schemes and empty opens (no
nonemptiness assumption is present), identity morphisms and identity open
immersions, composite morphisms, zero objects and zero complexes, arbitrary
commutative condensed coefficients for pullback and open lower-shriek, and the
coefficient restrictions for pushforward/tensor/Hom.  The source keeps the
scheme-object universe and coefficient universe explicit.  The tensor and Hom
clauses are restricted to the finite/ell-adic coefficient classes, so the
counterexamples recorded in the source docstrings for arbitrary coefficients are
not accidentally asserted.  No clause adds properness, smoothness, or a chosen
compactification to the functor restriction statement.

### Searches

- `msearch.py NB sk-def-sfb-dc-restricted-functors leanfinder "bounded
  constructible derived category restricted upper star lower star tensor hom
  functors"`: eight generic derived-category/full-subcategory hits; no exact
  six-functor package.
- `msearch.py ... loogle "AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar"`:
  zero hits because the published side module is outside Mathlib.
- `msearch.py ... grep "boundedConstructible(UpperStar|LowerStar|Tensor|Hom)"
  Mathlib`: zero hits.
- `rg` in `WeilConjectures/` initially finds no local old-checkout file for the
  side-overlay path; the prescribed `scompile.py --source` then returned the
  current published module.  I read all declarations and docstrings listed
  above and checked that the source names are absent from the shared `Sheaf`
  tree, so no project duplicate exists.
- `grep -rl "sk-def-sfb-dc-restricted-functors" dag/nodes` confirms this is the
  only node defining the aggregate notion; the component nodes are its recorded
  dependencies.

No statement correction and no `STATEMENT-DISPUTED` finding.  The node copy
changes only its `lean` field and records `existing: true` with branch
`slopmaster2`.

## Second reading by NB

I reread the node statement, every statement dependency and the complete source
module a second time.  The aggregate title is represented by the source's
component declarations rather than by an invented wrapper: upper star, lower
star, open lower-shriek, tensor, Hom, all three adjunction families, inclusion
comparisons and upper-star composition are each present.  The source's
`IsFinitenessCoefficient` and `IsEllAdicFinitenessCoefficient` classes match the
node's three coefficient cases; pullback and open lower-shriek retain arbitrary
commutative condensed `Λ`.  The `Over (Spec (.of k))` binders retain the exact
finite-type/separated setting and the source does not introduce a properness or
smoothness hypothesis.  The compatibility maps are canonical `liftCompιIso`s,
not arbitrary chosen maps.  All five displayed functor types, variance of Hom,
identity/composition behavior, and edge cases above match the node clause by
clause.  No mismatch was found.

## Reviewer fix (maintainer's stage-2 review)

- `lean.statement` was not verbatim: the recorded text kept `noncomputable` and a trailing `:=`, which
  `stage2_delivery.check_existing` reports as differing from the signature it reads,
  `def boundedConstructibleUpperStar : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧`. It is now that signature.
- `lean.note` said that a declarations list records each clause, but the record had no `declarations`. The list
  is now given: 20 declarations of the module, each `#check`ed against the live build with the side overlay.
- Coefficient scope, made precise. `IsFinitenessCoefficient` (used for `Rf_*` and `Lf^* ⊣ Rf_*`) contains the
  node's ℓ-adic rings and also `T̲` for a finite discrete ring killed by a power of ℓ, as in the restated
  `lem-sfb-dc-lower-star-preserves`. This widens the scope, but the preservation claim is true there (Deligne,
  Th. finitude), so no false or stronger assumption is introduced. `IsEllAdicFinitenessCoefficient` (used for
  ⊗ᴸ and RHom) is exactly O_E, E and Qlbar.
