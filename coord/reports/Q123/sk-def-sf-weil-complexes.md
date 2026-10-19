## Worker report

Repair of immutable returned head bd14e5ad453c, H3/H4. The returned delivery
attached only the upstream pair structure. Its claim that Tate and dual clauses
were merely complementary conventions was incorrect: these clauses need a
Lean interface. This delivery adds
`lean/Sheaf/Paper/StrictWeilDualTate.lean` and keeps the node statement unchanged.
The source read is the complete main-20261015
`sec-smooth-purity/sk-def-sf-weil-complexes/_section.md`, including its complement.
The shared base node has the same statement and no `lean` binding; the repair
replaces the withdrawn sandbox binding rather than repushing it unchanged.

Clause-by-clause correspondence:

- Finite field, algebraic closure and geometric Frobenius: the normalization
  declarations bind `k₀`, `[Field k₀]`, `[Finite k₀]`, use
  `AlgebraicClosure k₀`, and use the existing `specGeometricFrobenius k₀` and
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`. For arbitrary geometric
  fibres the imported `Scheme.Hom.geometricGaloisFrobenius` is the semilinear
  automorphism constructed from the model. The dual constructions are
  parameterized by `T` and `g : T ≅ T`, so apply to X, Y, or any such T.
  The smooth map f in the introductory setting is not an argument of any of
  these constructions; the source explicitly extends them to any T.
- Underlying complex and Weil isomorphism: reuse
  `AlgebraicGeometry.Etale.WeilComplex` without redefining it. Its fields are
  `obj : DerivedCategoryFiniteTor A T` and
  `frobenius : (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).obj obj ≅ obj`.
- Morphisms: reuse `WeilComplex.Hom`, whose equation is
  `K.frobenius.hom ≫ hom = Fr.map hom ≫ L.frobenius.hom`. This is exactly
  `h ∘ φ_K = φ_L ∘ Fr*(h)` with Lean's diagrammatic composition convention.
- Category of pairs and scope: the imported category instance computes identities
  and compositions on underlying morphisms; `WeilComplex.forget` forgets the
  isomorphism. No triangulated structure on pairs is added. The imported
  `WeilComplex.map_hom_eq_zero_of_iso_unit_geometricFiber` supplies the point
  Hom(Λ,Λ[1])=0 example, rather than an identification with Ext of Weil sheaves.
  The sentence limiting later uses to traces, stalk operators, weights,
  equivariant maps and functorial triangles is a scope convention.
- Canonical Tate datum: `strictWeilTateIso Λ g r` is exactly the existing
  `leftDerivedUpperStarTateObjectIso g.hom r`. `WeilComplex.tateLine` places
  `tateObject Λ T r`, with its existing constructible finite-Tor proof, into
  the original pair category. `HasTateTwist` supplies the actual twisting
  object and canonical pullback identification; no second twisting object or
  arbitrary isomorphism is introduced. `HasInvertibleExponent Λ T` is the
  coefficient admissibility hypothesis of this finite-coefficient API, now
  explicitly required by the current published source.
- Normalization: `strictWeilTateScalar Λ q r` renders q^{-r} using inverse(q)^n
  for r=n≥0 and q^{n+1} for r=-(n+1). The second branch explicitly gives the
  q^r convention on negative twists. `strictWeilTateCyclotomicScalar` is the
  geometric cyclotomic character of the actual algebraic closure, mapped
  along `algebraMap ℤ_[l] Λ` and raised to r. Its normalization theorem states
  equality to `strictWeilTateScalar Λ (Nat.card k₀) r`. It binds l prime and
  l≠char(k₀), and imposes no `Finite Λ` or `Field Λ` restriction. Thus its
  scalar-realization interface covers finite, integral, rational and
  algebraically closed coefficient rings. The categorical finite-stage
  theorem `strictWeilTateIso_normalization` states the operator equality on
  H⁰ of the actual normalized Tate line over Spec(k). It requires the existing
  `HasTateTwist.IsNormalized`, rather than claiming the formula for arbitrary
  formal twist data: the source's Tate object is the normalized roots-of-unity
  object, while the unnormalized upstream class also admits other objects.
- Coefficient datum τ₀=φ_Λ: `strictWeilTateIso_zero` states the commuting
  comparison through `HasTateTwist.twistObjectZeroIso`; the coefficient datum
  in the dual formula is the existing `leftDerivedUpperStarUnitIso`.
- Dual object: use the existing
  `DerivedCategory.coefficientDual (ModuleCat Λ) T`, namely RHom(K,Λ_T).
  `strictWeilHomComparison` is explicitly the tensor-Hom transpose of
  inverse(pullback-tensor comparison) followed by pullback of evaluation.
  Its isomorphism theorem uses only that g is an automorphism, and does not
  add a perfectness assumption. `strictWeilHomIso` packages this particular
  canonical map, not a choice from `Nonempty`.
- Three-arrow composite: `strictWeilContragredientMap` first applies
  `strictWeilHomIso`, then `RHom(Fr*K,-).map` of the coefficient datum, then
  `(RHom.map φ.inv.op).app (𝟙_ _)`. These are precisely the three arrows
  displayed in the node, with contravariance and φ^{-1} in the correct order.
  `strictWeilContragredientIso` uses the named proof of invertibility of that
  map. `WeilComplex.contragredientDatum` feeds it the Frobenius isomorphism
  of the existing pair, using its actual forgetful inclusion.
- Twisted dual: `strictWeilTwistedContragredientMap` is
  `tensorWeilDatum g.hom (strictWeilContragredientIso ...).hom
  (strictWeilTateIso ...).hom`. Its source includes the pullback-tensor
  comparison. `strictWeilTwistedContragredientIso` gives the corresponding
  isomorphism by composing the pullback-tensor isomorphism and functorial
  images of the two factor isomorphisms.

The scalar interface for general coefficient realizations is separate from the
categorical theorem for the finite, ordinary-etale `HasTateTwist` API. This
module does not construct completed integral or common-stage Tate Weil pairs;
those are not objects of the imported ordinary-etale pair category. The
universal scalar statement records their normalization, while the pair/dual
construction here uses the same upstream coefficient presentation as the
returned original binding. This distinction is explicit for independent review.

Dependencies used, with signatures and docstrings read:

- `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex`:
  `WeilComplex`, `WeilComplex.Hom`, its category instance, `forget`, and the
  geometric-fibre Hom vanishing declaration.
- `WeilConjectures.AlgebraicGeometry.GeometricFrobenius` (imported by it):
  `specGeometricFrobenius`, `Scheme.Hom.geometricGaloisFrobenius` and its
  base-change/semilinearity descriptions.
- `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius`:
  `tensorWeilDatum` and `frobeniusOperator`.
- Its imported Hom and monoidal comparison modules:
  `derivedTensorHomAdjunction`, `leftDerivedUpperStarTensorIso`,
  `leftDerivedUpperStarUnitIso`, `DerivedCategory.coefficientDual`.
- `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` and its
  `Conventions` import: `HasTateTwist.IsNormalized`, `tateObject`,
  `leftDerivedUpperStarTateObjectIso`, `twistObjectZeroIso`,
  `boundedConstructibleFiniteTor_tateObject`. The current published
  `Conventions` source was read with `scompile.py --source`; it requires
  invertibility of the exponent where these comparisons are used.
- Mathlib `NumberTheory.Cyclotomic.CyclotomicCharacter`:
  `cyclotomicCharacter`, defined from its compatible action on roots of unity.

Every newly postponed theorem is a claim in the unit's complement (canonical
pullback isomorphism, invertibility of its displayed composite, zero-twist
identification, or normalization), and has its source and full proof in its
docstring. Every definition has real data; the `asIso` definitions use named
invertibility theorems determining the inverse of an already constructed map.

Edge cases read against the formulas: r=0 gives scalar 1; r=1 gives inverse(q);
r=-1 gives q. Negative arbitrary r uses integer powers of a unit before
coefficient realization, so the integral and finite cases do not require a
field inverse operation. The zero coefficient ring is allowed. The zero complex
and empty scheme are allowed by the dual definitions. An arbitrary automorphism
(including the identity) is allowed for duals; the q-normalization is asserted
only for geometric Frobenius, not for an arbitrary g. In rank one the φ^{-1}
inside RHom reverses the original Frobenius scalar, as required. No dualizability
or extra assumption that K is perfect was added to the displayed dual datum.

Searches run in the repair:

- `msearch.py ... leanfinder "Weil complex Tate twist geometric Frobenius
  contragredient dual internal Hom"`: eight hits, concerning representations,
  Witt isocrystals and module duals, none the needed scheme-level interfaces.
- `msearch.py ... loogle "WeilComplex, TateTwist, internalHom"`: zero hits;
  Loogle reported unknown identifier WeilComplex.
- `msearch.py ... grep "contragredient|WeilComplex|tateWeil"`: zero Mathlib hits.
- Direct `rg` in upstream `WeilConjectures/` located and read `WeilComplex`,
  `WeilFrobenius.tensorWeilDatum`, `Perfect.Dual.coefficientDual`,
  `Perfect.Pullback`, `UpperStarMonoidal.Comparison`, `Conventions`,
  `KummerClass`, `Mathlib.CategoryTheory.Monoidal.Closed.Basic`, and
  `WeilSheaf.TateTwist`. The last file gives the Qbar-l cyclotomic scalar,
  not the coefficient-general scalar or the missing contragredient composite.
  The generic monoidal closed comparison was read; the new concrete comparison
  writes its adjunction formula in the existing derivedTensor API, with its
  fixed published tensor structure, rather than choosing an abstract isomorphism.
- Direct `rg` in project `lean/Sheaf` found no contragredient or Tate Weil
  interface for this item. Existing coefficient-twist and constant-Weil files
  were read to distinguish the completed/common-stage coefficient categories
  from the ordinary-etale presentation of the returned binding.
- The original three searches and upstream-by-node-id search are retained in
  `searches.jsonl` from the first delivery. The item has no `stmt_deps` to repair.

## Second reading by Q123

Author self-reading, not an independent review; the maintainer supplies the
independent immutable-head reading. I reread the whole node and the new module.
The returned omission was real. The new file has explicit canonical Tate data,
the q^{-r}/q^r scalar interface, τ₀ identification, the exact contravariant
three-arrow dual composite, its isomorphism, and the tensor formula for the
Weil datum of the twisted dual. The original pair and morphism definitions are
imported unchanged. I checked the direction of every arrow, the inverse on φ,
and the source of the tensor composite. I also separated the finite categorical
normalization from the coefficient-general cyclotomic scalar statement in the
report, so the published formalism's coefficient scope is visible to the reader.
No node statement was corrected and no new or dependency node was introduced.
