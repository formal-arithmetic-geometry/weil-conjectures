## Worker report

This repair uses the landed canonical scalar extension and pullback comparison from
`def-sp-constant-scalar-pullback-comparison`.  The duplicate local constructions of
scalar extension, restriction, the coefficient square, the restriction/pullback map,
and its mate/isomorphism (the seven declarations returned under H4) were removed.
The module now imports
`Sheaf.SecSmoothPurity.DirectImageScalarExchange` and declares only
`coefficientFrobeniusTrivialization` and
`absoluteFrobenius_coefficient_naturality`, both in
`Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality`.

`coefficientFrobeniusTrivialization` is the actual derived Frobenius trivialization
constructed by `proEtaleFrobeniusDerivedIso` from the section-normalized witness in
`absoluteFrobenius_proEtale_trivialization_pullback`; it has type

```
proEtaleConstantRingDerivedPullback A
    (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 (proEtaleDerivedCategory X A)
```

The target theorem is stated with the canonical declarations supplied by the repaired
statement dependency:

```
theorem absoluteFrobenius_coefficient_naturality (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (b : ℕ) (K : proEtaleDerivedCategory X A) :
    (AlgebraicGeometry.ProEtale.directImageScalarPullbackIso φ
      (X.iterateFrobenius hp (hX.2 ⊤) b)).hom.app K ≫
        (AlgebraicGeometry.ProEtale.directImageScalarExtension φ X).map
          ((coefficientFrobeniusTrivialization p hp X hX A b).hom.app K) =
      (coefficientFrobeniusTrivialization p hp X hX B b).hom.app
        ((AlgebraicGeometry.ProEtale.directImageScalarExtension φ X).obj K) :=
```

The binders render the hypotheses clause by clause: `p : ℕ` and `hp : p.Prime`
are a prime characteristic; `X : Scheme.{u}` and `hX : X.IsCharacteristic p`
are the characteristic-
`p` scheme; `{A B : Type u}` with `[CommRing A]`, `[CommRing B]` are finite
commutative coefficient rings, with `[Finite A]`, `[Finite B]`; `φ : A →+* B`
is the unital coefficient map; `b : ℕ` is every nonnegative iterate; and
`K : proEtaleDerivedCategory X A` is arbitrary.  The expression
`X.iterateFrobenius hp (hX.2 ⊤) b` is the absolute Frobenius iterate.  The first
term is the canonical comparison
`directImageScalarPullbackIso φ (F_X^b).hom.app K`, from the imported definition,
whose source is the pullback of the scalar extension of `K` and whose target is the
scalar extension of the pullback of `K`.  It is followed by the map under the same
canonical scalar extension of the `A`-trivialization.  The right side is the
`B`-trivialization at the scalar extension of `K`.  Thus the displayed equality is
exactly `T(τ_A) ≫ c = τ_B` with the comparison in the direction required by the
node.  There are no flatness, Tor-amplitude, boundedness, or constructibility binders;
`b = 0` is included by `ℕ`.

The dependency declarations used are:

- `Sheaf.AlgebraicGeometry.SchemeCharacteristic`: `Scheme.IsCharacteristic`.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `Scheme.iterateFrobenius`.
- `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite`:
  `proEtaleFrobeniusDerivedIso` and the absolute-Frobenius site trivialization.
- `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback`:
  `absoluteFrobenius_proEtale_trivialization_pullback`, including its projection,
  section-unit, iterate, and zero normalizations.
- `Sheaf.SecSmoothPurity.DirectImageScalarExchange`:
  `AlgebraicGeometry.ProEtale.directImageScalarExtension` and
  `AlgebraicGeometry.ProEtale.directImageScalarPullbackIso`.  These are the
  canonical constructions recorded by `def-sp-constant-scalar-pullback-comparison`;
  no local copy or arbitrary isomorphism is introduced.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` supplies the finite-coefficient
  pro-etale derived category used by the target.
- The remaining statement/proof dependencies are retained in the DAG because the
  source statement and proof plan cite the derived change-of-rings, Frobenius
  pullback, scalar-six-pullback, and finite-discrete coefficient-identification
  results.  They are not redefined in this module.

Edge cases checked: `b = 0` (the iterate and comparison normalize to identity),
`b = 1`, arbitrary iterates, empty schemes, `K = 0`, `φ = id`, the zero ring
(including `A = 0`, which forces `B = 0` for a unital map), and the non-flat map
`ℤ/p^2 → ℤ/p`.  All use the same canonical constant-ring constructions; no flatness
or Tor hypothesis is introduced.  No statement is disputed and no statement
correction or new node was needed.

Searches made before and during the repair were the recorded `msearch.py`
`leanfinder`, `loogle`, `leansearch`, and `grep` searches for Frobenius/coefficient
naturality, plus `rg` searches in the upstream `WeilConjectures` tree and the shared
`lean/Sheaf` tree.  They found no existing declaration of this theorem.  The exact
search for `directImageScalarPullbackIso`, `directImageScalarExtension`, and
`def-sp-constant-scalar-pullback-comparison` identified the landed module
`Sheaf/SecSmoothPurity/DirectImageScalarExchange.lean` and its DAG record, which are
now used directly.

Validation: `scompile.py Q60 lem-trf-absolute-frobenius-coefficient-naturality`
compiled the repaired module in both sandbox and library forms with no errors or
non-sorry warnings.  The expected target proof remains `sorry` for stage 2.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
