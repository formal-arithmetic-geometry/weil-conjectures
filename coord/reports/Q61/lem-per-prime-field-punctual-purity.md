## Worker report

`lean/Sheaf/AlgebraicGeometry/PrimeFieldPunctualPurity.lean` states only
`AlgebraicGeometry.Etale.primeField_punctuallyPure`, with proof `sorry`.
It imports `Sheaf.AlgebraicGeometry.PunctualPurity` and uses its landed
`AlgebraicGeometry.Etale.IsPunctuallyPure`. No definitions are delivered.

The signature is:

```lean
theorem primeField_punctuallyPure (ℓ : ℕ) (hℓ : ℓ.Prime) (k : Type u) [Field k]
    (_hk : Nonempty (k ≃+* ℚ) ∨ ∃ p : ℕ, p.Prime ∧ Nonempty (k ≃+* ZMod p))
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsNoetherian X]
    (_hX : IsRegularScheme X) (_hℓX : IsUnit (ℓ : Γ(X, ⊤))) :
    IsPunctuallyPure ℓ hℓ X
```

Hypothesis and clause correspondence:

* `ℓ : ℕ` and `hℓ : ℓ.Prime` specify the prime coefficient; the imported purity
  definition uses `regularClassCoefficients ℓ 1`, the standard lift of `ZMod (ℓ ^ 1)`.
* `k : Type u` and `[Field k]` specify the base field. `_hk` says precisely that
  it is isomorphic to `ℚ` or to `ZMod p` for a prime `p`.
* `X : Scheme.{u}` and `[X.Over (Spec (CommRingCat.of k))]` give a `k`-scheme.
* `[IsNoetherian X]` gives Noetherianity. `_hX : IsRegularScheme X` gives the
  published scheme regularity predicate, including local Noetherianity.
* `_hℓX : IsUnit (ℓ : Γ(X, ⊤))` gives invertibility of the coefficient on `X`.
* `IsPunctuallyPure ℓ hℓ X` is the landed predicate quantifying over every `w : X`.
  Its `IsPunctuallyPureAt` uses `X.presheaf.stalk w` for the local ring,
  `Spec (X.presheaf.stalk w)` for its spectrum, and `Spec.map (X.residue w)`
  for its closed-point inclusion. Its witness `d : ℕ` satisfies
  `ringKrullDim (X.presheaf.stalk w) = (d : WithBot ℕ∞)`. The local Noetherianity,
  regular-immersion and coefficient-unit witnesses allow evaluation of the class.
  `IsIso (punctualPurityClassMap ℓ hℓ ... d ...)` states invertibility of the
  canonical level-one Kummer class, with twist `d` and shift `2 * d`.
  The map is the transpose of the uniquely specified class-calculus family under
  `closedSupportPlusAdjunction`, with the canonical exact-direct-image and D+ comparisons.
* No finite-type or excellence assumption appears in the theorem.

Dependency declarations used, read in the published source:

* `Sheaf.AlgebraicGeometry.PunctualPurity`:
  `AlgebraicGeometry.Etale.IsPunctuallyPure`, `IsPunctuallyPureAt`,
  `punctualPurityClassMap`, `regularImmersionClasses`, and `supportedExtPlusHom`.
  This is `def-per-punctual-purity`, now added to the item's `stmt_deps`.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
* Through the published purity definition:
  `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus` gives
  `regularClassCoefficients`, `regularClassTwist`, and `regular_immersion_class_calculus`;
  `Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange` gives
  `closedSupportPlus` and `closedSupportPlusAdjunction`;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`
  supplies the canonical exact-functor comparison.
* `Mathlib.AlgebraicGeometry.ResidueField` gives `Scheme.residue`;
  `Mathlib.AlgebraicGeometry.Scheme` gives `Spec` and `Spec.map`;
  `Mathlib.RingTheory.KrullDimension.Basic` gives `ringKrullDim`.
  Ordinary derived categories and Tate twists are used through the published predicate,
  rather than copied into this module.

Edge cases checked: empty `X` gives a vacuous quantifier; dimension zero is admitted
and uses the identity class; dimension is recorded in `WithBot ℕ∞`, without truncation;
both characteristic-zero and prime positive-characteristic base fields occur in `_hk`.
The assumption that `ℓ` is invertible excludes characteristic `ℓ` at every nonempty point.
All universes and variables are explicitly bound (`autoImplicit false`).

Searches made (recorded in `searches.jsonl`):

* `msearch.py ... leanfinder "Every regular Noetherian scheme over a prime field is punctually pure for invertible finite etale coefficients"`: eight étale-algebra hits, none about punctual purity or the Kummer class.
* `msearch.py ... loogle "IsPrimeField, IsRegular, IsIso"` and
  `loogle "IsPrimeField, ringKrullDim, IsRegularLocalRing"`: no matching declarations (`IsPrimeField` unknown).
* `msearch.py ... leansearch "Regular Noetherian schemes over a prime field satisfy punctual etale cohomological purity"`: eight general algebraic-geometry hits, none stating this node.
* `msearch.py ... grep "Punctual|punctual|fundamentalClass" AlgebraicGeometry` and
  `grep "PunctualPurity|punctual.purity|IsPrimeField|IsPrimeRing"`: no matches in the searched source trees.
* A second `leanfinder` search for ordinary étale cohomology with invertible prime-field coefficients again returned only étale-locus declarations.


Repair searches on 2026-10-19: `rg` for `primeField_punctuallyPure`,
`def IsPunctuallyPure`, and the two class-map names in the upstream source and
`lean/Sheaf` found the landed `PunctualPurity` definitions, and only unrelated
weight-purity predicates upstream. The corresponding Mathlib name search had no matches.
` scompile.py --source Sheaf.AlgebraicGeometry.PunctualPurity` confirmed the live
source has exactly `IsPunctuallyPure (ℓ : ℕ) (hℓ : ℓ.Prime) (W : Scheme.{u})`.
No item-specific repair-notes file was found.

## Returned-delivery repair

The saved packet's initial dry run passed mechanically at `cbc5f22f85`; the returned
mathematical review still required a source repair. The four local declarations
`punctualKummerClassFamily`, `punctualKummerClassMap`, `IsPunctuallyPureAt`, and
`IsPunctuallyPure` are removed, and the published `PunctualPurity` module is imported.
The theorem now concludes `IsPunctuallyPure ℓ hℓ X`. The Lean declaration list contains
only the theorem. This resolves H12/H4 and prevents the duplicate-name import failure.

Added `def-per-punctual-purity` to `stmt_deps`. Removed
`lem-asd-etale-finite-twist-pullback` from the saved packet's `stmt_deps`, as requested:
its structured comparison data belongs inside the class calculus, not in this signature.
Only `lean` and `stmt_deps` differ from the current shared item node; the mathematical
statement and proof fields are unchanged. There is no statement correction and no new
node or dependency module.

The eleven non-public imports are retained under stages/2-statements.md §3.7: they
are the already-stated proof dependencies, covering excellence, regular completion,
affine smoothness/projective compactification, geometric class calculus, smooth duality,
and compact-support direct image. They are not extra public statement imports.

## Saved-packet self-check

Compared the saved node with the current shared node and read the full live predicate,
class-map signature and docstrings. The hypothesis correspondence above remains exact;
the repair replaces the duplicate implementation by the owning definition node.
The maintainer performs the independent second reading; this dispatcher-started worker
has not represented its own check as an independent review.

The repaired module compiled cleanly via the prescribed `scompile.py` wrapper in both
sandbox and library modes (6.4 s and 5.8 s), with no compiler diagnostics.
No `STATEMENT-DISPUTED` issue remains.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
