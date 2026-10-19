## Worker report

The module `lean/Sheaf/Paper/SfDirectImageCTFNonproper.lean` states
`AlgebraicGeometry.Etale.directImageCTFNonproper`.  It uses the existing finite-field datum
`D`, a prime `l` with `l ≠ D.p`, a finite-dimensional extension `E` of `Padic l`, a positive
level `n`, and the coefficient ring `Padic.coefficientExtensionRing l E n`.  The `ULift` of
that ring is the coefficient type of `ModuleCat`; this is the universe lift used by the
recorded small-etale derived-category declarations and denotes the same ring `A = A_{E,n}`.
The theorem concludes bounded constructibility on `Y` and Tor amplitude in `[a,b+2d]` for the
right-derived `Etale.lowerStar` along `f`.

The Lean signature renders each clause as follows.

* The global datum is `D : WeilConjectures.FiniteFieldDatum.{u}`.  The coefficient prime and
  extension are `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`,
  `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, and
  `(n : ℕ) (hn : 1 ≤ n)`.
* Finite-type `k`-schemes are `X Y : Scheme.{u}` with `X.Over (Spec (CommRingCat.of D.k))`
  and `Y.Over (Spec (CommRingCat.of D.k))`, together with `LocallyOfFiniteType` and
  `QuasiCompact` instances for their structure maps.
* The morphism is `(f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]`, with
  `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.  There is no properness,
  compactification, or other extra hypothesis.
* The dimension data are `(d : ℕ)` and
  `hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`.
* The input is a derived object `K` of sheaves of modules over the lifted coefficient ring on
  `X.smallEtaleTopology`; `hK` is
  `DerivedCategory.boundedConstructible (...) X K` and `hTor` is
  `DerivedCategory.hasTorAmplitudeIn (...) X a b K`.
* The conclusion is the conjunction of
  `DerivedCategory.boundedConstructible (...) Y (R f_* K)` and
  `DerivedCategory.hasTorAmplitudeIn (...) Y a (b + 2 * (d : ℤ)) (R f_* K)`, where `R f_*` is
  rendered by `(Etale.lowerStar (...) f).rightDerivedFunctor.obj`.

The statement dependencies used are:

* `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum` (global datum);
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.coefficientExtensionRing` and `Padic.finite_coefficientExtensionRing` (the finite
  coefficient construction and its positive-level finiteness theorem);
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`;
* `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`;
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsSeparated`;
* `Sheaf.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and
  `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible`;
* `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`,
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`;
* `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`;
* `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` (the module-valued constructibility
  notion used by the derived constructibility predicate);
* the recorded direct-image declaration
  `AlgebraicGeometry.Etale.lowerStar` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, with its
  `rightDerivedFunctor`.

Edge cases checked: `n = 1` is admitted by `1 ≤ n`; `d = 0` gives the stated shift by zero;
empty `X` is admitted (its Krull dimension is below every natural bound and the direct image is
zero); and no assumption `a ≤ b` is added, so the empty-interval convention of the Tor predicate
is retained.  The statement keeps arbitrary integer `a,b`, arbitrary finite-type `Y`, and does
not introduce properness.  The lifted coefficient type does not restrict the underlying ring or
its positive level.

Searches for an existing declaration were run as follows:

* `msearch.py ... leanfinder "bounded constructible etale complex finite Tor amplitude direct
  image separated finite type algebraically closed field dimension bound"`: eight Mathlib hits,
  all about etale algebra or morphism permanence; no direct-image Tor statement.
* `msearch.py ... loogle
  "torAmplitudeIn_rightDerivedLowerStar,boundedConstructible_rightDerivedLowerStar,DerivedCategory.hasTorAmplitudeIn"`:
  no hits (the unqualified query names are unavailable to Loogle).
* `msearch.py ... grep
  "boundedConstructible.*rightDerivedLowerStar|torAmplitudeIn.*rightDerivedLowerStar|directImage.*Tor"
  Mathlib`: no hits.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` found only the general source theorem
  `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar` and related proper/open or
  pro-etale results; it found no declaration of this finite-field nonproper corollary.

No new definition node or dependency repair was needed.  The theorem proof is intentionally
`sorry` at stage 2.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the complete theorem signature independently.  The prime,
finite extension, positive level, finite-type scheme, separated finite-type morphism, dimension
bound, arbitrary integer interval, bounded-constructible input, and Tor-amplitude input all occur
as binders.  The conclusion has exactly the two requested clauses, with the same input object and
interval endpoint `b + 2 * (d : ℤ)`.  The `Etale.lowerStar` right-derived functor is the recorded
module-sheaf direct image.  No properness or compactifiability binder appears, and no conclusion
was weakened or strengthened.  The `ULift` is only the recorded universe transport for
`A_{E,n}`.  Empty schemes, level one, zero dimension, and empty Tor intervals remain represented.

## Second reading by NC

I opened the node, its source-place metadata, every recorded statement dependency, and the
module before checking the signature. The node introduces the following data, rendered by the
Lean binders as indicated.

* The global datum is `D : WeilConjectures.FiniteFieldDatum.{u}`. Its fields provide the prime
  `D.p`, the finite field `D.k₀`, and the fixed algebraic closure `D.k` used below.
* The coefficient data are a natural `l` with `[Fact l.Prime]` and `hl : l ≠ D.p`, a field
  `E : Type u` with `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]`, and `n : ℕ` with `hn : 1 ≤ n`. The coefficient ring is
  `Padic.coefficientExtensionRing l E n`, represented in the module category by
  `ULift.{u + 1}` exactly as required by the recorded six-functor encoding.
* The finite-type schemes are `{X Y : Scheme.{u}}`, each with an `Over` structure over
  `Spec (CommRingCat.of D.k)`, `[LocallyOfFiniteType (X ↘ ...)]`, `[QuasiCompact (X ↘ ...)]`,
  and the corresponding two instances for `Y`. Thus “finite type over `k`” is the conjunction
  of the node's locally-finite-type and quasi-compact structure-map clauses.
* The morphism is `f : X ⟶ Y` with `[f.IsOver (Spec (CommRingCat.of D.k))]`,
  `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and `[QuasiCompact f]`. These are exactly
  separated and finite type; there is no properness or compactification hypothesis.
* The dimension data are `d : ℕ` and
  `hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, using Mathlib's topological Krull
  dimension. The integer endpoints are the unrestricted binders `a b : ℤ`.
* The input is `{K : DerivedCategory (Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} (ULift (Padic.coefficientExtensionRing l E n))))}`. The hypotheses
  `hK : DerivedCategory.boundedConstructible ... X K` and
  `hTor : DerivedCategory.hasTorAmplitudeIn ... X a b K` render respectively bounded
  constructibility and Tor amplitude in `[a,b]` on the small étale site.
* The conclusion is the conjunction whose first clause is
  `DerivedCategory.boundedConstructible ... Y ((Etale.lowerStar ... f).rightDerivedFunctor.obj K)`
  and whose second clause is
  `DerivedCategory.hasTorAmplitudeIn ... Y a (b + 2 * (d : ℤ))` of that same derived
  direct image. `Etale.lowerStar` is the recorded canonical module-sheaf direct image and
  `rightDerivedFunctor.obj` is its right-derived value.

Every listed object, hypothesis, and conclusion clause agrees with the node. In particular,
`[QuasiCompact f]` is the quasi-compact half of the stated finite-type hypothesis, the two
structure-map pairs are the finite-type hypotheses on `X` and `Y`, and `f.IsOver` expresses
that the morphism is over the fixed algebraic closure. No stronger field, Noetherian,
properness, compactification, or characteristic assumption was added, and no conclusion was
weakened or strengthened. The dependency declarations were read directly: `FiniteFieldDatum`,
`Padic.coefficientExtensionRing`, `topologicalKrullDim`, `smallEtaleTopology`,
`DerivedCategoryModule`/`boundedConstructible`, `hasTorAmplitudeIn`,
`Scheme.IsConstructibleEtaleModuleSheaf`, and `Etale.lowerStar` all supply the notions used
by the signature; no private duplicate is present.

The edge cases remain covered: `n = 1` satisfies `1 ≤ n`; `d = 0` gives the node's shift by
zero; the empty scheme is allowed by the scheme binders and the `WithBot ℕ∞` dimension bound;
`a` and `b` are arbitrary integers, so the dependency's empty-interval convention is retained;
and the prime characteristic case is excluded exactly by `hl : l ≠ D.p`. Universes are shared
as in the coefficient and small-étale declarations (`E`, `X`, `Y`, and `D` at `Type u`), with
only the documented `ULift` to the module category.

For the one-definition check I ran `msearch.py` with LeanFinder, Loogle, and grep queries for
`directImageCTFNonproper`, bounded-constructible direct images, and Tor-amplitude direct images,
then searched both `WeilConjectures/` and `lean/Sheaf/` with `rg`. The searches found only the
general `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar` and related proper/open
or pro-étale statements; no declaration of this finite-field nonproper corollary exists in
Mathlib, the source repository, or the project. The dependency records therefore remain usable,
and no new definition or dependency module is needed.

No mismatch was found, so the Lean file and node statement were unchanged in this second
reading. The exact file compiled cleanly with `scompile.py`; the only expected diagnostic is
the postponed `sorry` proof.
