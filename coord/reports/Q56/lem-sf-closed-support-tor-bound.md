## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorBound` states
`AlgebraicGeometry.Etale.closedSupport_torAmplitude`, with proof `sorry`.  It
uses the ordinary constant-`A` module-sheaf derived categories
`DerivedCategoryModule A T`, where `A : Type (u + 1)` is a finite commutative
ring and `Z,T,V : Scheme.{u}`.  The hypotheses render the node clause by clause:

* `[IsClosedImmersion i]` and `[IsOpenImmersion j]`, together with
  `hij : Set.range i.base = (Set.range j.base)ᶜ`, express the complementary
  closed and open immersions.
* The four `PreservesFiniteLimits`/`PreservesFiniteColimits` instances express
  exactness of `i_* = lowerStar` and `i^* = upperStar`; the `IsIso` instance on
  `upperStarLowerStarAdjunction ... i` is the counit isomorphism `i^*i_* ≅ id`.
* `a b e : ℤ`, `hab : a ≤ b`, and `he : 0 ≤ e` render the integer interval and
  its nonnegative enlargement.
* `hK` gives Tor amplitude `[a,b]` for `K`.  `hQ` gives `[a,b+e]` for
  `Rj_*j^*K`, rendered as `R(lowerStar ... j)` applied to
  `upperStar ... j` followed by `mapDerivedCategory`.
* `δ` has the target shifted derived object `i_*i^×K`, and `hδ` says that the
  triangle formed by the canonical closed counit, open unit, and `δ` is
  distinguished.  The conclusion gives `i^×K` Tor amplitude
  `[a,b+e+1]` on `Z`, using the right adjoint of `R i_*`.

The statement dependencies and declarations used are:

* `def-weil-closed-immersion`: Mathlib `AlgebraicGeometry.IsClosedImmersion`.
* `lem-exc-closed-support-triangle`:
  `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`,
  `AlgebraicGeometry.Etale.exists_etale_closedSupportTriangle`.
* `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and `DerivedCategory`.
* `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`,
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn` (the bounded
  predicate is supplied by the imported upstream coefficients module).
* `lem-exc-closed-ambient`:
  `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`,
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
* `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.IsOpenImmersion`.
* `def-weil-pbc-direct-image` and `def-weil-pbc-inverse-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, and
  `upperStarLowerStarAdjunction`.
* `def-weil-triangulated-category`: Mathlib's
  `CategoryTheory.Pretriangulated`/`IsTriangulated` infrastructure.

The proof dependencies imported for the planned proof are the existing
exact-derived-functor, derived-tensor-triangulated, homology-sequence,
exact-functor homology comparison, and inverse-image monoidal-comparison
modules.  Their recorded declarations are used in the module docstring's
five-step proof plan; no proof is attempted here.

Edge cases checked before writing: `i = 𝟙 T` (the counit and triangle reduce to
the identity case), `V` empty (the complement relation is still meaningful),
`e = 0` (the conclusion is exactly the one-step upper shift), `a = b` (the
interval remains well formed), boundary degrees `r = a` and `r = b+e+1`, and
the zero coefficient ring.  The integer hypotheses are retained, and no
boundedness, constructibility, flatness, or nonemptiness assumptions are added.

Searches made: `msearch.py` grep for `torAmplitude|TorAmplitude|tor_amplitude` in
Mathlib Algebra/Homology (no hits); `msearch.py` loogle for `hasTorAmplitudeIn`
(no hits); Lean Finder for “Closed support distinguished triangle Tor amplitude
upper bound plus one” (only generic t-structure declarations); LeanSearch for
“Tor amplitude bound for the fibre object in a distinguished closed support
triangle” (only generic distinguished-triangle declarations); and grep over
`WeilConjectures` for the theorem/notion (no matching closed-support Tor-bound
statement).  The recorded dependency declarations were opened in their source
modules and match the types used above.

## Second reading by Q56

I reread the node and the completed Lean signature independently, checking every
binder and conclusion.  The scheme morphisms, immersion classes, complement
condition, finite commutative coefficient ring, exactness instances, counit
isomorphism, three integer bounds, input object, both Tor-amplitude hypotheses,
canonical triangle maps, distinguishedness clause, and right-adjoint output all
occur in the same order and with the same objects.  The `hQ` expression is
exactly `Rj_*j^*K`, and the conclusion is exactly `i^times K` on `Z` with upper
endpoint `b + e + 1`.  No source hypothesis is omitted and no extra boundedness,
constructibility, flatness, or nonemptiness condition is present.  The only
postponed item is the theorem proof `sorry`, as required for stage 2.
