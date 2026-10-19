## Worker report

The module `Sheaf.AlgebraicGeometry.BirationalBadLocusComparison` states
`AlgebraicGeometry.Etale.birational_bad_locus_comparison`, with its sole theorem proof `sorry`.
Three helper definitions in this same module spell out the good complement, the canonical
comparison, and the conclusion after shrinking. All definitions have real data. Each has the
item's source and blueprint docstring, and all four declarations are in `lean.declarations`.
No new node or dependency repair is needed. The already landed definition node
`def-kun-unbounded-exchange` is added to `stmt_deps` because the canonical comparison uses it.
The natural-language statement is unchanged.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIII, 3.2.2,
3.3.1--3.3.2, Proposition 3.4.2 and its two-stage proof, and 3.5.1, printed pages 199--202.
The helper comparison implements precisely the adjunction map of 3.3.2: exchange on the
square defining U', restriction to T', and transpose by the canonical adjunction for p_T.
It does not choose an arbitrary arrow or a noncanonical isomorphism.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* Prime ell, finite field B of characteristic ell: `(ell : ℕ) [Fact ell.Prime]`,
  `(B : Type (u + 1)) [Field B] [Finite B] [CharP B ell]`.
* Integer c >= 1: `(c : ℕ) (hc : 1 ≤ c)`. Positive integers and positive natural
  numbers are the same index range, so this excludes no case.
* Height of z: `ringKrullDim (Z.presheaf.stalk z) : WithBot ℕ∞`, the recorded Krull
  dimension of the actual local ring, including both infinite and bottom conventions.
* The simultaneous induction hypothesis is `ih`: it quantifies over every
  `Z : Scheme.{u}`, `[IsNoetherian Z]`, every quasi-excellent affine ring of Z,
  stalkwise invertibility of ell, every scheme V and open immersion v, and every
  `L : DerivedCategoryModule B V` satisfying the recorded bounded constructible predicate.
  The closed set is encoded by its complementary open `O : Z.Opens`; its codimension
  condition is `∀ z, z ∉ O → (c : WithBot ℕ∞) ≤ ringKrullDim ...`, and its good-locus
  condition is bounded constructibility after exact inverse image along `O.ι`.
  This neither fixes Z nor restricts it to integral or separated schemes.
* X integral Noetherian quasi-excellent and ell invertible: `[IsIntegral X]`,
  `[IsNoetherian X]`, `hX` on every affine open, and `hinv` on every local ring.
* Dense open j: `(j : U ⟶ X) [IsOpenImmersion j] (hdense : Dense (Set.range j))`.
* K in D^b_c(U,B): `K : DerivedCategoryModule B U` and `hK` using exactly
  `DerivedCategory.isBoundedConstructible B U K`.
* Integral reduced closed T: `(i : T ⟶ X) [IsClosedImmersion i] [IsIntegral T]`.
  Integrality includes reducedness. Its generic point is `(t : T)` with
  `IsGenericPoint t Set.univ`; its image `i t` has height c by `hheight`.
* Bounded constructibility of Rj_*K on X minus T: `hgood`, using
  `boundedConstructibleOff`; this requires an open with exactly the complement of
  `Set.range i`, not just an unspecified smaller good open.
* Proper morphism of integral schemes p, isomorphism over a dense open:
  `[IsIntegral X']`, `(p : X' ⟶ X) [IsProper p]`, and `hbir` asserting
  `∃ V : X.Opens, Dense V ∧ IsIso (p ∣_ V)`. No extra Noetherian or excellence
  hypothesis is imposed on X'; these follow from finite type over X in the proof.
* Finite completely decomposed family: `n : ℕ`, `E : Fin n → Scheme`, `e`;
  `he` imposes separated, locally finite type, quasi-compact and etale.
  Locally finite type plus quasi-compact is finite type. `hcover` requires for each
  x' an actual z with e(z)=x' and `IsIso ((e k).residueFieldMap z)`.
* Shrinking about t: `∃ W : X.Opens, i t ∈ W ∧ ...`. All maps j, p, i and e are
  replaced by `morphismRestrict`; K is restricted along `(j ⁻¹ᵁ W).ι`.
  Covers are restricted along `p ⁻¹ᵁ W`. Thus the data are base changed together.
* U' and j': the actual categorical `pullback j p` and `pullback.snd j p`.
  K' is exact inverse image of K along `pullback.fst j p`.
* Finite disjoint union T': in `BirationalBadLocusConclusion`, `m : ℕ` and
  `D : Fin m → Scheme`, with T' the scheme coproduct `∐ D` and inclusion
  `Sigma.desc a`. This inclusion is required to be a closed immersion. Every D k
  is integral, so this finite disjoint union is reduced and its summands are its
  integral components, with no missing or intersecting components.
* Each component finite surjective over T: `IsFinite (q k) ∧ Surjective (q k)`;
  `w : CommSq (Sigma.desc a) (Sigma.desc q) p i` states that the induced maps
  commute with p and the inclusions. Restriction to each summand gives the same square.
* A section of some cover member over each component: the quantified `b : Fin n`
  and `s : D k ⟶ E b`, with `s ≫ e b = a k`.
* Rj'_*K' bounded constructible on X' minus T': the helper
  `boundedConstructibleOff B (Sigma.desc a)` applied to the actual derived direct image.
* The specified comparison has a cone in D^b_c(T,B): existential C and arrows f,g
  give `Triangle.mk (birationalBadLocusComparison ...) f g ∈ distTriang ...`,
  with `DerivedCategory.isBoundedConstructible B T C`. Its first map is fixed by
  the helper definition, the adjunction mate of restriction of the canonical exchange.
  In particular neither an arbitrary comparison map nor a bare existential cone is used.
* Empty family allowed: `m = 0` is permitted; there is no Nonempty assumption on Fin m.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherianity
  uses `Mathlib.AlgebraicGeometry.Noetherian.IsNoetherian`.
* `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (the quasi-excellent clause
  of the recorded excellent-ring node).
* `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
* `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` and its module derived category.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  `upperStar`, `upperStarLowerStarAdjunction`; its derived interfaces in
  `Derived.UpperLowerStarCoherence` and `Derived.UpperLowerStar` provide
  `rightDerivedLowerStar` and `mapDerivedUpperStarLowerStarAdjunction`.
  Using the unbounded functors on bounded constructible input gives the same
  ordinary small-etale right derived direct image; no alternative direct image is defined.
* `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` (and hence reducedness).
* `def-weil-pbc-scheme-conventions` is a convention record without its own module;
  its proper, separated, quasi-compact and closed-immersion notions are the Mathlib classes.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
* `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
* `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `exactDerivedSquareUpperStarIso`
  and `exactDerivedBaseChangeMap`, using their real existing definitions.

All recorded statement-dependency declarations were read with their signatures and
source docstrings. Published proof-dependency modules are imported privately as the plan
for stage 3; the unstated proof input
`lem-per-proper-finite-coefficient-bounded-preservation` has no module to import.
The convention `def-weil-triangulated-category` has no module of its own; the cone triangle
uses Mathlib's triangulated interface. The complete ten-step node proof is reproduced in
the theorem docstring, including the proper-unit defect, dimension inequality, finite
components, generic sections, the two comparisons and the octahedral argument.

Edge cases checked: c=1; zero K; j or p an isomorphism; no surviving component
(m=0, so T' empty and the comparison target zero); a cover with no members cannot satisfy
complete decomposition on the nonempty integral X'; empty opens and empty schemes remain
allowed in the induction hypothesis, and its codimension condition is vacuous for an empty
bad set. X and T themselves cannot be empty because they are integral. No finite-dimension,
normality, universal-catenarity or scheme-separatedness assumption was added. All universes
and variables are explicit and `autoImplicit` is disabled.

Searches actually run through msearch.py:

* LeanSearch: `proper birational morphism bounded constructible derived etale direct image
  comparison cone`: 8 hits, mostly IsProper and its stability instances, no matching theorem.
* LeanFinder: `proper birational morphism bad locus bounded constructible etale derived
  direct image`: 8 hits on constructible images, properness and rational maps; no match.
* Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.Etale`: 0 hits.
* Mathlib grep: `birational|completelyDecomposed|IsCompletelyDecomposed`, AlgebraicGeometry:
  8 hits on birational/rational-map files, none on this constructible comparison.
* Direct rg of the source WeilConjectures and project lean/Sheaf for the same concepts
  and the item id: birational geometry tools and a citation in
  `GabberOpenImmersionSheafFiniteness`, but no declaration of this item. The latter supplied
  the existing scheme/coefficient conventions. The exact helper and theorem names were
  also searched in both libraries and Mathlib, with no collisions. The item id has no
  entry in `dag/lean_names_upstream.json`.

Validation: scompile.py compiled both the sandbox probe and the named library module
cleanly (5.0s and 5.6s), with no warnings. No statement dispute or source error found.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
