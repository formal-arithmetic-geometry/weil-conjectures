## Worker report

The module `Sheaf.AlgebraicGeometry.RegularNormalCrossingsConstantImage` states
`AlgebraicGeometry.Etale.regular_normal_crossings_constant_image`, with its sole proof
postponed by `sorry`. Its real-data helper `normalCrossingsConstantDirectImage` names the
canonical ordinary small-etale `Rj_* B` occurring three times in that statement. No new
DAG node, dependency repair, or statement correction is needed.

Hypothesis and conclusion correspondence:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Finite field B of characteristic ell: `(B : Type (u + 1)) [Field B] [Finite B]
  [CharP B ell]`. The coefficient universe follows the existing ordinary small-etale
  convention and imposes no condition on the characteristic.
- Scheme Y: `{Y : Scheme.{u}}`; Noetherian: `[IsNoetherian Y]`; regular:
  `(_hY : IsRegularScheme Y)`. The latter includes local Noetherianity and stalkwise
  regularity, exactly as the recorded dependency states it.
- ell invertible on Y: `∀ y : Y, IsUnit (ell : Y.presheaf.stalk y)`.
- Closed boundary D: `(D : Y.IdealSheafData)`; strict normal crossings:
  `(_hD : IsStrictNormalCrossingsBoundary D)`. This uses the recorded reduced effective
  Cartier boundary and regular-intersection definition unchanged.
- Complementary open immersion j: `Scheme.Opens.ι D.support.compl`. Its domain is the actual open
  subscheme `Scheme.Opens.toScheme D.support.compl`, not an arbitrary scheme or a map with an
  assumed derived property. Mathlib's canonical open-subscheme inclusion is an open
  immersion. Thus no separate j binder or assumption is needed.
- Number r of irreducible components of D: `Nat.card ↥(irreducibleComponents D.subscheme)`.
  This counts maximal irreducible subsets of the boundary's underlying scheme. They are
  finite because D is a closed subscheme of a Noetherian scheme. No chosen decomposition
  or local branch count replaces the global component count.
- B on Y minus D: `constantSheaf` with `ModuleCat.of B B`, placed in degree zero by
  `_root_.DerivedCategory.singleFunctor _ 0`.
- Derived direct image: `rightDerivedLowerStar (ModuleCat B) (Scheme.Opens.ι D.support.compl)`, applied
  to that constant sheaf in degree zero. This is the existing unbounded right-derived
  extension of the recorded direct image; on this bounded-below input it computes the
  same K-injective direct image as `rightDerivedLowerStarPlus`. It supplies the object
  of the unbounded derived category required by the last clause.
- All R^q j_* B constructible: the first conjunct quantifies `q : ℤ` and applies
  `Scheme.IsConstructibleEtaleModuleSheaf` to the q-th `homologyFunctor` of the image.
- R^q j_* B zero for q greater than r: the second conjunct uses the same homology
  sheaf and `IsZero`, with r cast to ℤ.
- Rj_* B in D^b_c: the third conjunct is exactly
  `DerivedCategory.isBoundedConstructible B Y (normalCrossingsConstantDirectImage B D)`.
  This uses the dependency's finite-value stratification predicate, not a substitute
  boundedness or finite-generation notion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the scheme Noetherian
  condition is Mathlib's `IsNoetherian`, built from that predicate on affine opens and
  quasi-compactness. The definition is inherited through the regular-scheme module.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the canonical inclusion of the complement is an instance.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`. Its live source was
  also checked with `scompile.py --source`; it uses the ordinary small-etale category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; its derived functors in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `rightDerivedLowerStar` and the recorded `rightDerivedLowerStarPlus`.

The module imports the already stated proof dependencies without `public`, using the
upstream constructibility-comparison module to avoid the retired side duplicate.
The regular-lci geometric-calculus and regular-pair-purity nodes have no Lean record yet,
so no nonexistent module is imported for them. The theorem docstring contains all nine
natural-language proof steps from the node, including the strengthened induction,
invertible Tate-line adjunction argument, unbounded exactness for closed immersions,
localization triangle, degree bookkeeping, and extension from F_ell to B.

Edge cases checked against the source and definitions: D empty (ideal sheaf top), its
support empty, complementary immersion the full-open inclusion, no irreducible
components and r = 0; Y empty, with all geometric and invertibility hypotheses vacuous
and all sheaves zero; one smooth divisor (only degrees 0 and 1); two transverse divisors
(bound 2); disjoint divisors (the global count still gives a valid bound); B = F_ell;
negative q (included in constructibility; the derived image of a degree-zero sheaf is
bounded below); arbitrarily large positive q. No nonemptiness or excellence condition
was added. There are no disputed statements or known node faults.

Searches for existing declarations and notions:

- `msearch.py ... leanfinder`: "Higher direct images of a constant finite field sheaf
  across a strict normal crossings divisor on a regular Noetherian scheme are bounded
  constructible". Eight hits, including general scheme structure-sheaf and
  constructible-image results; none state this theorem.
- `msearch.py ... leansearch`: "constant etale sheaf normal crossings divisor higher
  direct image bounded constructible". Eight hits concerning constant sheaves and
  their essential-image criterion, none the asserted normal-crossings result.
- `msearch.py ... loogle`: `"rightDerived", "lowerStar"`. No hits.
- `msearch.py ... grep`: `normal.?crossing|normalCrossing|normal_crossing`, in
  AlgebraicGeometry. No matching theorem.
- `rg` over the upstream WeilConjectures and side `lean/Sheaf` trees for normal crossings,
  normal_crossings, and constant direct image. Existing boundary, branch-count,
  strictification, and permissible-blowup declarations do not state this result.
  Exact-item search upstream gives no existing declaration.
- Exact proposed declaration-name search in both source trees and
  `dag/lean_names_upstream.json` gives no collision.
- The local ILO PDF was read at XVI Theorem 3.1.1 and Corollary 3.1.3 (printed
  pp. 242–243). The latter gives the exterior-algebra formula with one degree-one
  generator for each boundary component, hence the component-count bound. It
  explicitly treats the zero- and one-component induction cases.

Validation: every delivered Lean file is checked with the prescribed `scompile.py`;
final `scompile.py` passed both sandbox and library-name compiles (4.2 s and 4.0 s)
with no warnings or errors. The required delivery preflight is run by `deliver2.py`.

## Second reading by Q63

No independent worker reading: this dispatcher brief requires direct worker delivery
and reserves the independent mathematical reading for the maintainer. I rechecked the
node and complete signature clause by clause as above; the boundary count is the global
irreducible-component count, the site is ordinary small etale, and the coefficient
object is the constant free rank-one B-module. No mathematical mismatch was found.
