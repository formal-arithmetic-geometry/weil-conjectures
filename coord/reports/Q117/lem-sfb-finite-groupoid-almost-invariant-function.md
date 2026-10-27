## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGroupoidAlmostInvariantFunction` states
`AlgebraicGeometry.finiteGroupoid_exists_almostInvariant_function`, with its proof
`by sorry`. There are no definitions, auxiliary theorems, dependency repairs, or
statement changes. The node copy changes only `lean`.

I read the entire node, its seven statement dependencies, their declaration records,
the groupoid source, the Mathlib definitions used below, the recorded proof-dependency
interfaces, and Stacks `literature/stacks-project/more-groupoids.tex` at
`lemma-find-almost-invariant-function` (Tag 0ABF, lines 2706 onward). The Stacks
statement has exactly the hypotheses and conclusion of the node. The withdrawn
CompactObject example was read; its node now points to the upstream module.

Hypothesis and conclusion correspondence:

- The two schemes are `{U R : Scheme.{u}}`. The specified source, target, identity,
  inverse and composition are `s t`, `e`, `i`, and `c : pullback s t ⟶ R`.
  `hG : IsGroupoidScheme s t e i c` uses the recorded absolute groupoid structure.
  Its laws hold on all test schemes, so residue-field extensions needed to compose
  arrows are available; no rational-point restriction is imposed.
- Both maps are finite: `[IsFinite s] [IsFinite t]`. Both are of finite presentation:
  `[LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t]`, together with
  finiteness already imposed. Finite morphisms are affine, hence quasi-compact and
  separated, hence quasi-separated. Thus this is exactly finite presentation in the
  conventions node, with no omitted global condition and no extra hypothesis.
- The finite list is `(m : ℕ) (x : Fin m → U)`. No positivity, nonemptiness,
  distinctness, reducedness or integral-scheme hypothesis is imposed.
- For every list index `k` and every `y ∈ t '' (s ⁻¹' {x k})`, `hOrbit` requires
  `∃ Z ∈ irreducibleComponents U, IsGenericPoint y Z`. This states that every
  point of each indicated orbit is generic in some irreducible component. It does
  not restrict only the marked points and does not require the orbits disjoint.
- The commutative ring is bundled as `A : CommRingCat.{u}`. The scheme morphism is
  `j : U ⟶ Spec A` with `[IsImmersion j]`, the immersion notion named in the
  closed-immersion node's `mathlib_match`. A closed immersion is not assumed.
- The boundary ideal is `I : Ideal A`. Its zero locus is exactly
  `PrimeSpectrum.zeroLocus (I : Set A)`, namely the prime ideals containing I.
  `hDisjoint` renders `j(U) ∩ V(I) = ∅` literally using `Set.range j`.
  `hClosed` renders closedness of `V(I) ∪ j(U)` literally. Neither is replaced
  by a stronger closedness or quasi-compactness hypothesis on j(U).
- `∃ h ∈ I` is an element of that same ideal in A.
- `j ⁻¹ᵁ PrimeSpectrum.basicOpen h` is precisely the open subscheme with point
  set j inverse-image D(h), since `basicOpen h` consists of primes not containing h.
- `IsAffineOpen (...)` asserts affineness of that open subscheme of the original U.
- `∀ k : Fin m, x k ∈ ...` includes every marked point.
- Equality of its inverse-image opens under s and t is precisely the last conjunct.
  Equality of opens gives the requested equality of inverse-image open subschemes;
  no invariance condition on the function itself is added.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.GroupoidScheme`, `AlgebraicGeometry.IsGroupoidScheme`.
  I read every field, including composition orientation and the identity/inverse laws.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`; the scheme-conventions node is a
  convention record and introduces no declaration of its own.
- `Mathlib.Topology.Sober`, `IsGenericPoint` (closure of the singleton).
- `Mathlib.Topology.Irreducible`, `irreducibleComponents` (maximal irreducible subsets).
  This dependency is a Mathlib leaf; its `mathlib_match` supplies the declaration.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`; its carrier reduces
  to `PrimeSpectrum A`, so there is no transport to a different space.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `AlgebraicGeometry.IsImmersion`,
  named in `def-weil-closed-immersion.mathlib_match`. The recorded
  `AlgebraicGeometry.IsClosedImmersion` is the closed variant, not the hypothesis here.
  No dependency repair is needed because the match explicitly supplies both notions.
- `Mathlib.RingTheory.Spectrum.Prime.Basic`, `PrimeSpectrum.zeroLocus`;
  `Mathlib.RingTheory.Spectrum.Prime.Topology`, `PrimeSpectrum.basicOpen`;
  `Mathlib.AlgebraicGeometry.AffineScheme`, `AlgebraicGeometry.IsAffineOpen`;
  scheme inverse-image notation `⁻¹ᵁ`. These are standard Mathlib constructions,
  re-exported by the public scheme-morphism imports.

Proof-only imports include the modules of the recorded norm-chart, invariant-norm,
and norm-prime declarations:
`WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts.exists_finiteLocallyFree_norm_charts`
(the declaration itself is `AlgebraicGeometry.exists_finiteLocallyFree_norm_charts`),
`Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm` /
`AlgebraicGeometry.affineGroupoid_invariant_norm`, and
`WeilConjectures.Mathlib.RingTheory.Localization.NormTrace` / `Algebra.norm_notMem_iff`.
The remaining Mathlib proof leaves are available through the immersion, proper,
quasi-finite, residue-field, ideal-operations and localization modules. The proof-only
node `lem-sfb-finite-groupoid-generic-affine-flat-thickening` has neither a Lean record
nor a Mathlib match, so there is currently no module to import for that node; it is
named with its application in the theorem's full natural-language proof docstring.
The norm theorem uses another existing presentation of groupoid laws; the translation
from the supplied recorded `IsGroupoidScheme` laws is proof work, not an added hypothesis.

Edge cases checked before writing:

- m = 0: choose h = 0. D(0) and both inverse images are empty; the empty open
  is affine (Spec of the zero ring). No `[Nonempty (Fin m)]` appears.
- Empty U: the same witness works; a nonempty list cannot be supplied.
- Zero A: Spec A is empty and any immersion into it has empty source; allowed.
- I = bottom: disjointness from V(0) forces U empty; again h = 0 works.
- I = top: the closedness hypothesis is still retained, as in the source.
- Repeated marked points and intersecting marked orbits are permitted.
- Identity groupoid at a field spectrum: the hypotheses have concrete instances,
  and choosing a boundary-ideal element nonvanishing at the point gives the conclusion.
- Nonreduced schemes and varying arrow ranks are unrestricted. The statement has no
  flatness, global freeness, connectedness or positive-characteristic restriction.
- The common universe u is the usual scheme/ring size convention; arbitrary universes
  are admitted, and no quantification over smaller test algebras becomes vacuous.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “A finite finitely presented scheme groupoid immersed
  in Spec A admits an affine invariant principal open from a boundary ideal containing
  finitely many generic orbits”. Eight hits, including affine covers and ideal-sheaf
  covers; none gives the groupoid assertion.
- `msearch.py ... leansearch`: “A finite scheme groupoid admits an invariant affine
  principal open in a boundary ideal containing finitely many generic point orbits”.
  Eight hits on affine basic opens, IsFinite, and quasi-affine schemes; no match.
- `msearch.py ... loogle '"IsGroupoidScheme", "IsAffineOpen"'`: zero hits.
- `msearch.py ... grep 'almost.*invariant|invariant.*function|groupoid.*[Nn]orm'`:
  25 hits, all unrelated modular-form, group-action, manifold or measure material.
- `rg -n 'almost.*[Ii]nvariant|[Ii]nvariant.*[Ff]unction|0ABF'` in both named
  project source roots: unrelated invariant-function declarations; no match.
- `grep -rn 'lem-sfb-finite-groupoid-almost-invariant-function' lean/WeilConjectures`:
  no hits. Exact-name search `finiteGroupoid_exists_almostInvariant` in both source
  roots and `dag/lean_names_upstream.json`: no hits.

No STATEMENT-DISPUTED flag or node fault was found. All variables and universes are
explicitly bound. Server compilation via scompile.py passed both sandbox and library
module-mode checks (4.1 s and 5.7 s), with no errors or warnings.

## Second reading by Q117

I reread the node and final signature in a separate pass; this is a self-review,
not a claim that another agent reviewed it (the dispatcher explicitly forbids
starting agents and provides an independent maintainer review after delivery).
The seven hypotheses match the signature: groupoid data, both finite maps, finite
presentation via locally finite presentation plus finiteness, genericity throughout
all marked orbits, immersion into the same Spec A, ideal disjointness, and closed
union. The four conclusion clauses are membership in I, affine inverse-image
principal open, containment of every marked point, and equality of the s/t preimages.
The orbit uses arbitrary underlying points, not only rational points. The groupoid
composition ordering agrees with the dependency. Fin m includes zero. There is no
extra conclusion about equality of pullbacks of h as functions. The hypotheses
require no extra global affineness of U. No mismatch or correction was found.
