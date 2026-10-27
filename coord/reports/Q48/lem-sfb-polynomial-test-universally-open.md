## Worker report

The module `Sheaf.AlgebraicGeometry.PolynomialTestUniversallyOpen` states
`AlgebraicGeometry.universallyOpen_specMap_of_isOpenMap_mvPolynomial` with a
single `sorry`. No definition or auxiliary theorem is introduced. The source is
Stacks Project Tag 0F31, `more-morphisms.tex`, lemma-test-universally-open,
implication (3) to (1), read in full at lines 21725–21788. The node's six-step
proof is included in the declaration docstring. There is no statement correction.
The prior Q66 review is the stage-1 proof review; the current node has no `lean`
record, so this delivery supplies the missing stage-2 statement.

Hypothesis and clause mapping:

- Arbitrary commutative rings A and C are `{A C : Type u} [CommRing A]
  [CommRing C]`. There is no domain, nonzero, reducedness, finite-generation,
  finite-presentation, or Noetherian hypothesis.
- The arbitrary ring homomorphism is `(φ : A →+* C)`. Its affine scheme morphism
  is `Spec.map (CommRingCat.ofHom φ)`, in the required contravariant direction.
- For every integer n ≥ 0 the finite variable set is `Fin n`, and the polynomial
  coefficient extension is `MvPolynomial.map (σ := Fin n) φ`. Its source and
  target are `MvPolynomial (Fin n) A` and `MvPolynomial (Fin n) C`.
  This maps constants through φ and leaves each indexed variable fixed.
- The only extra hypothesis is
  `h : ∀ n : ℕ, IsOpenMap
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) φ)))`.
  Natural numbers include zero. With no variables the constant-polynomial
  equivalences identify this map with φ; no test is omitted or added.
- The conclusion is `UniversallyOpen (Spec.map (CommRingCat.ofHom φ))`.
  Mathlib defines `UniversallyOpen` by the universal closure of topological
  `IsOpenMap`. It quantifies over every scheme base change, equivalently openness
  of `pullback.snd (Spec.map (CommRingCat.ofHom φ)) g` for every scheme T and
  morphism g from T to Spec A. `IsOpenMap` means the image of each open set is
  open. Thus the arbitrary-T, arbitrary-morphism and open-image clauses are all
  retained, including empty T. There is no quasi-compactness or separation bound.

Recorded statement dependencies used, with their source declarations read:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`; the latter accepts
  a morphism of `CommRingCat` and returns `Spec S ⟶ Spec R`.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`; its recorded evaluation/uniqueness declarations are
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` and
  `MvPolynomial.algHom_ext` in Basic. Eval also supplies `MvPolynomial.map`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`. They occur in the existing
  meaning of universal openness; no duplicate fibre product is defined.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` supplies the existing
  `AlgebraicGeometry.UniversallyOpen` class, its universal-closure definition,
  and the base-change projection instances, read directly at lines 37–105.

Proof dependencies were read and their recorded Mathlib modules imported
privately: Pullbacks (`pullbackSpecIso`), Spectrum.Prime.Topology (principal-open
basis and localization), TensorProduct.Defs (module tensor product),
RingTheory.TensorProduct.Basic and Maps (algebra tensor product and pushout),
Scheme (`preimage_basicOpen`, already public for the statement), PullbackCarrier
(`image_preimage_eq_of_isPullback`), AffineScheme (`isBasis_affineOpens`), and
OpenImmersion (open-immersion base change). Basic and Eval are already public
because the statement uses polynomial rings and coefficient maps.

Edge cases checked before writing: n = 0 is present; zero coefficient rings
are permitted by `CommRing` and may have empty spectrum; identity maps and
isomorphisms satisfy all polynomial tests; empty schemes and empty opens cause
no exception to universal openness. Test rings B need not be finitely generated,
and arbitrary infinite affine covers of T are permitted. The universe u is
explicit and arbitrary; rings and the full scheme category share the ambient
universe used by Mathlib's `UniversallyOpen`, with no independent smaller test
universe. `autoImplicit false` forbids automatically introduced binders.

Searches made using the prescribed msearch wrapper:

- LeanFinder: “If Spec of every finite polynomial extension of a ring
  homomorphism is open then its spectrum map is universally open”: 8 hits,
  universal-openness definitions, locality and underlying-open-map facts; none
  is the polynomial criterion.
- Loogle: `"UniversallyOpen", "MvPolynomial"`: 0 hits.
- Mathlib grep: `test.*universallyOpen|universallyOpen.*polynomial|universallyOpen.*MvPolynomial`:
  0 hits.
- LeanSearch: “Universal openness follows if every finite polynomial coefficient
  extension induces an open map on spectra”: 8 hits, definitions, constructor,
  underlying-open-map facts and a going-down/finite-presentation criterion;
  none proves the statement here.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for polynomial tests and
  universal openness: only a reference to this node in the parent
  `FiniteDominantNormalUniversallyOpen` proof, alongside unrelated polynomial
  modules; no existing theorem. Direct grep of this node id in
  `lean/WeilConjectures` found no result. Direct rg of the proposed full
  declaration name in Mathlib, WeilConjectures and Sheaf found no result.

No new nodes, dependency repairs, statement dispute, or hollow constructions.
The only postponed proof is the theorem matching the assigned node.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
