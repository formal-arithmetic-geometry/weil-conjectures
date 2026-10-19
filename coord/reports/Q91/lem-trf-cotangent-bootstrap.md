## Worker report

The module `Sheaf.RingTheory.CotangentBootstrap` states Stacks Tag 08R1
(`cotangent.tex`, `lemma-bootstrap`) on the standard cotangent complex already
provided by `lem-trf-cotangent-resolution-coherence`. Its one theorem has proof
`sorry`; the two helper definitions contain actual canonical data. The node's
statement and dependencies are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The homomorphism of commutative rings `A → B` is
  `f : Arrow CommRingCat.{u}`; `A = f.left`, `B = f.right`, and the map is `f.hom`.
  No injectivity, flatness, finite presentation, or nonzero-ring assumption is made.
- `Tor_i^A(B,B) = 0` for every `i > 0` is `hTor : ∀ i : ℕ, 0 < i →
  IsZero (((CategoryTheory.Tor' (ModuleCat.{u} (f.left : Type u)) i).obj
  (arrowModule f)).obj (arrowModule f))`. The helper `arrowModule` restricts the
  regular `B`-module along the given ring homomorphism, using the actual
  `ModuleCat.restrictScalars`. Thus both occurrences are the specified `B`
  with its `A`-module structure. `Tor'` derives in the first variable as recorded
  by the Tor dependency. `IsZero` concerns an object of `ModuleCat A`, not a bare type.
- `L_{B/(B ⊗_A B)} = 0` is `hDiagonal : IsZero (cotangentComplex C
  (diagonalCotangentArrow f))`. The helper arrow uses the algebra structure
  `f.hom.hom.toAlgebra` and Mathlib's `Algebra.TensorProduct.lmul'`, whose
  value on `b₁ ⊗ b₂` is `b₁ * b₂`. Its source is exactly `B ⊗[A] B` and its
  target is `B`; no arbitrary map or choice is supplied.
- The conclusion `L_{B/A} = 0` in `D(B)` is `IsZero (cotangentComplex C f)`.
  Both cotangent complexes use the SAME `C : Coherence.{u}` from the recorded
  dependency; they are the standard polynomial-resolution models, not the
  two-term naive cotangent complex or just its first two cohomology groups.
- `[∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]`
  is the ambient localization choice required by that recorded interface, not
  an additional algebraic hypothesis. Its standard instance is available from
  `HasDerivedCategory.standard`. Likewise `C` is a realization of the specified
  standard construction, whose existence is `exists_coherence` in the dependency.
  The theorem holds for every such realization. The single ring universe can
  contain any two given rings by using a common containing universe.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
  The dependency record was read together with these declarations and docstrings.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor' (C) (n : ℕ) :
  C ⥤ C ⥤ C`, explicitly left-derived in its first factor. Module-category
  abelian, monoidal and projective-resolution instances are imported explicitly.
- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `cotangentComplex`,
  `derivedDifferentials`, `differentialComplex`, and `exists_coherence`.
  I read the full model, standard formulas, comparison and functoriality fields,
  as well as the definitions of the complexes and the existence docstring.
  The dependency's public import exposes this interface to consumers.

Additional canonical APIs used are `ModuleCat.restrictScalars`, `ModuleCat.of`,
`RingHom.toAlgebra`, `Algebra.TensorProduct.lmul'`, `CommRingCat.ofHom`, and
`Arrow.mk`. These helpers only package the module and arrow occurring in this
node's own statement; no independent mathematical notion or postponed helper
lemma is introduced.

All currently stated proof dependencies are imported: bounded-flat K-flatness,
K-flat scalar-extension counit, localization cotangent vanishing, the derived
homology long exact sequence, the polynomial Kähler basis, and resolution
coherence (and the public Tor definition). The flat-base-change and transitivity
nodes have no recorded declarations yet; no import can be made for them. They
are not statement prerequisites. The theorem's docstring preserves all three
steps of the node's proof, including factor-map orientation, the identity-ring
localization argument, and the explicit K-flat tensor cancellation.

Edge cases checked against the source:

- `A = B` with identity map: the positive Tor groups vanish and both relevant
  standard cotangent complexes vanish; the statement specializes correctly.
- Zero rings are allowed: there is no `Nontrivial` binder, and tensor
  multiplication and restriction of scalars remain defined.
- Positive Tor is precisely `0 < i`; degree zero is deliberately not forced
  to vanish. For `k[t] → k[t]/(t)`, positive Tor does not vanish, so the premise
  correctly fails rather than yielding a false conclusion.
- For a polynomial algebra `A[x]`, the diagonal cotangent complex need not
  vanish; the diagonal hypothesis correctly excludes the usual nonzero
  cotangent complex. For localizations, both hypotheses have the expected
  vanishing behavior.
- No boundedness of the cotangent complex is assumed in the theorem; its
  standard model is supplied by the existing dependency. No characteristic
  or finiteness restriction is added.

Searches for existing statements and definitions:

- `msearch.py`, LeanFinder: “if Tor over A of B B vanishes and cotangent complex
  over tensor product vanishes then cotangent complex over A vanishes”. Eight
  hits: `Algebra.Extension.exact_cotangentComplex_toKaehler`, formally smooth
  cotangent base-change injectivity results, `Algebra.formallyEtale_iff`,
  `Algebra.Extension.tensorH1Cotangent`, standard smooth first-cotangent
  vanishing, and `Algebra.formallySmooth_iff`. None states this full derived
  cotangent bootstrap.
- `msearch.py`, Loogle: `Algebra.TensorProduct.lift, CommRingCat.ofHom,
  CategoryTheory.Tor'`. Zero hits.
- `msearch.py`, Mathlib grep: `cotangent.*bootstrap|cotangentComplex.*[Tt]or|
  diagonalCotangent`. One unrelated hit in
  `Mathlib/RingTheory/Extension/Cotangent/Basic.lean:70`,
  `Cotangent.mk_C_mem_ker_cotangentComplex`.
- `rg` of `WeilConjectures/`, `lean/Sheaf/`, and the upstream declaration index
  for `lem-trf-cotangent-bootstrap|cotangent.*bootstrap|bootstrap.*cotangent`
  found only the proof-plan citation in `EtaleCotangentVanishing.lean`, not
  an existing bootstrap theorem.
- `rg` of Mathlib's tensor-product and algebra sources located
  `Algebra.TensorProduct.lmul'` and its `lmul'_apply_tmul` formula. The draft
  was revised to use this canonical map directly.
- `rg` of the source library, side library and DAG for the proposed helper
  and theorem names (`arrowModule`, `diagonalCotangentArrow`,
  `tensorSquareMultiplication`, `cotangentComplex_isZero_of_tor_and_diagonal`)
  found no existing declarations to duplicate. The unused draft multiplication
  helper was removed in favor of the existing Mathlib construction.

Validation: `scompile.py Q91 lem-trf-cotangent-bootstrap` compiled the sandbox
file and its library-path form cleanly (3.1 s and 2.9 s respectively). The
initial draft's constructor errors were repaired before this validation.
No statement correction, disputed statement, new node, or dependency repair
is needed.

## Second reading by Q91

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
