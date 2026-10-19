## Worker report

The module `Sheaf.RingTheory.KoszulQuotientCotangentVanishing` states
`Algebra.KoszulQuotientCotangent.exists_canonical_iso_and_vanishing`.
Its sole theorem proof is `sorry`. The four helper definitions contain real data.
The item node changes only in `lean`; no statement correction or new node is needed.

The statement was checked against Stacks `cotangent.tex`,
`lemma-mod-regular-sequence` (Tag 08SJ), lines 2702–2725, including the
polynomial/Koszul derived-base-change argument. For the word “canonical” I also
read `lemma-surjection` and `equation-comparison-map` at lines 1880–1939.

Hypotheses and clauses, in the node's order:

* A commutative ring R: `(R : Type u) [CommRing R]`, with arbitrary explicit `u`.
* A finite sequence of length r ≥ 0: `(r : ℕ) (f : Fin r → R)`; no positivity
  restriction, proper-ideal restriction or nontriviality instance is imposed.
* Koszul regularity: `hreg : RingTheory.Sequence.IsKoszulRegular f`, exactly
  the recorded definition using homology of the Koszul complex.
* I = (f₁,…,fᵣ): the term `Ideal.span (Set.range f)` throughout the statement.
  B = R/I: the actual quotient `R ⧸ Ideal.span (Set.range f)`.
  `quotientArrow` is literally `Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))`.
* The standard cotangent complex: `cotangentComplex C (quotientArrow R I)` from
  the recorded dependency. `C : Algebra.CotangentResolution.Coherence` is a
  specified standard-resolution model, quantified universally; it is not an
  extra mathematical condition on R or f. The dependency's `exists_coherence`
  supplies it. The inherited instance binder
  `[∀ B : CommRingCat.{u}, HasDerivedCategory.{u+1} (ModuleCat.{u} B)]`
  is the dependency's size/localization infrastructure, available by the standard
  localization construction. No equality of independent ring universes is imposed:
  B is R's quotient, and the actual coefficient ring is bundled explicitly to
  let the inherited localization instance apply.
* In D(B): the objects and isomorphism are in `DerivedCategory (ModuleCat.{u} B)`,
  Mathlib's localization of integer-indexed cochain complexes of ordinary B-modules.
* `(I/I²)[1]`: `(DerivedCategory.singleFunctor (ModuleCat.{u} B) (-1)).obj
  (ModuleCat.of B I.Cotangent)`. `Ideal.Cotangent` is exactly I/I² with its existing
  B-module action. A module concentrated in cochain degree -1 is its degree-zero
  complex shifted by +1 under the recorded derived-category shift convention.
* The canonical conormal identification induces the isomorphism: the first
  conjunct asserts the existence of the isomorphism `e`, together with its
  normalization for **every** `a : I`. It supplies a cycle `z` whose image under
  `iCycles (-1)` is `relationVector C R I a`, and requires
  `conormalHomologyMap C R I e (homologyπ (-1) z) = I.toCotangent a`.
  The vector is explicitly `1 ⊗ d([C(a)] - [0])` in the standard differential
  complex's degree -1, using the equality of the dependency's standard term with
  the specified iterated polynomial ring, not an arbitrary representative.
  Its first polynomial face is a, its second is zero because a ∈ I; their
  differentials vanish. This is the standard relation representing a mod I²
  in the surjection conormal comparison. `conormalHomologyMap` only composes the
  existing localization homology comparison, H⁻¹(e), and the single-complex
  homology comparison. Thus the theorem specifies the identification on actual
  conormal classes, including cycle existence; it is not a bare isomorphism.
  These classes generate H⁻¹ by the surjection conormal comparison, so the
  normalization specifies the canonical identification.
* Vanishing: the second conjunct is `∀ i : ℤ, i ≠ -1 → IsZero
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj ... )`.
  This includes positive degrees, degree zero, and all degrees below -1.
* No Noetherian hypothesis: none appears in the signature or the constructions.

Dependency declarations read and used:

* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.singleFunctor`.
* `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `cotangentComplex`,
  `differentialComplex`, `complexGenerator`, and `Coherence.standard_spec`.
  I read the full dependency module, including the formula specifying the faces,
  standard terms, differential generators, and `exists_coherence` signature.
* `Sheaf.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`, read with its full signature/docstring.
* Existing Mathlib conormal data: `Mathlib.RingTheory.Ideal.Cotangent`,
  `Ideal.Cotangent` and `Ideal.toCotangent`, with their existing quotient action.
* `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`:
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`; its imported
  `homologyFunctorFactors` supplies the concrete-to-derived comparison.
* Already stated proof dependencies are ordinary, non-public imports:
  `Sheaf.RingTheory.KoszulConormalBasis`,
  `ExteriorAlgebra.exists_koszul_conormal_basis`; and
  `Sheaf.RingTheory.KoszulDerivedQuotient`,
  `RingTheory.KoszulDerivedQuotient.isIso_comparison`. Their signatures and
  docstrings were read. The two proof-only nodes
  `lem-trf-cotangent-flat-base-change` and
  `lem-trf-cotangent-polynomial-special-case` have no recorded Lean module, so
  there is no module to import yet. They are not needed to type this statement;
  their precise roles remain in the theorem's complete four-step proof docstring.

Edge cases checked before writing: r = 0 (empty range, I = 0, B = R, the conormal
module is zero); R the zero ring; I = R, including a sequence containing a unit
(B and its module category are zero); arbitrary characteristic and non-Noetherian
rings. Every case remains in the signature. The target single complex has its
module in degree -1, so the sign of the displayed shift and the exceptional
cohomology degree agree. Normalization uses all a ∈ I, including a = 0, and
asserts actual cycle existence rather than assuming it or using an implication
with an uninhabited antecedent.

Searches made with the prescribed wrapper:

* LeanFinder: `cotangent complex of a quotient by a Koszul regular sequence is
  the conormal module shifted by one` — eight hits, including
  `Algebra.SubmersivePresentation.cotangentEquiv`, presentation differential maps,
  and `Algebra.H1Cotangent`. None is the full derived cotangent assertion.
* Loogle: `Ideal.Cotangent, Algebra.H1Cotangent` — one result,
  `Algebra.FormallySmooth.kerCotangentToTensor_injective_iff`, not a match.
* Mathlib grep: `cotangent.*regular|regular.*cotangent` in `RingTheory` — four
  regular-local-ring cotangent-space dimension references, no match.
* LeanSearch: `cotangent complex quotient Koszul regular sequence conormal module
  shifted one` — eight hits. `Ideal.Cotangent` and its quotient-ring action are
  the existing conormal notion and are used directly. The other results concern
  naive first homology, exact sequences or kernels, not the full complex.
* `rg` on the source `WeilConjectures` and project `lean/Sheaf`:
  `cotangent.*[Kk]oszul|[Kk]oszul.*cotangent|lem-trf-koszul-quotient-cotangent-vanishing`
  — only conormal vector uses in two Koszul dual/roof modules; no cotangent-complex
  theorem. The item id has no upstream match. Searching all five proposed
  declaration names found no same-name declaration (an unrelated plural
  `quotientModels` was the only textual hit). The upstream name index was also
  searched for cotangentComplex/IsKoszulRegular; its unrelated scheme
  symmetric-algebra cotangent declaration is not this statement.

No node fault or disputed statement was found. No definition is selected from
an unspecified existence theorem. The isomorphism and cycle representatives
are asserted by the theorem, not used to define mathematical data.

Validation: `scompile.py Q98 lem-trf-koszul-quotient-cotangent-vanishing` compiled
both sandbox and library-module forms cleanly (1.8 s and 2.0 s). An initial
elaboration issue was repaired by qualifying `_root_.cast` and retaining explicit
`CommRingCat.of` bundles for the inherited localization instance; no mathematical
hypothesis or universe restriction changed.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
