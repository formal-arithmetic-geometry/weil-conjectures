## Worker report

Item: `lem-trf-cotangent-polynomial-special-case` (Q36, stage 2).
The new module `Sheaf.RingTheory.PolynomialAugmentationCotangent` states
`Algebra.PolynomialAugmentationCotangent.exists_canonical_iso_and_basis`.
Its only postponed proof is this named theorem, with the node's five-step proof
and source in its docstring. All five helper definitions contain actual data.
No node statement, dependency, or proof is changed; only the item's `lean` field
is attached. There are no new nodes or dependency repairs.

Source checked directly: `literature/stacks-project/cotangent.tex`,
`lemma-special-case` (Tag 08SI), its transitivity proof, and
`lemma-surjection` with `equation-comparison-map` for the conormal normalization.
The source proves the derived identification, rather than only a per-degree
cohomology identification.

Hypothesis and clause correspondence:

- `n ≥ 0`: `(n : ℕ)` covers exactly all finite nonnegative numbers, including zero.
- `P = ℤ[x₁,…,xₙ]`: `MvPolynomial (Fin n) ℤ`. The zero-based `Fin n` labels
  relabel the same n variables; there is no change to the polynomial ring.
- `B = ℤ`, with each variable mapped to zero: `augmentationArrow n` is
  `Arrow.mk (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id ℤ)
  (fun _ : Fin n ↦ 0)))`. It fixes every integer coefficient and sends every
  variable to zero. The codomain is the actual integer ring, not an unrelated
  quotient or an arbitrary algebra.
- `J = (x₁,…,xₙ)`: `augmentationIdeal n` is Mathlib's
  `Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ))`.
- The specified standard cotangent complex is
  `Algebra.CotangentResolution.cotangentComplex C (augmentationArrow n)`.
  The explicitly bound `C : Coherence.{0}` supplies the dependency's actual
  standard polynomial resolution and its generator-normalized differential
  model. No alternate cotangent complex is defined. The section instance
  `[∀ B : CommRingCat.{0}, HasDerivedCategory.{1} (ModuleCat.{0} B)]` is
  the dependency's localization-size infrastructure, not a ring-theoretic
  hypothesis; the theorem holds for each such choice and every `C`.
- `J/J²` is exactly Mathlib's `(augmentationIdeal n).Cotangent`, the quotient
  of the ideal by its square submodule, with its canonical integer action.
  Since `B = ℤ`, this is precisely the B-module action transported along
  the augmentation quotient `P/J ≃ ℤ`: every integer acts by repeated addition.
- The asserted isomorphism in `D(B)` is the existentially bound isomorphism
  `e : cotangentComplex C (augmentationArrow n) ≅
  (DerivedCategory.singleFunctor (ModuleCat.{0} (CommRingCat.of ℤ)) (-1)).obj
  (ModuleCat.of ℤ (augmentationIdeal n).Cotangent)`.
  A module in cochain degree -1 is its degree-zero complex shifted by `[1]`,
  with the sign/shift convention of the recorded derived-category dependency.
- Canonicity is expressed by the rest of the existential clause, not by a bare
  unspecified `Nonempty` isomorphism: for every `a : augmentationIdeal n`,
  the standard vector `relationVector C n a` has a cycle lift `z`, and the
  induced degree -1 homology map sends `homologyπ (-1) z` to `J.toCotangent a`.
  `relationVector` is the actual tensor generator
  `1 ⊗ d([C(a)] - [0])` in the recorded standard resolution, transported using
  `C.standard_spec`. Its two faces have zero relative differential.
  `conormalHomologyMap` uses the existing derived homology comparison and
  the single-complex homology isomorphism to state this equality in the actual
  module `J/J²`. This is the surjection conormal normalization from the source.
  These classes generate degree -1 homology; with the isomorphism to a single
  module this fixes the derived isomorphism. It is the same normalization used
  by the already landed Koszul-quotient consumer, specialized here to the actual
  augmentation `P → ℤ`, rather than its different arrow `P → P/J`.
- The classes of the variables form a B-basis: the next conjunct supplies
  `b : Module.Basis (Fin n) ℤ (augmentationIdeal n).Cotangent`, with
  `b i = (augmentationIdeal n).toCotangent
  ⟨MvPolynomial.X i, Ideal.subset_span ⟨i, rfl⟩⟩` for every variable.
- Both sides zero for `n = 0`: the final conjunct is
  `n = 0 → IsZero (cotangentComplex C (augmentationArrow n)) ∧
  IsZero ((DerivedCategory.singleFunctor ... (-1)).obj
  (ModuleCat.of ℤ (augmentationIdeal n).Cotangent))`.
  Thus the zero case is asserted for both derived objects, not merely mentioned
  in prose or obtained by silently imposing `0 < n`.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `cotangentComplex`,
  `differentialComplex`, `complexGenerator`, and the fields `standard`,
  `standard_spec`, `differentials`; its main `exists_coherence` and proof
  docstring were also read. Public import for the statement's standard model.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `HasDerivedCategory`, `DerivedCategory`, and `DerivedCategory.Q` (available
  through the public dependencies). The homology comparisons used are
  `DerivedCategory.homologyFunctorFactors` and
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`; the latter comes
  from the public import `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`.
- `Sheaf.RingTheory.CotangentTransitivityTriangle`:
  `Algebra.CotangentResolution.exists_transitivity_triangles` (plain proof import).
  Its prescribed first and second arrows, boundary and diagram naturality were read.
- `Sheaf.RingTheory.PolynomialCotangentIdentification`:
  `Algebra.CotangentResolution.polynomial_augmentation_isIso` (plain proof import),
  including `DifferentialAugmentation.generator` and its full localization clause.
- `Mathlib.RingTheory.Kaehler.Polynomial`:
  `KaehlerDifferential.mvPolynomialBasis`, `mvPolynomialBasis_apply`,
  `mvPolynomialBasis_repr_apply` (plain proof import). This dependency has
  `status: mathlib` and no `lean` record: its `mathlib_match` is used directly.
- `WeilConjectures.RingTheory.RegularSequenceConormal`:
  `RingTheory.Sequence.regularSequence_conormal_free` (plain proof import),
  with its actual basis-vector equation and free-module conclusion.
- `Mathlib.RingTheory.Ideal.Cotangent`: existing `Ideal.Cotangent` and
  `Ideal.toCotangent`, publicly imported; no new conormal module definition.

Edge cases checked mathematically before drafting:

- Empty variable set (`n = 0`): the ideal generated by the empty range is zero,
  its conormal module is zero, and the polynomial augmentation is an isomorphism
  to ℤ. The standard cotangent complex is zero; its integer basis is empty.
- One variable: the target conormal module is `(x)/(x²)` with basis `[x]`,
  so the derived target is one copy of ℤ in degree -1, not degree +1 or zero.
- Every `a ∈ J`, including zero and elements of `J²`, is covered by the
  normalization. For elements of `J²` the resulting conormal class is zero.
- Integer scalars are fixed by the augmentation; no field, characteristic,
  Noetherian, flatness, regularity, or positive-length hypothesis was added.
- All objects here are concrete small types (`ℤ`, `Fin n`, finite polynomial
  rings); universe 0 excludes none of the node's rings or variable sets.
  The localization morphism universe 1 is exactly the recorded standard-model API.

Searches for an existing declaration (all on 2026-10-22):

1. `msearch.py ... leanfinder` query:
   `cotangent complex of the augmentation from an integer polynomial ring to integers is the conormal module shifted by one`.
   Eight hits: `Algebra.Extension.cotangentComplex_mk`,
   `Algebra.SubmersivePresentation.cotangentEquiv_apply`,
   `Algebra.Extension.cotangentComplex`,
   `Algebra.PreSubmersivePresentation.cotangentComplexAux`,
   `Algebra.Extension.H1Cotangent`, `KaehlerDifferential.quotientCotangentIdeal`,
   `Algebra.H1Cotangent`, `KaehlerDifferential.quotientCotangentIdealRingEquiv`.
   These are ordinary conormal/differential maps or H1, not this full derived statement.
2. `msearch.py ... loogle` query `Ideal.Cotangent, MvPolynomial.eval`:
   zero hits.
3. `msearch.py ... grep` query
   `cotangent.*[Pp]olynomial|[Pp]olynomial.*cotangent|special.case`,
   subdirectory `RingTheory`: 25 hits, mostly unrelated special-case comments;
   relevant conormal/differential code does not state the derived augmentation result.
4. `msearch.py ... leansearch` query
   `cotangent complex of the polynomial augmentation Z[x_1,...,x_n] to Z is the conormal module in degree minus one`.
   Eight hits include `Ideal.Cotangent`, its quotient-module instance,
   `Algebra.Extension.Cotangent`, `Algebra.Extension.CotangentSpace`,
   `IsLocalRing.CotangentSpace`, and `Algebra.Extension.H1Cotangent`.
   Reused `Ideal.Cotangent`; no complete derived result found.
5. `rg` of `lean/WeilConjectures` for `CotangentResolution|cotangentComplex`
   and for polynomial/conormal combinations found ordinary presentation and
   H1 calculations, not this derived statement; an exact item-id search found
   no upstream declaration. `rg` of `lean/Sheaf` found the recorded standard
   resolution, polynomial identification, and the Koszul-quotient consumer's
   prose reference to this item, but no statement of the polynomial case.
   `NaiveCotangentComparison` was also read: it is a general presentation
   comparison with a different two-term target; it does not state this result.
   Searches for `PolynomialAugmentationCotangent`,
   `polynomial_augmentation_conormal`, `augmentationIdeal`, and
   `polynomialAugmentation` in the live sources and `dag/lean_names_upstream.json`
   found no name collision.

Validation: compiled the entire delivered module using the prescribed
`scompile.py`, in both sandbox and library module modes. An initial missing
variable-type annotation and bundled-ring typeclass inference issue were repaired;
a subsequent line-width warning was repaired. The final file has explicit binders,
`set_option autoImplicit false`, no file-local notation or instance, and no data
chosen from a postponed existence proof. The only `sorry` is the named main theorem.

No `STATEMENT-DISPUTED` issue or source discrepancy was found. The original node
statement remains unchanged. The worker delivers directly; the maintainer supplies
the independent review, as required by the dispatcher's current brief.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
