## Worker report

The module `Sheaf.AlgebraicGeometry.FreeAnnihilatorNonreducedFibres` states
`AlgebraicGeometry.free_annihilator_nonreduced_fibres`. Its sole theorem has proof
`sorry`; no definition, helper theorem, new node, or dependency repair is needed.
Only the item's `lean` field changes. No statement fault or disputed assertion was found.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0575,
`lemma-nonreduced-in-neighbourhood`, especially the paragraph from the short exact sequence
through nonreducedness of each whole fibre (lines 7147–7168 in the source read).
The source uses a flat last term; the already reviewed node deliberately assumes the
stronger, sufficient freeness of that term. This delivery preserves the node unchanged.

Each hypothesis and conclusion is rendered as follows:

- Commutative rings and the specified algebra structure: `{A B : Type u}`,
  `[CommRing A] [CommRing B] [Algebra A B]`.
- Scheme and its morphism to the affine base: `{X : Scheme.{u}}` and
  `(f : X ⟶ Spec (.of A))`.
- The affine open `U = Spec B` is presented by `(i : Spec (.of B) ⟶ X)` with
  `[IsOpenImmersion i]`. An open immersion identifies its source with an open subscheme,
  so this is precisely an affine open chart, with its ring B retained as specified.
- Agreement with the specified A-algebra structure is
  `hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B))`.
  Without this equation the module freeness could concern an unrelated scalar action.
- The element is `(b : B)`; `(hb : IsNilpotent b)` means some positive power vanishes.
  This is equivalent to the node's existence of `n ≥ 1` with `b ^ n = 0`;
  any zero-exponent witness forces a zero ring and also gives a positive witness.
- The quotient C is written without a new alias as
  `B ⧸ Module.annihilator B (Ideal.span ({b} : Set B))`.
  This is Ann(b): annihilating the principal ideal is equivalent to killing b, and
  commutativity changes `x * b = 0` to the node's `b * x = 0`.
  Read `Submodule.mem_annihilator_span_singleton` in Mathlib's `RingTheory/Ideal/Maps.lean`
  (lines 1011–1012), which explicitly supplies this equivalence.
- `C ≠ 0` is the `Nontrivial` instance for that quotient.
- Freeness of C is `Module.Free A` of that quotient. The quotient has the canonical
  A-algebra structure of `Ideal.Quotient.algebra`, induced from the specified A → B.
- The principal quotient D is `B ⧸ Ideal.span ({b} : Set B)`, with hypothesis
  `[Module.Free A (B ⧸ Ideal.span ({b} : Set B))]`. This is B/bB with the same induced
  scalar action. Neither free-module hypothesis has a finite-rank restriction.
- Every field map is `∀ (k : Type (max u v)) [Field k] [Algebra A k]`.
  Algebra structures on a commutative field encode exactly unital homomorphisms A → k.
  The universe includes u, preventing a vacuous quantification over undersized test fields;
  v is arbitrary, so there is no upper bound on the size of a test field.
- The specific image is `b ⊗ₜ[A] (1 : k)` in `B ⊗[A] k`, in the node's factor order.
  Its nonvanishing and nilpotence are respectively `≠ 0` and `IsNilpotent`, joined by `∧`.
- The second conjunct is `∀ t : Spec (.of A), ¬ IsReduced (f.fiber t)`.
  This concerns each whole scheme-theoretic fibre of X, rather than just the chart fibre.
- There are no domain, finite type, Noetherian, finite-basis, or extra nonemptiness binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (scheme and hom structures, and Spec/map signatures and docstrings).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (lines 38–39: the open immersion of locally ringed spaces).
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`
  (lines 43–45: existence of a basis, with unrestricted index type).
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`
  (lines 658–663: scalar extension of a linear map; the recorded dependency also records
  `TensorProduct`, whose pure tensors occur directly in the statement).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`
  (line 38: pullback along the canonical residue-field morphism), with its projections read.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`
  (lines 68–71: reduced sections on every open).

The statement imports these recorded modules publicly. Additional public imports
`Mathlib.RingTheory.TensorProduct.Basic` and
`Mathlib.RingTheory.Ideal.Quotient.Operations` provide the tensor ring and the quotient
A-algebra structures. The already stated proof dependencies are imported non-publicly:
`Mathlib.LinearAlgebra.TensorProduct.Basis` supplies `Module.Basis.baseChange` and
`Module.Basis.baseChange_apply` (signatures and docstrings read at lines 61–75);
`WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor` supplies
`AlgebraicGeometry.affine_fibre_sections_tensor` (entire declaration and docstring read).
The docstring records the node's four proof steps: the annihilator injection and exact
sequence; the basis section and tensor retraction; the nonempty base-changed basis and
surviving nilpotent; the residue-field application and open-section obstruction to
reducedness. No proof dependency import is omitted.

Edge cases checked before writing:

- b = 0 gives Ann(b) = B and the zero quotient C, excluded by exactly the stated C ≠ 0.
- A = 0 or B = 0 likewise cannot satisfy the nontrivial-C hypothesis.
- An empty chart has zero coordinate ring and is excluded by that same hypothesis,
  without adding a nonempty-chart condition.
- A nonempty infinite basis of C is allowed; no finite-rank assumption is introduced.
  The basis of D can be arbitrary, including empty in the abstract free-module predicate.
- All characteristics are allowed: over any field, dual numbers with b = epsilon give
  C = k and D = k, and every field extension retains the nonzero nilpotent.
- Over Z, B = Z[epsilon]/(epsilon²) with b = epsilon has C = D = Z and fits the criterion.
  Replacing b by 2 epsilon gives a nonfree D and vanishes modulo 2, illustrating why
  the D hypothesis matters. No flatness assumption on B was substituted for it.
- The whole-fibre conclusion is separately quantified outside the field quantifier.
  No hypothesis asserting existence of a base point or field map is added.

Searches actually run through `msearch.py`, with their logged results:

- LeanFinder: "A nilpotent survives every field base change if the quotient by its
  annihilator is nonzero free and the quotient by its principal ideal is free, hence all
  scheme fibres are nonreduced". Eight hits, including `Algebra.IsGeometricallyReduced`,
  `AlgebraicGeometry.IsReduced`, and `isNilpotent_tensor_residueField_iff`; no exact match.
- Loogle: `IsNilpotent, TensorProduct`. Three hits:
  `isNilpotent_tensor_residueField_iff`, `PrimeSpectrum.mem_image_comap_basicOpen`,
  and `PrimeSpectrum.mem_image_comap_zeroLocus_sdiff`. The first requires a finite free
  algebra and characterizes nilpotence, not survival via the two quotients; the others
  characterize prime-spectrum images, not this statement. Its full signature and docstring
  were read in `Mathlib/RingTheory/Spectrum/Prime/Polynomial.lean`, lines 40–47.
- Mathlib grep: `annihilator.*[Tt]ensor|[Tt]ensor.*annihilator|nonreduced` in `RingTheory`:
  zero hits reported by the wrapper.
- LeanSearch: "Nonzero free annihilator quotient and free principal quotient imply a
  nilpotent remains nonzero under arbitrary base change to a field". Eight hits, including
  `Module.quotientAnnihilator`, `IsNilpotent.map`, and
  `Submodule.annihilator_quotient`; none states the criterion or its geometric conclusion.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for annihilator and nonreduced
  language found the parent's `NonreducedFibreOpen` and unrelated annihilator results;
  the parent states spreading near a generic point under finite type assumptions, not
  this unrestricted free-quotient criterion. Its statement and source docstring were read.
  A narrower combined annihilator/fibre search found unrelated fibre-module and
  associated-prime lemmas. The item-id search under `lean/WeilConjectures` had no hits.
  `dag/lean_names_upstream.json` had annihilator declarations but no attachment for this item.
  The proposed full declaration name had no hits in Mathlib, WeilConjectures, or Sheaf.

Validation: `scompile.py Q26 lem-trf-free-annihilator-nonreduced-fibres` compiled the file
both as sandbox and library module successfully (13.5 s and 9.3 s), without errors or
unexpected warnings. `autoImplicit` and `relaxedAutoImplicit` are disabled; every universe
and variable is explicitly bound.

## Second reading by Q26

Author's separate rereading of the unchanged node, the complete module, and Tag 0575;
the maintainer supplies the independent review under the direct-dispatch procedure.
The source's final exact-sequence argument is precisely the subargument isolated by this
node, with the node's deliberate D-free specialization retained.

Checked the A/B commutative ring binders, the scheme X and f, the open immersion i, and
especially the equality hi identifying the algebra map. Checked that the annihilator is
of the principal ideal as a B-module, hence kills b itself; the quotient scalar actions
are induced from A → B. Nontrivial C and both independent freeness hypotheses are present,
with no finiteness restriction. Checked that nilpotence is assumed of b, and the first
conclusion is both nonvanishing and nilpotence of that very pure tensor for every field
map. Checked the universe of the test fields includes that of A. The second conclusion
uses f.fiber t, for every point of the full base, with scheme reducedness negated.
No extra ring, scheme, or morphism property is present. Checked the module has one
sorry-only theorem and no extra definitions, that each named dependency's recorded
interface is reused, and that the docstring explains all four proof steps. No mismatch
was found and no statement correction was made.
