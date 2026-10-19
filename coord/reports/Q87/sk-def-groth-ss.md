## Worker report

This is an existing-declaration delivery. No Lean module or theorem is introduced.
The two definitions named by the blueprint already exist upstream, and the final
paragraph concerning double complexes also has its exact existing construction,
including the canonical image filtrations for both spectral sequences. Only the
node's `lean` field changes. Its statement, source, dependencies and status stay
as received. There is no repair note for this item.

Source checked: the complete current blueprint unit
`literature/blueprint/main-20261015/blueprint/sec-picard-framework/sk-def-groth-ss/_section.md`.
It agrees verbatim with the node's statement. There are no statement-dependency
nodes: `stmt_deps` is empty.

The primary binding is
`CategoryTheory.Functor.IsAcyclicComposablePair`, in
`WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`.
The second blueprint-named definition is
`CategoryTheory.SpectralSequence.Abutment`, in
`WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`, publicly
imported by the primary module. `lean.declarations` lists these and the related
acyclic-object, infinity-page and Prop-valued abutment definitions available
through that import. The additional double-complex module is identified in
`lean.note`, with its canonical constructions; it is independently imported in
the scratch validation. No common replacement notion or duplicate definition is
needed.

Each hypothesis and clause is rendered as follows.

1. Categories A and B are Grothendieck abelian, C abelian: the source section
   declares `{A : Type u₁} [Category.{v₁} A] [Abelian A]
   [IsGrothendieckAbelian.{v₁} A]`, the corresponding independent parameters for B,
   and `{C : Type u₃} [Category.{v₃} C] [Abelian C]`. Enough injectives and injective
   resolutions come from the Grothendieck instances. The elaborated acyclicity
   definition does not retain A's unused Grothendieck instance: its predicate
   uses only G's right derived functors. It applies verbatim in the source's
   Grothendieck context and imposes no additional condition on the pair.
2. Composable additive functors: `(F : A ⥤ B) (G : B ⥤ C) [F.Additive]
   [G.Additive]`. There is no left-exactness hypothesis in this definition,
   matching the unit rather than the stronger hypotheses of the later
   Grothendieck spectral-sequence theorem.
3. G-acyclic objects: `G.rightAcyclic B₀`, defined as
   `∀ q : ℕ, IsZero ((G.rightDerived (q + 1)).obj B₀)` in
   `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`.
   The natural indices `q + 1` are exactly all strictly positive degrees.
   `IsZero` is categorical vanishing, appropriate to an arbitrary abelian C.
4. The pair's acyclicity condition is exactly the body of the primary binding:
   `∀ (I : A) [Injective I] (q : ℕ), 0 < q →
   IsZero ((G.rightDerived q).obj (F.obj I))`.
   All injectives are tested, and degree zero is excluded as in the node.
   Mathlib's `Functor.rightDerived` in
   `Mathlib.CategoryTheory.Abelian.RightDerived` is constructed by applying
   the functor to an injective resolution and taking cohomology, as the
   parenthetical explanation of RⁿF, RⁿG and Rⁿ(G∘F) requires.
5. First-quadrant cohomological spectral sequence starting at E₂:
   `(E : E₂CohomologicalSpectralSequenceNat C)` in the abutment signature.
   Its bidegrees are `ℕ × ℕ`, with cohomological differentials `(r, 1-r)`.
6. The stable term is `E.pageInfinity (p,q)`, whose definition is precisely
   `(E.page (p + q + 2 : ℕ)).X (p,q)`.
   Stabilization uses that for `r > max p (q+1)` the incoming differential has
   negative first coordinate and the outgoing differential has negative second
   coordinate. The chosen page satisfies both strict inequalities.
7. The abutment family is `(H : ℕ → C)` in `SpectralSequence.Abutment`.
   Its genuine filtration data is `filtration (n p : ℕ) : Subobject (H n)`.
8. Decreasing filtration: the field `filtration_succ_le (n p : ℕ)` asserts
   `filtration n (p+1) ≤ filtration n p`.
9. The whole-object initial step `F⁰Hⁿ = Hⁿ` is the field
   `filtration_zero (n : ℕ) : filtration n 0 = ⊤`.
10. The endpoint `Fⁿ⁺¹Hⁿ = 0` is
    `filtration_succ_self (n : ℕ) : filtration n (n+1) = ⊥`.
    Monotonicity forces all subsequent steps to vanish, so indexing the
    filtration on every natural p adds no restriction.
11. The quotient identification for every `p+q=n` is the field
    `nonempty_gradedIso (n p q : ℕ) (hpq : p+q=n)`, with type
    `Nonempty (cokernel (Subobject.ofLE _ _ (filtration_succ_le n p)) ≅
    E.pageInfinity (p,q))`.
    In an abelian category this cokernel is exactly `FᵖHⁿ/Fᵖ⁺¹Hⁿ`.
    `Nonempty` expresses the isomorphism assertion in the text; a chosen
    isomorphism can be extracted classically. `AbutsTo E H` is the existence
    of this filtration structure, `Nonempty (E.Abutment H)`.
12. An arbitrary first-quadrant double complex is
    `(K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))`,
    for any abelian C. `K.total (ComplexShape.up ℕ)` is its total complex.
    Each total degree contains only finitely many summands, so no arbitrary
    coproduct assumption is added. The source's `extendNat` extends by zero
    to integer indices, with the proved canonical total-cohomology isomorphism
    `K.totalExtendNatHomologyIso n`.
13. Filtration by either degree:
    `K.extendNat.columnFiltration` and `K.flip.extendNat.columnFiltration`,
    from `WeilConjectures.Algebra.Homology.ExactCouple.TotalComplexFiltration`.
    The definition is the subcomplex inclusion of the totals of columns
    of index at least p. Transposition gives rows.
14. The bigraded exact couple is
    `CategoryTheory.DecreasingFiltration.exactCouple`, in
    `WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex`:
    its D-terms are `Hⁿ(FᵖTot K)` and E-terms are `Hⁿ(grᵖTot K)`;
    the maps are inclusions, quotient maps and connecting maps.
15. Derived couples give the pages: in
    `WeilConjectures.Algebra.Homology.ExactCouple.FirstQuadrant`,
    `ExactCouple.firstQuadrantPage r` uses
    `(X.derivedIter (r-1).toNat).E (p,p+q)` and its differential, and
    `firstQuadrantSpectralSequence` packages their homology identifications.
    Thus `K.firstSpectralSequence` in
    `WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex` is literally
    the sequence of the column filtration's exact couple. Applying it to
    `K.flip` is the other spectral sequence.
16. The first abutment to actual total cohomology is
    `HomologicalComplex₂.firstSpectralSequenceAbutment`:
    `K.firstSpectralSequence.Abutment (fun n ↦ (K.total (up ℕ)).homology n)`.
    Its theorem `firstSpectralSequenceAbutment_filtration (n p : ℕ)` identifies
    the filtration exactly with
    `imageSubobject (HomologicalComplex.homologyMap
    (K.extendNat.columnFiltration.F p).arrow n ≫
    (K.totalExtendNatHomologyIso n).hom)`.
    This is precisely the specified image after the canonical identification
    of the extended total cohomology with total cohomology. It is not an
    unspecified or arbitrarily chosen filtration.
17. The second abutment to the SAME total cohomology is
    `HomologicalComplex₂.flipFirstSpectralSequenceAbutment`:
    `K.flip.firstSpectralSequence.Abutment
    (fun n ↦ (K.total (up ℕ)).homology n)`.
    The corresponding `_filtration` theorem gives the image of
    `HomologicalComplex.homologyMap
    (K.flip.extendNat.columnFiltration.F p).arrow n`, followed by
    `(K.flip.totalExtendNatHomologyIso n).hom` and
    `HomologicalComplex.homologyMap (K.totalFlipIso (up ℕ)).hom n`.
    Thus the row filtration is transported along the canonical signed
    total-flip isomorphism, not left on a different abutment object.
18. Finiteness and automatic convergence are supplied by
    `HomologicalComplex₂.columnFiltration_convergesTo` and
    `columnFiltration_homologyFiltration_F_zero` / `_F_succ` in the total
    filtration module. The only support hypothesis is vanishing when either
    integer coordinate is negative, supplied for `K.extendNat` (and its flip).
    The proof uses that `FᵖTot K` is the whole complex for `p≤0` and its
    degree-n term is zero when `p>n`. The two abutment constructors explicitly
    use these convergence and endpoint results.

Edge cases checked before recording: degree zero gives the required two steps
`F⁰H⁰=H⁰`, `F¹H⁰=0` and quotient E∞⁰⁰=E₂⁰⁰. At `p=0` or `q=0` the stable page
`p+q+2` still kills both possible incident differentials. The zero double
complex and zero functors are allowed. First-quadrant support provides totals
without infinite coproducts; there is no boundedness-in-both-directions or
left-exactness restriction. Objects and morphisms of A, B and C have independent
universes. The abutment lives in `Type (max u v)`, with no smallness restriction
on the abelian category.

Searches performed via `msearch.py` (results retained in `searches.jsonl`):

- LeanSearch: `right acyclic object of an additive functor and spectral sequence
  abutment finite filtration` returned eight hits, including
  `Functor.rightDerived`, `Functor.rightDerivedToHomotopyCategory` and
  `InjectiveResolution.isoRightDerivedObj`; no replacement abutment definition.
- LeanFinder: `Composable additive functors send injective objects to acyclic
  objects; abutment of a first quadrant spectral sequence to a finite filtered
  graded family` returned eight hits, including
  `Functor.isZero_rightDerived_obj_injective_succ`; no exact combined notion.
- Loogle: `Functor.IsAcyclicComposablePair, SpectralSequence.Abutment` returned
  zero hits, with unknown identifier `Functor.IsAcyclicComposablePair` (the
  identifier is upstream project code, not a Mathlib declaration).
- Mathlib grep: `IsAcyclicComposablePair|structure Abutment|G.Acyclic` under
  `Algebra/Homology` returned zero hits.
- Direct source `rg` for `IsAcyclicComposablePair`, `structure Abutment`,
  `sk-def-groth-ss`, `firstSpectralSequenceAbutment` found the primary source
  definitions and existing consumers under `lean/Sheaf`. Searching for the
  `rightAcyclic` definition located the exact acyclic-object predicate above.
- The local old source checkout lacks `ExactCouple/DoubleComplex.lean`.
  Prescribed `scompile.py --source` resolved the live `DoubleComplex`,
  `TotalComplexFiltration`, `FilteredComplex`, `FirstQuadrant` and `Grothendieck`
  sources. Their full signatures, docstrings and construction bodies were read;
  no missing-file workaround or duplicate construction was made.

Validation: `scompile.py Q87 sk-def-groth-ss scratch/ExistingCoverage.lean`
(with the absolute sandbox filename) checked all 17 declarations above using
both upstream imports. It also printed the elaborated acyclicity definition and
all abutment fields. The wrapper reported successful sandbox and library
compilation, 1.6 seconds each, with no errors or warnings. This scratch file is
not part of the delivery; the delivery tool separately checks all names of the
existing binding using only its recorded module.

No new definitions, new nodes, dependency repairs, postponed theorems, statement
corrections or disputed statements are needed. Independent review is performed
by the maintainer as specified in the worker brief.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
