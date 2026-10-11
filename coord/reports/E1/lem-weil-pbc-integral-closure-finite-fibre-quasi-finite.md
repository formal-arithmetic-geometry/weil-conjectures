## Worker report

The module `Sheaf.RingTheory.FiniteQuotientComponentQuasiFinite` states
`Algebra.isQuasiFiniteAtPrime_of_finite_quotient_component`, with one `sorry` and no new
definitions. The original node and its dependencies are unchanged except for its `lean` record.
No statement correction, dependency repair, or new node is needed.

Source checked: https://stacks.math.columbia.edu/tag/09XH, the first sentence of the proof
of Lemma 15.11.5. The local literature file is not present on this machine; the source was
read at the official Stacks site. That sentence has precisely the finite-type and finite
quotient-factor hypotheses of this node. Tags 00PL and 00PK are represented by the already
landed definition, whose signature and complete docstring were read.

Hypothesis and clause correspondence:

- Commutative rings A, B and the ring map φ are `(A : Type u) (B : Type v)` with
  `[CommRing A] [CommRing B] [Algebra A B]`; φ is `algebraMap A B`. An arbitrary ring map
  is represented by its `RingHom.toAlgebra`, so this excludes no ring map.
- Finite type is `[Algebra.FiniteType A B]`, exactly finite generation as an A-algebra.
- The ideal I is `(I : Ideal A)`; the extended ideal IB is `I.map (algebraMap A B)`.
- The quotient product decomposition is
  `(e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A] (C₁ × C₂))`.
  The factor rings have separate universe variables w and z and `CommRing` instances.
  Their A-algebra structures are precisely those induced by φ and the two projections;
  the algebra equivalence expresses this compatibility, rather than an unrelated product.
- Finiteness of C₁ over A/I is `[Module.Finite (A ⧸ I) C₁]`, with
  `[Algebra (A ⧸ I) C₁] [IsScalarTower A (A ⧸ I) C₁]`. The scalar tower requires its
  restricted A-action to be the one occurring in e. This is exactly the quotient-induced
  action specified in the node. These structures are available for every decomposition
  in the node; no finite-type or finiteness hypothesis is imposed on C₂.
- The idempotent ε is `e.symm (1, 0)`; it needs no extra binder or new definition.
  Its corner with identity ε identifies with C₁ under e. Multiplication by ε has first
  coordinate unchanged and second coordinate zero, so the map to that corner is precisely
  the first projection used below. The module docstring explains this identification.
- The displayed local `π : B →+* C₁` is `RingHom.fst C₁ C₂` composed with `e.toRingHom`
  and `Ideal.Quotient.mk (I.map (algebraMap A B))`. It is exactly b ↦ ε b-bar in the
  first factor, not an arbitrary map to C₁.
- `T : Set (PrimeSpectrum B) := Set.range (PrimeSpectrum.comap π)` is exactly the set
  of contractions of primes of C₁. Its primes automatically contain IB.
- “For every q in T” is `∀ q : PrimeSpectrum B, q ∈ T → ...`.
- The conclusion `IsQuasiFiniteAtPrime A B q` is the recorded dependency declaration.
  Unfolding it sets `p := q.comap (algebraMap A B)` and asks that the singleton of
  `PrimeSpectrum.preimageHomeomorphFiber A B p ⟨q, rfl⟩` be open in
  `PrimeSpectrum (p.asIdeal.Fiber B)`. This renders every clause concerning p, κ(p),
  the corresponding unique fibre prime, and its isolation. `Ideal.Fiber` uses
  κ(p) ⊗[A] B, canonically the factor-swapped tensor in the node.
- The final reference to scheme quasi-finiteness is explanatory, not an additional
  scheme conclusion. No independent scheme predicate is introduced or imported.

Dependency declarations read and used:

- `def-weil-pbc-ring-map-quasi-finite-at-prime`: `Sheaf.RingTheory.QuasiFiniteAtPrime`,
  `Algebra.IsQuasiFiniteAtPrime`, imported directly and used in the conclusion.
- `def-weil-pbc-localization-at-prime`: Mathlib `Localization.AtPrime`,
  `Ideal.ResidueField`, `Ideal.Fiber`, read in their recorded files. They are used
  through the recorded predicate; its import provides the fibre construction.
- `def-weil-affine-spectrum`: Mathlib `AlgebraicGeometry.Spec`, `Spec.map`, and
  `Spec.homEquiv` signatures/docstrings read in Scheme and GammaSpecAdjunction.
  This ring-level statement uses their underlying space `PrimeSpectrum` and underlying
  map `PrimeSpectrum.comap`; it has no scheme-valued conclusion needing a Spec import.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, all four recorded
  `Scheme.Hom` predicates were read. The node cites it only to explain the affine notion;
  the exact ring predicate above is the operative dependency, so no unused scheme import.

Edge cases checked before writing:

- I = top makes B/IB the zero ring and hence both factors zero; T is empty and the
  universal conclusion is vacuous. The theorem requires no nontriviality instance.
- C₁ = zero ring likewise gives empty T, with the zero module finite.
- C₂ = zero ring, I = bottom, and zero rings A or B are allowed. When primes exist the
  recorded fibre-prime construction uses their prime instances, without assuming domains.
- No Noetherian, reduced, normal, characteristic, henselian-pair, or integral-closure
  assumption was added. The source observation applies to any pair (A, I).
- A, B, C₁, C₂ have independent explicit universes u, v, w, z; all variables are bound.

Searches for an existing statement (run via the prescribed msearch.py, recorded in searches.jsonl):

- LeanFinder: `finite type algebra quasi finite at primes of a finite direct factor of
  a quotient by an ideal`: eight hits, including Algebra.QuasiFiniteAt,
  Algebra.quasiFinite_iff, quotient quasi-finiteness, and finite-primes-over criteria;
  none combines a finite quotient product component with quasi-finiteness on its image.
- Loogle: `Algebra.QuasiFiniteAt, Ideal.Quotient`: zero hits; Ideal.Quotient is not an
  identifier accepted by Loogle. LeanFinder and textual search supply useful coverage.
- LeanSearch: `finite type ring map quasi finite on finite direct factor of quotient
  algebra`: service unavailable (Internal Server Error), recorded without a match verdict.
- Mathlib grep: `QuasiFiniteAt.*(quotient|prod)|finite.*component|quasiFinite.*(quotient|prod)`
  in RingTheory: eleven hits, concerning weak quasi-finiteness of other quotients,
  Zariski's main theorem, and unrelated graded/isotypic components; no exact statement.
- Source and project rg: `finite.*[Cc]omponent|quasiFiniteAt.*(quotient|prod)|IsQuasiFiniteAtPrime|finite_fibre_quasi`.
  The project contains the recorded predicate and related general finite-map/étale
  criteria, but none states the finite quotient-component theorem. The upstream source
  has only unrelated finite-component results. Literal node-id grep in WeilConjectures
  returns no match. The selected declaration name is new.

Validation: scompile.py compiled the module on the server, exit 0, in 1.4 seconds,
with no warnings or errors. All seven DAG proof steps are included in the theorem
 docstring, including their non-elementary dependency node ids. Only the theorem proof
is `sorry`; nothing is proved and no data depends on a placeholder.

## Second reading by E1

I reread the node statement and the theorem signature item by item.

- The node's ring map \(\varphi:A\to B\) is rendered by `[CommRing A] [CommRing B]
  [Algebra A B]`, with `algebraMap A B` used in the quotient ideal and in the fibre
  predicate. No Noetherian, domain, characteristic, or nonzero assumptions are added.
- Finite type is exactly `[Algebra.FiniteType A B]`.
- The ideal \(I\subseteq A\) is `(I : Ideal A)`, and `IB` is
  `I.map (algebraMap A B)`.
- The product decomposition is the displayed
  `(e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A] (C₁ × C₂))`; the separate `CommRing`
  and algebra instances introduce the two factors. The quotient algebra on `C₁`, its
  scalar tower with `A`, and `[Module.Finite (A ⧸ I) C₁]` render precisely that the
  first factor is finite over `A/I`; the `AlgEquiv` over `A` enforces compatibility
  with the original map.
- The idempotent \(\varepsilon=(1,0)\) is represented by `e.symm (1, 0)` in the
  explanatory docstring. The map \(\pi:B\to C₁\) is exactly the composition in the
  `let π` clause: quotient map, `e.toRingHom`, and `RingHom.fst`.
- `T` is exactly `Set.range (PrimeSpectrum.comap π)`, so its elements are the inverse
  images of primes of `C₁`, as in the node.
- The conclusion has the same quantifier order,
  `∀ q : PrimeSpectrum B, q ∈ T → IsQuasiFiniteAtPrime A B q`. The recorded
  dependency defines the corresponding contracted prime and isolated point of the
  fibre spectrum, so no conclusion clause is omitted or strengthened.

The edge cases are covered: `I = ⊤`, either factor zero, and zero rings make the
universal statement vacuous where appropriate; `C₂ = 0`, `I = ⊥`, existing primes,
and all independent universes remain allowed. No characteristic or finiteness
condition beyond the stated finite factor is hidden in the signature.

I searched Mathlib RingTheory, the upstream `WeilConjectures` tree, and this
project's `lean/Sheaf` tree, and ran LeanFinder, Loogle, and LeanSearch searches
(the LeanSearch service returned no match). They contain general `QuasiFiniteAt`
and fibre criteria but no finite quotient-component theorem. The dependency
`Sheaf.RingTheory.QuasiFiniteAtPrime` was read and is used directly; no private
copy or second definition is present.

No mismatch was found between the node and Lean, so no source, statement, or
module repair was needed. The module compiled cleanly on the server with only the
intended theorem `sorry`.

## Reviewer fix (R-icq1141)

The delivered signature (`[Algebra A C₁] [Algebra A C₂] [IsScalarTower A (A ⧸ I) C₁]`,
`e : B/IB ≃ₐ[A] C₁ × C₂`) was equivalent to the node but a second spelling of the finite
quotient-component hypothesis. Restated in the landed sibling's form (J1 c634916b4,
lem-weil-pbc-integral-closure-finite-fibre-image-clopen): `[Algebra (A ⧸ I) C₁]
[Module.Finite (A ⧸ I) C₁] (e : B/IB ≃+* C₁ × C₂)` with `hcompat : ∀ a, algebraMap (A ⧸ I)
C₁ (mk a) = (e (mk (algebraMap A B a))).1`, which pins the A/I-structure to A/I → B/IB → C₁
(mk surjective). The redundant A-algebra structures on C₁, C₂ are gone; π, T and the
conclusion are unchanged. Recompiled clean.
