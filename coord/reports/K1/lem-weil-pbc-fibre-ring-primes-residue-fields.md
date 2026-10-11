## Worker report

The module `Sheaf.RingTheory.FibrePrimesResidueFields` states
`PrimeSpectrum.fibre_primes_residue_fields`, with one `sorry` and no new definitions.
The node is unchanged except for its `lean` record. No statement correction, disputed
statement, new node or dependency module is needed.

Hypotheses and objects, clause by clause:
- Arbitrary commutative rings A and B: `(A : Type u) (B : Type v) [CommRing A]
  [CommRing B]`, with independently explicit universes.
- The ring homomorphism φ: `[Algebra A B]`, with φ rendered as `algebraMap A B`.
  An arbitrary ring homomorphism gives precisely this algebra structure via
  `RingHom.toAlgebra`; no finiteness or injectivity is imposed.
- The prime p: `(p : PrimeSpectrum A)` bundles the ideal and its primality.
- κ(p) and κ(q): `p.asIdeal.ResidueField` and `q.1.asIdeal.ResidueField`, exactly
  Mathlib's residue field of the localization at the prime, modulo its maximal ideal.
- C = B ⊗_A κ(p): the local abbreviation `C := B ⊗[A] p.asIdeal.ResidueField`.
  This keeps the node's factor order; Mathlib `Ideal.Fiber` uses the opposite order,
  canonically exchanged by `Algebra.TensorProduct.comm`.
- j(b) = b ⊗ 1: `j := Algebra.TensorProduct.includeLeft.toRingHom`.
- Primes q with φ⁻¹(q) = p: the subtype `F` of `PrimeSpectrum B` with
  `q.asIdeal.comap (algebraMap A B) = p.asIdeal`.
- The induced κ(p) → κ(q): `Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal
  (Algebra.ofId A B) q.2.symm`.
- ψ_q(b ⊗ λ) = b̄ λ̄: `Algebra.TensorProduct.lift` of
  `IsScalarTower.toAlgHom A B q.1.asIdeal.ResidueField` (the canonical B → κ(q))
  and that induced residue-field map. `Commute.all` supplies commutativity of the
  target ring; it is not an additional hypothesis.

Conclusions, clause by clause:
- (1) A bijection, preserving and reflecting inclusions: `∃ e : PrimeSpectrum C ≃o F`.
  The order on `PrimeSpectrum` is ideal inclusion and the subtype inherits it.
- Its forward map is j⁻¹: `∀ Q, (e Q).1.asIdeal = Q.asIdeal.comap j`.
- Its inverse sends q to ker ψ_q: `∀ q, (e.symm q).asIdeal = RingHom.ker (ψ q)`.
- (2) At Q = ker ψ_q the residue field is isomorphic to κ(q):
  `∀ q, ∃ θ : (e.symm q).asIdeal.ResidueField ≃+* q.1.asIdeal.ResidueField`.
  The preceding inverse-map equality identifies Q exactly. A ring equivalence of
  these fields is an isomorphism of fields, with no extra choice of scalar structure.
- The isomorphism is induced by ψ_q, including the node's final compatibility clause:
  `θ.toRingHom.comp (algebraMap C (e.symm q).asIdeal.ResidueField) = ψ q`.
  Thus no arbitrary abstract field isomorphism substitutes for the prescribed map.

Dependency declarations read and used:
- `def-weil-pbc-localization-at-prime`: Mathlib leaves `Localization.AtPrime`
  (`Mathlib.RingTheory.Localization.AtPrime.Basic`), `Ideal.ResidueField`
  (`Mathlib.RingTheory.LocalRing.ResidueField.Ideal`) and `Ideal.Fiber`
  (`Mathlib.RingTheory.LocalRing.ResidueField.Fiber`). The latter module is the
  sole import; it provides the canonical tensor-product and prime-spectrum notions.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` in `Mathlib.AlgebraicGeometry.ResidueField`.
  These supply the scheme interpretation in the parenthetical last sentence;
  no scheme occurs as an extra object in this ring-theoretic statement.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme` and `Spec.homEquiv` in
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` were read. The primes are rendered
  directly as `PrimeSpectrum` points. `AlgebraicGeometry.Spec.residueFieldIso`
  in `Mathlib.AlgebraicGeometry.ResidueField` identifies the scheme residue field
  at each such point with the `Ideal.ResidueField` used here. No unused scheme
  import is added solely for that interpretation.

Source: read Stacks Tag 00E6 at https://stacks.math.columbia.edu/tag/00E6 and
`remark-fundamental-diagram` in `/home/ubuntu/c1-stacks-review/algebra.tex`;
read Tag 0H9M's `remark-local-ring-fibre` in that same local Stacks source,
lines 3520–3538 (web access to 0H9M failed). These give the fibre prime
correspondence and the localized fibre quotient. The docstring carries the node's
five proof steps and their named dependencies, including compatibility on both
sets of tensor generators. No proof is attempted in stage 2.

Edge cases checked: A = 0 has no prime p, so no invalid residue field is formed.
B = 0 and, more generally, a zero fibre give empty prime spectra and empty F;
an order isomorphism between these empty types is allowed, and the field clause
is vacuous. Non-maximal primes are included, since no maximality is required.
Noninjective maps, rings with nilpotents, all characteristics and independent
ring universes are allowed. No nontriviality assumption on B or C is introduced.

Searches (all run for this item through `/home/ubuntu/weil-launcher/msearch.py`):
- `leanfinder`: “primes of a tensor product fibre ring correspond to primes lying
  over a prime with the same residue fields”. Eight hits, notably
  `PrimeSpectrum.preimageEquivFiber`, `preimageOrderIsoFiber` and their kernel
  formulae; `Ideal.fiberIsoOfBijectiveResidueField` is a different base-change
  result. No declaration states both clauses and the compatibility together.
- `loogle`: `Ideal.ResidueField.map, Algebra.TensorProduct.lift`: zero hits.
- `grep` in `RingTheory/LocalRing/ResidueField`:
  `residueFieldMap_bijective|preimageOrderIsoFiber|residueField.*[Ee]quiv`: sixteen
  hits. Read Fiber.lean in full through the order correspondence, and Ideal.lean
  including `Ideal.ResidueField.map`, `mapₐ`, `RingHom.SurjectiveOnStalks.residueFieldMap_bijective`,
  and residue-field equivalences. These provide components, not the entire statement.
- `leansearch`: “residue fields of fibre rings and primes lying over”: unavailable,
  Internal Server Error (not a no-match verdict).
- `rg` in upstream `WeilConjectures`, the project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: `fibre.*residue|fiber.*residue|primes.*[Ff]iber|
  lem-weil-pbc-fibre-ring-primes-residue-fields`. Hits concern other fibre statements
  or docstring references to this node, not its full statement.
- Exact declaration-name collision search in Mathlib, upstream, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: `fibre_primes_residue_fields|fiber_primes_residue_fields`:
  no matches. The upstream node-id search found no declaration for this item.

Validation: server single-file compilation via `scompile.py`; delivery preflight
via `deliver2.py --no-push`. The second reader supplies the second-reading section.

## Second reading by K1

I reread the node statement, its Stacks source places (Tags 00E6 and 0H9M), and
`Sheaf.RingTheory.FibrePrimesResidueFields` item by item. The Lean rendering and
verdict are as follows.

- The arbitrary commutative rings and independent universes are `(A : Type u)` and
  `(B : Type v)` with `[CommRing A] [CommRing B]`; this matches the node.
- The homomorphism is represented by the supplied `[Algebra A B]` and its
  `algebraMap A B`; this is the standard unital ring-hom formulation and adds no
  finiteness, injectivity, characteristic, or Noetherian hypothesis.
- The chosen prime is `p : PrimeSpectrum A`, and the residue field is
  `p.asIdeal.ResidueField`; the subtype `F` contains exactly `q` satisfying
  `q.asIdeal.comap (algebraMap A B) = p.asIdeal`.
- `C := B ⊗[A] p.asIdeal.ResidueField` and
  `j := Algebra.TensorProduct.includeLeft.toRingHom` render the fibre and
  `b ↦ b ⊗ 1` with the same factor order as the node.
- The dependent `ψ` is the tensor lift of
  `IsScalarTower.toAlgHom A B q.1.asIdeal.ResidueField` and
  `Ideal.ResidueField.mapₐ ... q.2.symm`; hence it sends `b ⊗ λ` to the residue
  of `b` times the induced residue of `λ`, exactly as specified. `Commute.all` is
  only the commutativity proof required by `TensorProduct.lift`, not a hypothesis.
- `e : PrimeSpectrum C ≃o F` gives the bijection and preserves and reflects
  inclusions. The first conjunct states its forward contraction formula, and the
  second states the inverse formula `ker (ψ q)`, in the node's order.
- The final conjunct quantifies every `q`, gives a ring equivalence
  `κ(e.symm q) ≃+* κ(q)`, and requires its underlying map composed with
  `algebraMap C κ(e.symm q)` to equal `ψ q`. This is precisely the prescribed
  residue-field compatibility, not an arbitrary field isomorphism.

No mismatch was found and no source or dependency correction was needed. The
statement covers the empty spectrum (including a zero fibre) because the order
isomorphism is between the corresponding empty types and the residue-field
clause is vacuous; it imposes no maximality, injectivity, nonzero-ring,
characteristic, or finiteness assumptions and permits all listed universes.
The zero base has no prime `p`, so the universally quantified theorem has no
invalid instance. I also checked that `n = 0` is irrelevant: the node has no
such parameter.

I repeated the three-definition searches: LeanFinder and Loogle searches for
the combined fibre-prime/residue-field statement, grep through Mathlib's
`ResidueField/Fiber` files, grep through `WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json`, and an exact declaration-name search. Mathlib's
`preimageOrderIsoFiber` and related lemmas cover only the prime correspondence;
no existing declaration states both clauses and the required compatibility, so
the module is correctly new and uses the recorded dependency notions.

The module compiled cleanly with `scompile.py`; it contains only the required
statement proof `sorry`, with no proved theorem or hollow definition.

## Reviewer fix (R-frp1010)

H4/H12 (one definition per notion): the fibre ring was a private `B ⊗[A] κ(p)` with
`includeLeft`; the project's fibre ring is Mathlib's `p.asIdeal.Fiber B = κ(p) ⊗[A] B` with
`j = includeRight` (as landed G1 e8f0036eb `Fiber.localRingHom_surjective_ker_quotientEquiv`).
Restated on `p.asIdeal.Fiber B`; the primes over `p` are now Mathlib's
`PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}` and `ψ q` is exactly the lift whose kernel is
`PrimeSpectrum.preimageEquivFiber` (checked by `rfl` against `preimageOrderIsoFiber`).
Clause (1) is Mathlib's `preimageOrderIsoFiber`; clause (2) with the compatibility
`θ ∘ π_Q = ψ_q` has no Mathlib statement, so the record stays `existing: false`.
