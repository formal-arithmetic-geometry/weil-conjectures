## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeToEllDecomposedEtaleFiniteSubcover` states
`AlgebraicGeometry.primeToEllDecomposed_etale_finite_subcover`, with its proof `sorry`.
No definitions or helper theorems are introduced. Only the item's `lean` field changes.

Source checked directly: ILO, Travaux de Gabber, Exposé II, Proposition 2.2.2 and
Corollary 2.2.4, printed pp. 26–27 (PDF pages 32–33). The corollary extracts a
finite subset of indices of an étale prime-to-ell decomposed covering. Its proof
uses compactness of the constructible topology and the open pointwise lifting
loci. Neither source quasi-compactness nor source separation is assumed.

Clause-by-clause correspondence:

- A scheme X is `(X : Scheme.{u})`. `[IsNoetherian X]` means locally Noetherian
  and quasi-compact, exactly equivalent to the stated finite affine Noetherian
  cover by Mathlib's `isNoetherian_iff_of_finite_affine_openCover` and
  `isNoetherian_iff_of_finite_iSup_eq_top`, read in full. It is not merely a
  hypothesis on the topology of X.
- A prime ell is `(ell : ℕ) (hEll : ell.Prime)`; no invertibility or
  characteristic restriction is imposed.
- A set-indexed family is `{I : Type w} (U : I → Scheme.{u})
  (f : ∀ i : I, U i ⟶ X)`, with an independent arbitrary index universe w.
- Every member is étale: `(hEtale : ∀ i : I, Etale (f i))`.
- Every x has an index i and a point z above it: the binders of `hCover` and
  `f i z = x`.
- Finiteness of the residue extension is
  `((f i).residueFieldMap z).hom.Finite`. `RingHom.Finite` means finite as a
  module via this very homomorphism, so this uses the canonical extension
  κ(f i z) → κ(z), identified with κ(x) using the preceding equality.
- Prime-to-ell degree is `Nat.Coprime ((f i).residueDegree z) ell`.
  `Scheme.Hom.residueDegree` is Mathlib's finrank for precisely that canonical
  residue-field map. For prime ell, this is equivalent to ell not dividing
  the finite degree. The explicit finiteness clause avoids relying on the
  zero convention for infinite finrank.
- The conclusion is `∃ I₀ : Set I, I₀.Finite ∧ ...`: a finite subset of the
  original index type. The remaining conclusion repeats exactly the lifting
  clauses, adding only `i ∈ I₀`. The sources are the original U i, with no
  changes or restrictions.
- No quasi-compactness, finite type, reducedness, or separation hypotheses on
  U i or f i are present.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (record of def-pc-scheme).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff`, and `isNoetherianRing_iff_ideal_fg` (record of
  def-weil-pbc-noetherian-ring). The Noetherian scheme interface is the
  equivalent existing `Mathlib.AlgebraicGeometry.Noetherian` class above.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (record of def-weil-etale-morphism).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, and `Scheme.Hom.residueDegree` (the first two
  are the recorded declarations of def-weil-residue-field).

Public imports expose these statement interfaces. Plain proof imports provide
`Mathlib.Topology.NoetherianSpace`, `Mathlib.Topology.Spectral.Basic`, and
`Mathlib.Topology.Spectral.ConstructibleTopology`. The Noetherian module also
provides the local-Noetherian quasi-separatedness and Noetherian-space facts.
These cover every currently stated proof dependency's recorded Mathlib module.
The proof dependency lem-per-prime-to-ell-decomposed-locus-constructible currently
has no Lean record or module, so it cannot yet be imported. Its mathematical
step and all other steps are included in the theorem docstring. This does not
prevent stating the theorem; it is not a missing statement dependency.

Edge cases checked before writing:

- Empty X: the conclusion permits I₀ = ∅ and all pointwise assertions are
  vacuous, even for empty I.
- Nonempty X and empty I: hCover is impossible, exactly as in the source.
- Identity cover: the canonical residue map is identity and its degree is 1;
  `Scheme.Hom.residueDegree_id` confirms the convention. Thus every prime is
  allowed, including 2.
- Characteristic ell is permitted: neither the node nor Corollary 2.2.4 requires
  ell invertible on X.
- Infinite residue extension: RingHom.Finite rejects it regardless of
  residueDegree's zero convention. Étale extensions are in fact finite here.
- Arbitrary non-quasi-compact or non-separated sources remain quantified over.
- I has arbitrary size: no Finite, Fintype, Nonempty, or universe relation to u
  is assumed. Finite subsets are expressed as Set.Finite without a DecidableEq
  assumption.

Searches for existing statements (all on 2026-10-24):

- msearch.py leanfinder: “Etale family on a Noetherian scheme lifting every
  point with finite residue degree prime to a prime admits a finite subfamily”.
  Eight hits on étale algebra construction/descent; none states this result.
- msearch.py leansearch: “An etale family with prime to ell residue field
  lifts over a Noetherian scheme admits a finite subfamily”. Eight étale
  definitions/descent hits; no matching finite extraction statement.
- msearch.py loogle: `Scheme.Hom.residueFieldMap, Module.finrank` was rejected
  as an unknown unqualified identifier. Corrected query
  `AlgebraicGeometry.Scheme.Hom.residueDegree` returned six hits, including
  the canonical degree definition and identity case, but no extraction theorem.
- msearch.py grep: `residue.*[Dd]egree|primeTo|prime_to|decomposed`, restricted
  to AlgebraicGeometry: four hits, giving residueDegree and algebraic cycles.
- rg on lean/WeilConjectures and lean/Sheaf for the same concepts, and the
  exact node id in lean/WeilConjectures: no existing statement. Additional
  exact-name search `primeToEllDecomposed_etale_finite_subcover` and
  `PrimeToEllDecomposedEtaleFiniteSubcover` in both source roots and
  dag/lean_names_upstream.json found no declaration.
- The related `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology` module was
  read. Its decomposed-family predicate is specialized to Alt S and cannot
  express arbitrary sources, so it is not substituted for this statement.
- The item's `lean_removed` records an earlier deleted module with this name;
  the live module is absent and the item's lean is null. This restores a
  missing statement, rather than duplicating a current declaration. There is
  no released repair note for this item.

Validation: prescribed scompile.py compiled the module separately in sandbox
mode (7.3 s) and library mode (3.4 s), both clean, exit 0. All universes and
variables are explicitly bound; no diagnostics remain. The only postponed
proof is the named item theorem. No statement dispute or node correction.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
