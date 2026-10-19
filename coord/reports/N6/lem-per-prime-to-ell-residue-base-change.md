## Worker report

The module `lean/Sheaf/DeligneLaumon/PrimeToEllResidueBaseChange.lean` states
`AlgebraicGeometry.prime_to_ell_residue_base_change`.  It uses the canonical scheme
fibre product
`pullback (C := Scheme) (Spec.map (CommRingCat.ofHom (algebraMap k L)))
(Spec.map (CommRingCat.ofHom (algebraMap k K)))` for
`Spec L ×_{Spec k} Spec K`.

The Lean rendering of each hypothesis is:

- `k`, `L`, and `K` are fields via `[Field k] [Field L] [Field K]`.
- The field extensions are the canonical algebra structures
  `[Algebra k L] [Algebra k K]`.
- Finiteness of `L/k` is `[FiniteDimensional k L]`.
- The degree datum is `(d : ℕ)` together with
  `hd : Module.finrank k L = d`.
- The prime is `(ell : ℕ)` with `hell : Nat.Prime ell`.
- Prime-to-ell is `hcop : ¬ ell ∣ d`.

The first conclusion is `∀ z : P, (q.residueFieldAlgebraMap z).Finite`,
where `P` is the displayed fibre product and `q` is its second projection.
Mathlib's `RingHom.Finite` means that the codomain is a finitely generated module
over the domain, with scalar action induced by this ring map. Here the domain is
`K` and the codomain is `P.residueField z`, so this is exactly finite-dimensionality
over `K`, hence finiteness of every residue degree.  The second conclusion is an
existential point `z : P` with
`¬ ell ∣ (pullback.snd ... ...).degreeOver z`.  The `pullback.snd` map is the
canonical projection `P → Spec K`, and `degreeOver` is the existing upstream
notion `[κ(z):K]` induced by that structure map.  Thus the existential clause
is exactly the prime-to-ell residue-degree assertion.  The coordinate algebra is
Mathlib's `Algebra.TensorProduct k L K`; its canonical commutative algebra
structure supplies the multiplication on pure tensors specified in the node.
No hypothesis imposes separability or finite-dimensionality on `K/k`.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, used for all three field binders.
- `def-pc-field-extension`: Mathlib `Algebra`, used for the two extension maps.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, used in the
  fibre-product object.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  used for `P` and its projection to `Spec K`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField`, used in the
  universal finiteness clause.
- `def-weil-pbc-module-tensor-product`: Mathlib `Algebra.TensorProduct`, the
  canonical coordinate algebra described by the node and used in the proof plan.
- `def-weil-vector-space-dimension`: Mathlib `Module.finrank`, used for `d`.

The degree notation `Scheme.Hom.degreeOver` and the canonical map
`Scheme.Hom.residueFieldAlgebraMap` are read from `WeilConjectures.ZetaSeries`
(and checked against its current server source through `scompile.py --source`).
The map is the composite `K → κ(q(z)) → κ(z)` for the projection `q : P → Spec K`.
`degreeOver` uses the algebra structure induced by this same map. The first clause
uses Mathlib's `RingHom.Finite` from `Mathlib.RingTheory.Finiteness.Defs`.

The stated proof dependencies are imported without `public`: Mathlib's
`AlgebraicGeometry.PullbackCarrier`, `LinearAlgebra.FiniteDimensional.Basic`, and
`RingTheory.Artinian.Module`, together with the current published upstream modules
`WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField` and
`WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration`.
The theorem docstring follows all six steps of the node's proof.

Edge cases checked against the statement and source: `L = k` gives `d = 1` and
one degree-one point even when `K` is infinite; in particular `k = L = K = ℚ`
has infinite residue field but residue degree one; a separable split tensor product (for example
`L = C, k = R, K = C`) gives several degree-one points; taking `K = L` gives the
usual diagonal factor; and a purely inseparable extension (for example
`F_p(t^{1/p})/F_p(t)`) gives a nonreduced tensor algebra while the residue-degree
conclusion remains valid.  No step assumes `K/k` finite or separable, and `ell`
is an arbitrary natural prime.

Searches made before writing:

- `msearch.py ... leanfinder "A finite field extension of degree coprime ..."`:
  returned only unrelated linear-disjointness and residue-field ingredients; no
  exact assertion (no match).
- `msearch.py ... leansearch "Prime to ell degree field extension base change ..."`:
  returned tensor base-change and quasi-finite ingredients; no exact assertion.
- `msearch.py ... loogle "Algebra.TensorProduct, finrank"`: 0 hits.
- `msearch.py ... grep "coprime|relPrime"` and
  `grep "finrank.*[Rr]esidue|[Rr]esidue.*finrank"`: only unrelated ingredients.
- `rg` over `WeilConjectures/` and `lean/Sheaf` for prime-to-ell residue-degree
  phrases and the node id: no existing declaration of this statement.
- `grep -rl` over `dag/nodes` for the node id and blueprint searches: no duplicate
  node carrying this notion.

No node fault or `STATEMENT-DISPUTED` flag was found.

## Second reading by N6

I opened the current node, saved Lean file, dependency records, and upstream
`Scheme.Hom.residueFieldAlgebraMap` and `Scheme.Hom.degreeOver` declarations.
The initial dry run passed its mechanical preflight and compilation, but the
saved first conjunct was mathematically wrong: `Finite (P.residueField z)` means
finite cardinality of the field, not finite extension degree over `K`. For example,
`k = L = K = ℚ`, `d = 1`, `ell = 2` satisfies every hypothesis and has one residue
field isomorphic to `ℚ`; the saved conclusion asserted it finite. I replaced that
clause with `(q.residueFieldAlgebraMap z).Finite`, using the canonical projection
`q` and Mathlib's finite-module predicate on its induced ring map. This repairs
the Lean rendering; the natural-language node is correct and needs no correction.

The `Field`, `Algebra`, finite extension, degree equality, primality, and
nondivisibility hypotheses occur exactly as binders. The fibre product uses the
two contravariant maps from the affine spectra. Every point now has a residue
field finite-dimensional over `K` through the second projection; the existential
point uses that same second projection for `degreeOver = [κ(z):K]`. The tensor
multiplication is Mathlib's canonical one under the affine fibre-product
isomorphism, rather than extra data or a further condition. No separability or
finiteness hypothesis on `K/k` appears. I also restored the available proof
imports and expanded the theorem's proof docstring to the node's six steps.

I read ILO Exposé II Proposition 1.2.7 at printed pages 25–26 in the supplied PDF.
It explicitly permits an arbitrary field extension `K/k` and asserts the
prime-to-ell residue-field factor; the finite tensor-algebra argument in the node
also supplies the universal finiteness clause. The split separable and purely
inseparable cases above agree with this source.
