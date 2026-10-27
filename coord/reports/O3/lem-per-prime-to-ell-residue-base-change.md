## Worker report

The module `Sheaf.DeligneLaumon.PrimeToEllResidueBaseChange` states
`AlgebraicGeometry.prime_to_ell_residue_base_change`. Its only theorem has proof
`sorry`; there are no new definitions, helper theorems, or dependency repairs.
Only the item's `lean` field changes. The old removed module is not an existing
declaration: the node's `lean_removed` explicitly records its deletion, and the
current sources have neither that file nor that declaration.

Hypothesis-by-hypothesis and clause-by-clause reading:

- The fields k, L, K are `(k L K : Type u)` with `[Field k] [Field L] [Field K]`.
  The field extensions are exactly `[Algebra k L] [Algebra k K]`, whose maps are
  `algebraMap k L` and `algebraMap k K`. These use the dependency interfaces, with
  no extra structure on either extension.
- Finiteness of L/k is `[FiniteDimensional k L]`; its stated degree d is the
  natural number `d` with `hd : Module.finrank k L = d`.
- The prime ell is `ell : ℕ` and `hell : Nat.Prime ell`; the prime-to-degree
  hypothesis is exactly `hdegree : ¬ ell ∣ d`.
- P is literally `pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))`, not a set of abstract field
  factors or an assumed replacement for the tensor algebra.
- Every point z of P is quantified in the first conjunct. The statement
  `((pullback.snd ...).residueFieldMap z).hom.Finite` means that κ(z) is a finite
  module over κ(q(z)). Since q(z) is the unique point of Spec K, this field is
  canonically K, so this is precisely finiteness of [κ(z):K]. In particular,
  `RingHom.Finite` is module-finiteness, not finiteness of the underlying set.
- The second conjunct is `∃ z : ↑P, ¬ ell ∣ (pullback.snd ...).residueDegree z`.
  Mathlib defines `Scheme.Hom.residueDegree` as the finrank for that very
  residue-field map. Hence its field extension is exactly the one in the first
  conjunct and its degree is [κ(z):K]. Finiteness in the first conjunct removes
  its infinite-extension junk value convention.
- The tensor-product sentence fixes the intended algebra, rather than imposing
  an additional hypothesis. The proof import `pullbackSpecIso k L K` identifies
  P with Spec(L ⊗[k] K), with the projection maps given by its `_inv_fst` and
  `_inv_snd` formulas. Mathlib's `Algebra.TensorProduct.tmul_mul_tmul` is exactly
  the multiplication formula in the node. These are the existing constructions;
  no new tensor multiplication or residue-field construction is introduced.
- K/k has no separability, finite-generation, cardinality, or dimension binder.
  The common universe u is the ambient universe of Scheme and CommRingCat;
  it can be instantiated at the maximum of the field universes. There is no
  independent smaller universe used to restrict test extensions.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (mathlib_match).
- `def-pc-field-extension`: `Algebra` and `RingHom.toAlgebra`,
  Mathlib.Algebra.Algebra.Defs.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, with scheme
  pullbacks supplied by Mathlib.AlgebraicGeometry.Pullbacks.
- `def-weil-residue-field`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  and its finrank interface `Scheme.Hom.residueDegree`,
  Mathlib.AlgebraicGeometry.ResidueField. This avoids the additional project
  `degreeOver` interface, whose owning node is not a statement dependency.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  Mathlib.LinearAlgebra.TensorProduct.Defs (mathlib_match); also read its lift,
  uniqueness, and rTensor declarations in Basic and Map.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  Mathlib.LinearAlgebra.Dimension.Finrank. FiniteDimensional is the existing
  abbreviation for Module.Finite in Mathlib.LinearAlgebra.FiniteDimensional.Defs.

All stated proof dependencies are imported, without public exposure when only
used by the proof: `AlgebraicGeometry.pullbackSpecIso`
(Mathlib.AlgebraicGeometry.Pullbacks), `Scheme.Pullback.carrierEquiv`
(Mathlib.AlgebraicGeometry.PullbackCarrier),
`Scheme.Pullback.exists_residueField_equiv_ofPointTensor`
(WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField),
`fieldOfFiniteDimensional` (Mathlib.LinearAlgebra.FiniteDimensional.Basic),
`IsArtinianRing.of_finite` (Mathlib.RingTheory.Artinian.Module), and
`RingTheory.exists_ideal_filtration_length_one`
(WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration).
Their signatures and docstrings were read; the theorem docstring records the
node's six proof steps, including the dimension sum with multiplicities.

Edge cases checked before writing:

- L=k: d=1, and P=Spec K has one point of degree 1, for every prime ell.
- k=R, L=C, K=C, ell odd: two degree-one points, rather than a purported
  degree-two field extension after base change.
- Purely inseparable L/k of degree p, with K=L: the tensor algebra may be
  nonreduced; the single residue degree can be 1. The length filtration counts
  multiplicities, and neither the statement nor its proof plan assumes a
  product of fields or separability. If ell=p, the degree hypothesis excludes
  this degree-p example, as it should; ell equal to the characteristic is not
  excluded in general.
- Arbitrarily large transcendental K/k remains allowed.
- d=0 is impossible for a field extension with finite dimension; no redundant
  positivity hypothesis is added. The existence clause rules out an empty P.
- No finite underlying set of residue-field elements is required: characteristic
  zero examples such as k=L=K=Q are included.

Searches for an existing statement (2026-10-24):

- msearch.py leanfinder, query `A finite field extension of degree prime to ell
  after arbitrary field extension has a point of prime to ell residue degree`:
  eight hits on finite fields and inseparable degrees; none is the assertion.
- msearch.py loogle, query `Module.finrank, Ideal.ResidueField`: nine hits on
  fibre rank, inertia degree, and the ramification/inertia degree sum. None
  states both clauses for this arbitrary field-base-change pullback.
- msearch.py grep, query
  `prime_to_ell.*residue|residue.*prime_to_ell|coprime.*finrank`: two hits on
  linear disjointness of extensions of coprime degrees; no matching assertion.
- rg in Mathlib/AlgebraicGeometry, FieldTheory, RingTheory for
  `prime_to_ell_residue_base_change|prime.to.ell.*residue|residue.*prime.to.ell`:
  no match. rg in WeilConjectures and Sheaf for residue/base-change and
  prime-to-ell/residue patterns found unrelated tame and alteration material;
  the exact declaration name and exact blueprint id have no source match.
  The required grep -rn of the item id in WeilConjectures likewise has no hit.

Source checked directly in the local ILO PDF, Expose II, Proposition 1.2.7,
printed pp. 25--26: it explicitly allows arbitrary K/k and asserts the
prime-to-ell residue degree. The node's additional every-point finiteness
follows from its finite-dimensional tensor-algebra argument. No statement
correction or STATEMENT-DISPUTED issue was found.

Validation: the prescribed scompile.py compiled both the sandbox module and its
library module path cleanly. The first parse check caught an extra parenthesis,
which was repaired before the clean compile. Final dry-run result is recorded
below after validation.

The final `deliver2.py --no-push` run printed OK: commit 66e6ec10d8f passed
preflight and compiled. The final packet changes only `lean` on the node; the
recorded signature matches the file verbatim, and every Lean line is at most
100 characters. The independent maintainer review is supplied by the delivery
workflow; no second worker or sub-agent was started.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
