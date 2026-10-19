## Worker report

The module `Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension` states
`Algebra.isQuasiFiniteAtPrime_iff_topologicalKrullDimAt_eq_zero`, with `sorry` as
its entire proof. No definitions, auxiliary theorems, or node corrections are added.

Hypothesis and clause correspondence:

- Commutative rings R and T: `(R : Type u) (T : Type v) [CommRing R] [CommRing T]`,
  with both universes explicitly bound and independent.
- The homomorphism φ: `[Algebra R T]`, whose ring map is `algebraMap R T`.
  This encodes an arbitrary commutative ring map, without injectivity or other assumptions.
- Finite type: `[Algebra.FiniteType R T]`, the dependency's recorded predicate.
- The prime q of T: `(q : PrimeSpectrum T)`.
- The contracted prime p: `q.comap (algebraMap R T)`.
- The residue field and fibre ring: the target of `preimageHomeomorphFiber` is
  `PrimeSpectrum ((q.comap (algebraMap R T)).asIdeal.Fiber T)`.
  `Ideal.Fiber` is κ(p) ⊗[R] T, the convention of the recorded localization node.
  The node's T ⊗[R] κ(p) is carried to this ring by `Algebra.TensorProduct.comm`;
  this ring isomorphism preserves the corresponding prime and its open neighbourhoods.
  Thus it also preserves their dimensions and dimension at the point.
- The unique fibre prime over q: `PrimeSpectrum.preimageHomeomorphFiber R T
  (q.comap (algebraMap R T)) ⟨q, rfl⟩`. Membership of q in its own fibre is definitional.
  This homeomorphism has `preimageOrderIsoFiber` as its underlying order equivalence,
  exactly the dependency's recorded bijection, not an independently chosen prime.
- Quasi-finiteness at q: `IsQuasiFiniteAtPrime R T q`, as recorded by the dependency.
- Dimension zero at the fibre prime: `topologicalKrullDimAt (...) = 0`.
  The source definition is the infimum over dimensions of all open neighbourhoods,
  an attained minimum in `WithBot ℕ∞`. The spectrum is the underlying space of `Spec`.
- “If and only if” is `↔`, with no further conclusion or assumptions.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, available publicly through
  `Sheaf.RingTheory.QuasiFiniteAtPrime`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`; residue
  field construction in `Mathlib.RingTheory.LocalRing.ResidueField.Defs`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`,
  `PrimeSpectrum.preimageEquivFiber`, `PrimeSpectrum.preimageOrderIsoFiber`, and
  `PrimeSpectrum.preimageHomeomorphFiber` (available through QuasiFiniteAtPrime).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` (public import).
- `Sheaf.RingTheory.QuasiFiniteAtPrime`: `Algebra.IsQuasiFiniteAtPrime` (public import).
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt` (public import).
- Proof imports: `Mathlib.RingTheory.Spectrum.Prime.Noetherian` for the affine
  Noetherian-space input; `Mathlib.AlgebraicGeometry.Noetherian` for local Noetherianity,
  open-subscheme permanence and compactness; and
  `Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete` for
  `AlgebraicGeometry.finite_and_discreteTopology_of_topologicalKrullDim_le_zero`.
  `topologicalKrullDim` comes through the dimension module; `CompactSpace` through
  topology imports. Finite-type algebra Noetherianity comes through QuasiFiniteAtPrime.
  Thus every stated proof dependency has its module in the import closure.

Sources checked: local Stacks `morphisms.tex`, lemma
`lemma-locally-quasi-finite-rel-dimension-0` (0397), both proofs, especially the second;
`properties.tex`, `lemma-isolated-dim-0-locally-noetherian` (0H7C).
They agree with the node and the Lean statement.

Edge cases: A zero target ring has no q, so no nonexistent fibre point is required.
For an actual q, its contraction is prime and its canonical fibre prime exists, even
when the base ring is not Noetherian. The fibre is finite type over a field, which
is the only Noetherianity needed. A field fibre is a singleton with dimension zero.
Positive-dimensional neighbourhoods are not replaced by the dimension of a local
ring (which would be the wrong notion). No finite-dimensional or nonzero hypothesis
is imposed; all characteristics and independent ring universes are allowed.

Searches performed with `msearch.py` (recorded in searches.jsonl):

- LeanFinder: “A finite type ring map is quasi finite at a prime iff the fibre spectrum
  has topological Krull dimension zero at the corresponding point”. Eight results,
  including `Algebra.quasiFinite_iff`, `Algebra.QuasiFiniteAt`, and finiteness/discreteness
  of quasi-finite fibres; none states the local dimension equivalence.
- Loogle: `"QuasiFiniteAt", "topologicalKrullDimAt"`: zero results.
- Mathlib grep: `quasiFinite.*(krullDim|dimension)|topologicalKrullDimAt.*[Qq]uasi`:
  zero results.
- `rg` of the same pattern in upstream WeilConjectures and project `lean/Sheaf`:
  only flat quasi-finite dimension comparison results, with extra smoothness/flatness
  hypotheses; no matching theorem. An item-id search found no upstream declaration.
- Proposed full name searched in upstream name inventory, upstream sources, and
  project Sheaf: no collision.

No node faults or disputed statements were found. The declaration docstring carries
all six proof steps of the node. Server compilation uses scompile.py only.

## Second reading by NX

I read the node, its six statement dependencies and their recorded declarations,
the delivered module, and Stacks morphisms.tex lemma-locally-quasi-finite-rel-dimension-0
(0397), including both proofs. That lemma assumes only local finite type; its affine
finite-type specialization is precisely this node. I also read properties.tex
lemma-isolated-dim-0-locally-noetherian (0H7C), and algebra.tex
lemma-isolated-point-fibre (00PK) and definition-quasi-finite (00PL).
No source-wide field, characteristic, separatedness or Noetherian hypothesis is missing.

Object, hypothesis and conclusion checklist, in the node's order:

1. Arbitrary commutative rings R and T: `(R : Type u) (T : Type v)` with
   `[CommRing R] [CommRing T]`. Verdict: exact, including independent universes.
2. An arbitrary ring homomorphism φ: `[Algebra R T]`, with `algebraMap R T`.
   Verdict: exact; every homomorphism between commutative rings induces this algebra
   structure, with no injectivity or faithful-action requirement.
3. Finite type of φ: `[Algebra.FiniteType R T]`. I opened its class declaration in
   Mathlib.RingTheory.FiniteType: the top subalgebra is finitely generated.
   Verdict: the recorded dependency and exactly the node's hypothesis, including
   an empty set of generators.
4. Prime q of T: `(q : PrimeSpectrum T)`; its contraction p:
   `q.comap (algebraMap R T)`. Verdict: exact; proper primality is carried by q,
   and no maximality or rational-point assumption is introduced.
5. Residue field and fibre: the type of the displayed point is
   `PrimeSpectrum ((q.comap (algebraMap R T)).asIdeal.Fiber T)`.
   I opened Localization.AtPrime, Ideal.ResidueField, and Ideal.Fiber. The latter
   is κ(p) ⊗[R] T, the dependency's recorded convention. Tensor commutation
   identifies it with T ⊗[R] κ(p), carries t ⊗ 1 to 1 ⊗ t, and induces a
   homeomorphism on spectra. Verdict: same fibre and same dimension invariant.
6. Unique fibre prime over q:
   `PrimeSpectrum.preimageHomeomorphFiber R T (q.comap (algebraMap R T)) ⟨q, rfl⟩`.
   I opened preimageEquivFiber, preimageOrderIsoFiber and preimageHomeomorphFiber
   in Mathlib.RingTheory.LocalRing.ResidueField.Fiber. The homeomorphism extends
   the recorded order equivalence; its forward prime is the kernel of the
   residue-field tensor map and its inverse contracts along includeRight.
   Verdict: exactly the canonical prime in the node, without a new choice.
7. Quasi-finiteness at q: `IsQuasiFiniteAtPrime R T q`. I read the whole
   Sheaf.RingTheory.QuasiFiniteAtPrime definition: it requires openness of the
   singleton of precisely the same canonical fibre prime. Verdict: the recorded
   notion, with identical finite-type assumptions and no private substitute.
8. Dimension zero at that fibre point: `topologicalKrullDimAt (...) = 0`.
   I opened the upstream definition: it is the infimum of
   `topologicalKrullDim U` over open U containing the point; the infimum is
   attained in WithBot ℕ∞. Mathlib's topologicalKrullDim is the dimension of
   chains of irreducible closed subsets. I also opened Spec in
   Mathlib.AlgebraicGeometry.Scheme: its underlying space is this spectrum.
   Verdict: precisely the node's minimum over open neighbourhoods.
9. The equivalence: `↔` joins exactly clauses 7 and 8. Verdict: both directions,
   no extra conclusion, no reordered existential quantifier or hidden hypothesis.

Edge cases: if T is the zero ring its spectrum has no q, so the assertion is
vacuous, as in the node. If R is the zero ring any R-algebra T is also zero;
there is no excluded prime to handle. The existence of q ensures the canonical
fibre point exists, so an empty fibre is never assigned a point. Field fibres
and finite zero-dimensional fibres give dimension zero. Empty generator sets
(n = 0) are admitted by FiniteType; no n or index-type binder is restricted.
No characteristic restriction or nontriviality assumption is imposed. Non-Noetherian
R and T are covered: only their finite-type residue-field fibre needs to be
Noetherian. At the generic point of an affine line over a field, dimension at
the point is one although the local ring is a field; the Lean correctly retains
the former dimension. Infinite dimension is representable in WithBot ℕ∞.
All variables and universes in the signature are explicitly bound.

Independent reuse searches (different wording from the worker): LeanFinder query
“For a finitely generated algebra, isolated primes in the fibre are exactly the
points of local topological dimension zero” returned eight auxiliary results,
including localization dimension bounds and
PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero, with no match.
Loogle query `"topologicalKrullDimAt", "PrimeSpectrum"` returned zero results.
LeanSearch query “An isolated point in the fibre of a finite type algebra has
local dimension zero and conversely” was unavailable (Internal Server Error);
no negative verdict is inferred from that failure. Direct rg searches for
`topologicalKrullDimAt`, isolated/dimension combinations and quasiFinite/dimension
combinations covered upstream WeilConjectures, project lean/Sheaf and Mathlib's
AlgebraicGeometry and RingTheory. I opened the nearby project
QuasiFiniteLocalDimension module: it is a local-ring dimension inequality,
not this equivalence. Upstream smooth and flat quasi-finite dimension results
have different hypotheses and conclusions. No existing declaration replaces this item.

The proof imports cover all recorded proof dependencies: I checked the finite-type
Noetherianity theorem, the Noetherian spectrum instance, the locally Noetherian
class and open-subscheme instance, the Noetherian scheme class, CompactSpace,
and the project finite/discrete theorem's signature. There are no new definition
nodes or dependency modules to review. The single theorem's proof is exactly
`sorry`; no definitions or auxiliary results are introduced. Its docstring cites
the source and blueprint id and carries all six node proof steps. Header,
namespace, imports and line widths meet the conventions. The node's lean.statement
was compared programmatically with the file and is verbatim equal.

Mismatches found: none. Changes: appended this independent second reading and
recorded its independent searches; the Lean statement and node are unchanged.
