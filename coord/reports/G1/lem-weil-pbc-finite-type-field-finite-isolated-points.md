## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteIsolatedPointsOfFiniteType` states
`AlgebraicGeometry.Spec.finite_setOf_isOpen_singleton_of_finiteType`, with `sorry` as
its sole proof. No definitions or dependency modules were needed. The item's only changed
field is `lean`.

Hypothesis and clause correspondence:

- “Let k be a field”: `(k : Type u) [Field k]`.
- “A a finitely generated k-algebra”: `(A : Type v) [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]`. The commutative-ring binder is the algebra convention of the
  dependency node; no nontriviality, domain, or reducedness condition is imposed on A.
- “the set of prime ideals q contained in A”: the comprehension ranges over
  `q : Spec (CommRingCat.of A)`. The underlying carrier is definitionally `PrimeSpectrum A`,
  whose elements bundle an ideal and its primality proof; thus this is exactly a set of primes.
- “for which {q} is open in Spec A”: `IsOpen ({q} : Set (Spec (CommRingCat.of A)))` uses
  the spectrum's actual Zariski topology. No closedness condition is added.
- “is finite”: `.Finite` on this set, not finiteness of the whole spectrum.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra` is a Mathlib leaf, with no `lean` record required.
  Its recorded `Algebra.FiniteType` is imported from `Mathlib.RingTheory.FiniteType`;
  its full class signature and docstring identify finite generation of the top subalgebra.
- `def-weil-affine-spectrum` is a Mathlib leaf. Its recorded `AlgebraicGeometry.Spec`
  is imported from `Mathlib.AlgebraicGeometry.Scheme`. Its full definition and docstring,
  and `Spec.topObj` in `Mathlib.AlgebraicGeometry.Spec`, identify the underlying
  topological space as `PrimeSpectrum A`. The latter's structure and docstring were read
  in `Mathlib.RingTheory.Spectrum.Prime.Defs`.

Source check: the local `literature/stacks-project/algebra.tex` is absent, so the source was
read at https://stacks.math.columbia.edu/tag/00UK. The first paragraph of its proof uses
Noetherianity of the finite type fibre to obtain finitely many isolated closed points.
The present node deliberately states finiteness of all isolated points, justified by its
minimal-prime argument. The declaration docstring includes all four recorded proof steps
and the nodes used by each. No statement correction or dispute is needed.

Edge cases checked mathematically before writing:

- The zero k-algebra is allowed; its spectrum is empty and the set is finite.
- A = k has one prime, whose singleton is open.
- A = k × k has two isolated points.
- A = k[t] has no isolated primes; no dimension-zero hypothesis is appropriate.
- Nonreduced finite type algebras are included (for example k[ε]/(ε²), with one point).
- Arbitrary field characteristic is allowed; independent explicit universes u and v allow
  the field and algebra to live in different universes. All variables are explicitly bound.

Searches (2026-10-11):

- `msearch.py ... leanfinder "A finitely generated algebra over a field has finitely many
  points of its prime spectrum whose singleton is open"`: eight hits, principally
  `Algebra.QuasiFinite.finite_primeSpectrum`, quasi-finite fibre criteria and Zariski's
  lemma. These require different hypotheses or concern different conclusions; no exact match.
- `msearch.py ... loogle "Algebra.FiniteType, PrimeSpectrum"`: six hits, including
  `Algebra.QuasiFiniteAt.isClopen_singleton`, `of_isOpen_singleton`, and fibre criteria;
  none states finiteness of the set of isolated points.
- `msearch.py ... grep "isolated|finite.*singleton|finite.*[Pp]rimeSpectrum" RingTheory`:
  25 hits. `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`
  characterizes individual isolated points; discrete-spectrum criteria require dimension
  zero. No exact statement found. The full Jacobson module was subsequently read.
- `msearch.py ... leansearch "A finite type algebra over a field has finitely many isolated
  points in its prime spectrum"`: unavailable (Internal Server Error), no verdict assigned.
- Direct `rg` over Mathlib Topology for isolated-point finiteness and finite open-singleton
  sets: no matching theorem found.
- Direct `rg` over `WeilConjectures` and `lean/Sheaf` for isolated-point finiteness:
  related geometric splitting statements only, no exact declaration. `grep -rn` for the
  item id in `WeilConjectures` returned no occurrence.
- Declaration-name search in `dag/lean_names_upstream.json`, `WeilConjectures`, and
  `lean/Sheaf` found no competing finite-isolated-points declaration.

Validation: `scompile.py G1 lem-weil-pbc-finite-type-field-finite-isolated-points` on the
module returned exit code 0 (1.6 seconds), without errors or warnings. Delivery dry run
is the final mechanical check; the second reading is reserved for the separate reader.

## Second reading by G1

I reread the node statement, its Stacks source place (Algebra, Tag 00UK,
lines 40362--40420), the two dependency records, and the submitted module.
The correspondence is exact:

- The field object and hypothesis are `(k : Type u) [Field k]`; no
  characteristic or finiteness condition is added.
- The algebra object and hypotheses are `(A : Type v) [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A]`, which render a finitely generated
  k-algebra with independent universes.
- A prime ideal `q ⊆ A` is rendered by
  `q : Spec (CommRingCat.of A)`, whose points are prime ideals.
- The isolation clause is exactly
  `IsOpen ({q} : Set (Spec (CommRingCat.of A)))`, using the spectrum's
  Zariski topology.
- The conclusion is exactly finiteness of the resulting set, via `.Finite`.
  Quantifier order and the subset-builder are unchanged.

The dependency nodes are Mathlib's `Algebra.FiniteType` and
`AlgebraicGeometry.Spec`; their declarations were checked and provide the
notions used here. No private duplicate or extra hypothesis occurs. Edge
cases checked were the zero algebra (empty spectrum), `A = k`, a product
`k × k`, a polynomial algebra (no isolated points), nonreduced finite type
algebras, and arbitrary characteristic; all are covered by the binders.
The worker's LeanSearch, Loogle/LeanFinder, and direct Mathlib/project grep
searches were rerun/read; related theorems require stronger hypotheses and no
exact declaration exists. The unavailable LeanSearch invocation is recorded
in the worker search log.

No mismatch was found, so no source, node, dependency, or Lean change was
needed in this second reading.
