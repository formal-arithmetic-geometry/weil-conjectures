## Worker report

The module `Sheaf.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra` states
`AlgebraicGeometry.topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial`.
Its only proof is `sorry`; no definitions, dependency modules, or new nodes are needed.
The node is unchanged except for `lean`.

Clause-by-clause correspondence:

- A field k: `(k : Type u) [Field k]`, with arbitrary explicitly bound universe u.
- An integer n ≥ 0: `(n : ℕ)`, covering precisely all nonnegative integers.
- A commutative k-algebra T: `(T : Type v) [CommRing T] [Algebra k T]`, with
  independent arbitrary universe v.
- T of finite type over k: `[Algebra.FiniteType k T]`.
- A k-algebra homomorphism k[t₁,…,tₙ] → T:
  `(φ : MvPolynomial (Fin n) k →ₐ[k] T)`. Fin n indexes exactly n variables.
- This map is of finite type: `hφ` is `Algebra.FiniteType (MvPolynomial (Fin n) k) T`
  for the algebra structure `φ.toRingHom.toAlgebra`; this ensures the property is
  attached to this very map, with no arbitrary polynomial-algebra structure.
- Quasi-finite at every prime of T: `hq` quantifies over `q : PrimeSpectrum T` and
  uses `Algebra.IsQuasiFiniteAtPrime (MvPolynomial (Fin n) k) T q`, with the same
  induced algebra structure and hφ installed as its finite-type instance. This is
  exactly the dependency's isolated-singleton-in-the-fibre definition.
- Krull dimension of Spec T is at most n:
  `topologicalKrullDim (Spec (CommRingCat.of T)) ≤ (n : WithBot ℕ∞)`.
  The comparison takes place in the dimension type containing minus infinity.
- The empty spectrum is included: no nontriviality or nonemptiness condition on T
  is imposed, and bottom in `WithBot ℕ∞` represents minus infinity.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `Algebra.FiniteType`,
  `Mathlib.RingTheory.FiniteType` (imported through QuasiFiniteAtPrime), definition
  by finite generation of the top subalgebra.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `Mathlib.Algebra.MvPolynomial.Basic`; also read recorded `MvPolynomial.algHom_ext`
  in Basic and `MvPolynomial.aeval` in Eval. Only the polynomial type is needed here.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`: `Algebra.IsQuasiFiniteAtPrime`,
  `Sheaf.RingTheory.QuasiFiniteAtPrime`, whose full definition and docstring were read.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, dimension by irreducible closed subset chains.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`; also read `Spec.topObj` in Spec, which is the
  Zariski space `PrimeSpectrum T` underlying this scheme.

Source check: this machine has no `literature/stacks-project/algebra.tex`, so read
Stacks Tag 00QG directly at https://stacks.math.columbia.edu/tag/00QG.
It states the finite-type field-algebra dimension bound and invokes 00QF and 00OP.
The node expands that proof into local bounds and the prime-chain passage to global
Krull dimension; both steps, with all the recorded proof dependencies, are in the
Lean docstring. The source uses the symbol ⊂ for the algebra map, but its proof
requires no injectivity; the node explicitly states a homomorphism and the inequality,
including empty spectra. No change to the node is required.

Edge cases checked before writing: n = 0 gives the polynomial ring on an empty
variable set and the bound zero. For T the zero ring, there are no primes, hq is
vacuous, and the empty spectrum has bottom dimension. A polynomial source itself
with the identity map has dimension n, showing that equality cases are retained.
A proper quotient can have dimension strictly less than n; no injectivity,
surjectivity, domain, algebraic closure, or characteristic condition is added.
Independent universes u and v allow the field and its algebra to have different sizes.

Searches (real invocations recorded by msearch.py in searches.jsonl):

- LeanSearch: “A finite type quasi-finite algebra over a polynomial ring in n
  variables over a field has dimension at most n”; unavailable (Internal Server Error).
- LeanFinder: “quasi finite algebra over polynomial ring over field Krull dimension
  bounded by number of variables”; found MvPolynomial.ringKrullDim_of_isNoetherianRing,
  polynomial dimension bounds and transcendence degree bounds. None states the
  dimension bound for a quasi-finite target algebra with the node's hypotheses.
- Loogle: `Algebra.QuasiFinite, ringKrullDim`; no hits.
- Mathlib grep via msearch.py: `QuasiFinite|ringKrullDim`, in RingTheory/QuasiFinite;
  found the quasi-finite definitions, no dimension bound.
- Direct rg of Mathlib/RingTheory/KrullDimension/Polynomial.lean confirmed the
  dimension theorems there concern the polynomial source.
- Direct rg of WeilConjectures and lean/Sheaf:
  `quasi.?[Ff]inite.*[Dd]im|[Dd]im.*quasi.?[Ff]inite|` followed by the item id.
  Read WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean:
  its dimension equality needs universally closed and surjective morphisms;
  its other statements concern fibre discreteness and flat codimension preservation,
  so none has exactly this node's statement. Project hits are proof docstrings.
- `grep -rn` of the item id in WeilConjectures returned no match.
- Exact new declaration-name rg in dag/lean_names_upstream.json, WeilConjectures,
  and lean/Sheaf returned no match.

No statement dispute or dependency fault was found. The server compilation of the
51-line module succeeded with exit code 0 and no warnings. The signature in `lean.statement`
is taken verbatim from the declaration, including its local-instance binders.

## Second reading by E1

I read the sandbox node and module independently, all five statement-dependency
nodes and their recorded declarations, and the Stacks source. No mathematical
or Lean mismatch was found. The Lean module and node record are unchanged;
this section is the only delivery change from the first worker's files.

Objects, hypotheses, and conclusion, listed before checking the Lean:

1. A field k. Rendered by `(k : Type u) [Field k]`: exact, with arbitrary
   characteristic and no algebraic-closure assumption.
2. An integer n >= 0. Rendered by `(n : ℕ)`: exact, including zero.
3. A commutative k-algebra T. Rendered by `(T : Type v) [CommRing T]
   [Algebra k T]`: exact. T is not required to be nontrivial or a domain.
4. T is of finite type over k. Rendered by `[Algebra.FiniteType k T]`:
   exact. I read the class in Mathlib/RingTheory/FiniteType.lean, whose field
   is finite generation of the top subalgebra, matching the dependency node.
5. A k-algebra homomorphism from the n-variable polynomial ring to T.
   Rendered by `(φ : MvPolynomial (Fin n) k →ₐ[k] T)`: exact. I read
   MvPolynomial's finitely supported monoid-algebra definition, aeval, and
   algHom_ext. Fin n merely relabels the node's n variables; there is no
   injectivity or surjectivity hypothesis.
6. This very homomorphism is of finite type. Rendered by `hφ`, after
   `letI := φ.toRingHom.toAlgebra`: exact. The local algebra structure is
   induced by φ, so this hypothesis cannot refer to a different map.
7. The map is quasi-finite at every prime of T. Rendered by `hq`, using
   the same induced algebra and hφ as its finite-type instance, then
   `∀ q : PrimeSpectrum T, Algebra.IsQuasiFiniteAtPrime
   (MvPolynomial (Fin n) k) T q`: exact. I opened
   Sheaf/RingTheory/QuasiFiniteAtPrime.lean: it contracts q using the
   algebra map and requires the canonical fibre prime's singleton to be
   open. Mathlib's Ideal.Fiber is κ(p) tensor T, and
   PrimeSpectrum.preimageHomeomorphFiber identifies that prime with q.
   The reversed tensor factors relative to the node are canonically
   interchangeable. No additional field, localization, or finiteness
   instance is required beyond the ones explicitly supplied here.
8. The Krull dimension of Spec T is at most n, including the empty
   spectrum with dimension minus infinity. Rendered by
   `topologicalKrullDim (Spec (CommRingCat.of T)) ≤ (n : WithBot ℕ∞)`:
   exact. I read AlgebraicGeometry.Spec in Scheme.lean, Spec.topObj in
   Spec.lean (the underlying space is PrimeSpectrum T), and
   topologicalKrullDim in Topology/KrullDimension.lean (Order.krullDim
   of IrreducibleCloseds). WithBot ℕ∞ retains minus infinity and infinity,
   so the node's dimension convention is preserved, not replaced by a
   natural-number dimension.

Source reading: the local repository lacks the Stacks checkout. I retrieved
algebra.tex from the official stacks/stacks-project repository into the
sandbox's scratchpad and read its conventions, the Dimension of fibres
section introduction, and lines 31290-31305. The section imposes no hidden
Noetherian, domain, or characteristic restriction. The general conventions
include the zero ring. I also opened the official pages for
[00QG](https://stacks.math.columbia.edu/tag/00QG),
[00QF](https://stacks.math.columbia.edu/tag/00QF), and
[00OP](https://stacks.math.columbia.edu/tag/00OP).
The literal 00QG text uses a subset sign for the map; the delivered node
expressly uses a homomorphism. Its stated inequality is valid in this
generality by the exact same 00QF local argument, which assumes no
injectivity. The Lean follows the node, including quotients and zero T.
There is no statement_change in this delivery and no new definition node
or dependency module to review under H12/H13.

Edge cases: when n = 0, Fin n is empty and the source is the constant
polynomial ring; the conclusion remains dimension <= 0. When T is the
zero ring, PrimeSpectrum T is empty, hq is vacuous, and the topological
dimension is bottom, hence <= n. The field k cannot be the zero ring,
exactly as in the node. The identity polynomial-algebra map retains the
equality case; polynomial quotients can have smaller dimension. There
is no characteristic restriction, no nonempty-spectrum assumption, and
no implicit same-universe condition: u and v are separately declared and
all declaration parameters are bound. The only index set is Fin n,
which includes its empty case.

Independent searches, with different wording from the first reader:

- LeanSearch via msearch.py: "The spectrum of an algebra with discrete
  fibres over affine space in n variables has Krull dimension at most n".
  Service returned Internal Server Error; recorded as unavailable, not
  as evidence of absence.
- LeanFinder via msearch.py: "dimension monotonicity of a finite type
  ring map with isolated fibre points". Eight results: standard-smooth
  relative dimensions, module rank comparisons, presentation dimensions,
  and a lower bound for polynomial-ring dimension. None states this node.
- Loogle via msearch.py: `Algebra.QuasiFinite`. Twelve results, concerning
  finite fibres, Artinian bases, quotients and localizations. I read the
  class in QuasiFinite/Basic.lean: it is a global fibre-finiteness notion,
  not a replacement statement for the required dimension bound.
- Direct rg of Mathlib/RingTheory/QuasiFinite for `krullDim|KrullDim|dimension`
  found zero-dimensional fibre arguments, not this bound. Direct rg of
  WeilConjectures and lean/Sheaf for dimension/quasi-finite combinations
  and `KrullDim.*[Ff]inite`, plus the full proposed declaration name in
  those trees and dag/lean_names_upstream.json, found no duplicate.
  I opened the upstream Morphisms/QuasiFinite.lean declarations: its
  dimension equality requires universally closed and surjective, and its
  codimension equality requires flatness. Neither has this signature.
  Thus the module should be retained rather than marked existing.

H5/H6/H8/H9 checks: no definitions in this module, hence no hollow data;
its single theorem has only `sorry`; module and declaration docstrings
both cite Tag 00QG and the correct blueprint id. The theorem docstring
carries both node proof steps, including all named proof dependencies,
the local polynomial dimension bound and the supremum over prime chains.
All lines are at most 100 characters; imports supply the spectrum,
polynomial ring, dimension and recorded quasi-finite-at-prime notion.
The namespace has no Sheaf prefix. The recorded lean.statement is
verbatim the file signature up to `:=`, and no universe or variable is
left unbound.

Validation: scompile.py on the absolute sandbox module path returned
exit code 0, compiled in 1.5 seconds, with no warnings. An initial call
with a repository-relative path failed to locate the sandbox module;
this was corrected by passing its absolute path, with no file change.
