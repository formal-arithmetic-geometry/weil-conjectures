## Worker report

The module `Sheaf.RingTheory.EquationCountLocalizeRelativeGlobalCompleteIntersection`
states `Algebra.exists_localization_relativeGlobalCompleteIntersection`, with its sole proof
`sorry`. No definitions, auxiliary nodes, dependency replacements, or statement corrections
are needed. The declaration docstring gives all seven steps of the node's proof.

Hypotheses and objects, clause by clause:

- A commutative ring is `(R : Type u) [CommRing R]`, with explicit arbitrary universe `u`.
- The nonnegative integers and the equations are `(n c : ℕ)` and
  `(f : Fin c → MvPolynomial (Fin n) R)`.
- The ring `S = R[x_1,...,x_n]/(f_1,...,f_c)` is exactly the quotient by
  `Ideal.span (Set.range f)`, named `S` in the signature's let expressions.
- The prime ideal is bundled as `q : PrimeSpectrum S`. Its inverse image is
  `p := PrimeSpectrum.comap (algebraMap R S) q`.
- Mathlib's `p.asIdeal.Fiber S` is `κ(p) ⊗[R] S`, the tensor factors reversed from the
  node by the canonical commutativity isomorphism. It is not a different fibre.
- The point `Q` is `PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩`. Reading that
  definition shows that its ideal is precisely the kernel of the tensor-product map
  built from `Ideal.ResidueField.mapₐ` and `IsScalarTower.toAlgHom` to `q.asIdeal.ResidueField`.
  Thus it is the canonical kernel point of the node, not an arbitrary prime above `q`.
- The hypothesis `dim_Q Spec F = n-c` is `hdim`, namely
  `c ≤ n ∧ topologicalKrullDimAt Q = (n - c : ℕ)`. The dimension at a point is nonnegative;
  hence the order condition is a consequence of, and makes this equivalent to, the signed
  integer equality in the node. It prevents truncated subtraction admitting `c > n`.

Conclusions, clause by clause:

- `∃ h : MvPolynomial (Fin n) R` chooses the polynomial; `g := Ideal.Quotient.mk _ h`
  is exactly its image. `g ∉ q.asIdeal` is the required exclusion.
- `Option (Fin n)` has the `n` old variables `some i` and the new variable `none`.
  `Option (Fin c)` similarly indexes exactly `c+1` equations.
- The relations at `some i` are `MvPolynomial.rename some (f i)`, the old equations
  embedded in the larger polynomial ring. The relation at `none` is
  `MvPolynomial.rename some h * MvPolynomial.X none - 1`. Their ideal quotient is `T`.
- `IsRelativeGlobalCompleteIntersection (algebraMap R T)` uses the dependency's actual
  declaration. Since that predicate existentially chooses a presentation, the following
  conjunct explicitly requires the expected dimension for THIS enlarged presentation:
  for each `p : Ideal R` with `hp : p.IsPrime`, `Nontrivial (p.Fiber T)` implies
  `c+1 ≤ n+1` and `topologicalKrullDim (PrimeSpectrum (p.Fiber T)) = n+1-(c+1)`.
  This is exactly the nonempty-fibre clause with the signed count, not a stronger condition;
  it also entails the preceding existential presentation predicate by reindexing the finite
  Option sets with `Fin (n+1)` and `Fin (c+1)`.
- `∃ e : T ≃ₐ[R] Localization.Away g` supplies an R-algebra isomorphism.
  The two last conjuncts specify it on every old variable and the new variable:
  `some i` maps to `algebraMap S (Localization.Away g) (Ideal.Quotient.mk _ (X i))`,
  while `none` maps to `IsLocalization.Away.invSelf g`, i.e. `1/g`.
  Algebra homomorphisms from the quotient are determined by these generators and the
  R-algebra condition, so this is the exact homomorphism described in the node.

Dependency declarations inspected and used:

- def-weil-pbc-mv-polynomial-ring: Mathlib.Algebra.MvPolynomial.Basic,
  `MvPolynomial`, `MvPolynomial.algHom_ext`; Mathlib.Algebra.MvPolynomial.Eval,
  `MvPolynomial.aeval` (universal-property interpretation); the signature uses `MvPolynomial`.
- def-weil-pbc-localization-at-prime: Mathlib.RingTheory.Localization.AtPrime.Basic,
  `Localization.AtPrime`; Mathlib.RingTheory.LocalRing.ResidueField.Ideal,
  `Ideal.ResidueField`; Mathlib.RingTheory.LocalRing.ResidueField.Fiber, `Ideal.Fiber`.
  The latter two occur through `PrimeSpectrum.preimageEquivFiber`, whose full definition was read.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Spec`.
  Only its underlying topological space is involved, so the signature uses `PrimeSpectrum`,
  the actual underlying space of affine Spec, without constructing unused scheme structure.
- def-kun-topological-dimension-at-point:
  WeilConjectures.Mathlib.Topology.KrullDimension, `topologicalKrullDimAt`, imported directly.
- def-weil-pbc-relative-global-complete-intersection:
  Sheaf.Paper.RelativeGlobalCompleteIntersection, `Algebra.IsRelativeGlobalCompleteIntersection`,
  imported directly and used together with the explicit fibre property of the given presentation.
- def-weil-ring-localization-away: Mathlib.GroupTheory.MonoidLocalization.Away,
  `Localization.Away`, via Mathlib.RingTheory.Localization.Away.Basic, which also supplies
  `IsLocalization.Away.invSelf`.

Edge cases checked before writing: zero ring R gives no q, as does a unit ideal of relations;
no Nontrivial R assumption was added. For n=c=0 the quotient is R and the enlarged presentation
adjoins just one variable with equation hX-1. Empty relation families (c=0), and arbitrary zero
or redundant equations, are admitted. For c>n the signed dimensional hypothesis is impossible,
as required; no subtraction truncation changes this. When n=c the dimension is zero. Empty
fibres of T impose no dimension equation, through the Nontrivial antecedent. The prime q with
g outside it guarantees that the chosen localization is not the zero ring, without an extra
hypothesis. No Noetherian, flatness, regular-sequence, field, or smoothness assumption was added.

Searches (actual msearch invocations logged in searches.jsonl):

- LeanFinder: "Polynomial quotient with c equations localizes to relative global complete
  intersection when fibre dimension at a prime is n minus c". Eight hits concern standard
  smoothness and smooth localization; none states this dimension-count assertion.
- LeanSearch: "Localize polynomial quotient to relative global complete intersection with
  expected fibre dimension". Service returned Internal Server Error; unavailable, no verdict.
- Loogle: `IsLocalization.Away.mvPolynomialQuotientEquiv`. Two hits: the canonical one-variable
  presentation of a localization and its evaluation formula. Neither states the existence of
  a localization with the required fibre dimensions.
- Mathlib grep: `CompleteIntersection|complete.intersection|localize_relative`. One hit is
  explanatory text in RingTheory/Extension/Presentation/Basic.lean, no matching declaration.
- rg of the source WeilConjectures tree and lean/Sheaf for `relativeGlobal|RelativeGlobal|
  equation-count-localize`: only the existing general relative-global-complete-intersection
  definition, which is reused. Search for this node id and the chosen declaration name in
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json yielded no existing statement.

Source checked: https://stacks.math.columbia.edu/tag/00ST, part (3) and its proof. The local
literature/stacks-project/algebra.tex is absent on this machine; the authoritative tag was
opened directly. It specifies the same enlarged presentation, prime, dimension hypothesis,
and nonmembership conclusion. No mathematical node fault or disputed statement was found.

Tool observation: the local stage2_delivery.py signature reader stops at a top-level match
branch `|` in a signature. The final signature uses the standard `Option.elim'` combinator
for the relation family and has no such branches; no tool was modified.

## Second reading by K1

I read the node statement clause by clause against
`Algebra.exists_localization_relativeGlobalCompleteIntersection`.

- The base object is `(R : Type u) [CommRing R]`; the finite indices are
  `n c : ℕ`; and the equations are `f : Fin c → MvPolynomial (Fin n) R`.
  This renders the commutative ring, arbitrary nonnegative counts, and exactly
  `c` equations in `n` variables.
- `S` is the quotient
  `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)`, and `q` is a bundled
  prime of `S`.  The inverse image `p` and fibre point are rendered in `hdim`
  by `PrimeSpectrum.comap` and `PrimeSpectrum.preimageEquivFiber`.
  The additional `c ≤ n` records the nonnegative (untruncated) meaning of the
  source's integer `n-c`; it excludes the spurious Nat-subtraction case `c>n`.
- The conclusion chooses `h`, sets `g := Ideal.Quotient.mk _ h`, and states
  `g ∉ q.asIdeal`.
- `relations : Option (Fin c) → MvPolynomial (Option (Fin n)) R` has the old
  equations at `some i` and the new equation
  `rename some h * X none - 1` at `none`.  Thus `T` is exactly the stated
  quotient with one added variable and equation.
- The conclusion now states precisely that this `T` satisfies
  `IsRelativeGlobalCompleteIntersection (algebraMap R T)` and provides the
  `R`-algebra isomorphism `e : T ≃ₐ[R] Localization.Away g`, with the old
  variables and new inverse mapped exactly as in the node.

The first worker had inserted an extra conjunct explicitly asserting the fibre
 dimension of this particular presentation.  That clause is stronger than the
 node's conclusion, which only asks for the relative-global-complete-intersection
 predicate.  I removed it from the Lean theorem and made the node's `lean.statement`
 verbatim match the repaired signature.  No other mismatch was found.

Edge cases checked: `c=0`, `n=0`, `n=c`, empty relation families, redundant or
zero equations, zero rings (which have no prime `q`), and empty fibres of `T`.
The `c ≤ n` guard prevents truncated subtraction from admitting `c>n`; no
Noetherian, field, flatness, characteristic, or universe restriction was added.

Searches recorded by the worker were rechecked: LeanFinder/LeanSearch and
Loogle searches found only standard-smooth or localization presentation results;
grep of Mathlib, `WeilConjectures`, and `lean/Sheaf` found no matching statement.
The reused predicate is the dependency declaration
`Algebra.IsRelativeGlobalCompleteIntersection` in
`Sheaf.Paper.RelativeGlobalCompleteIntersection`; its definition was read and
matches the node's notion.
