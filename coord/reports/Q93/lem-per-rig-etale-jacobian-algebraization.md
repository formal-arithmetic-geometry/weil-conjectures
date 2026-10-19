## Worker report

The delivery states `AlgebraicGeometry.rigEtaleJacobianAlgebraization` in
`Sheaf.RingTheory.RigEtaleJacobianAlgebraization`. Its proof is `sorry`, as required
for stage 2. The added definition module is `Sheaf.RingTheory.CompletedPolynomialConormal`.
The item's mathematical statement is unchanged. Its `stmt_deps` gains only the new
construction node `def-per-completed-polynomial-conormal`.

Source checked directly: `literature/stacks-project/restricted.tex`,
`lemma-equivalent-with-artin` (Tag 0AJU), condition (3), and
`lemma-approximate-by-etale-over-complement` (Tag 0AKG), condition (8).
The finite completed-polynomial presentation implies the finite-type reduction required
in 0AKG. No additional flatness, properness, nonzero ring, principal ideal,
non-zero-divisor, or nonempty-variable hypothesis is imposed.

Clause-by-clause rendering of the item:

- Commutative Noetherian ring A: `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- Ideal I: `(I : Ideal A)`.
- A finite number r of variables, including zero: `(r : ℕ)` and `MvPolynomial (Fin r) A`.
- P is the I-adic completion of that polynomial ring: `rigPolynomialCompletion I r`
  is the actual `AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
  (MvPolynomial (Fin r) A)`. The ideal used in this ring completion is IQ.
- Ideal J in P: `(J : Ideal (rigPolynomialCompletion I r))`.
- E is P/J: the type `rigPolynomialCompletion I r ⧸ J` throughout the signature.
- E is I-adically complete: `[IsAdicComplete I (rigPolynomialCompletion I r ⧸ J)]`.
  This module form is the same I-adic filtration as powers of the extended ideal IE:
  `(I^n • ⊤)` is IE to the nth power, with scalars restricted to A.
- Some nonnegative annihilator exponent: the theorem quantifies `(c : ℕ)` and takes
  the two annihilation assumptions at that c. Applying it to a witness of the informal
  existential gives exactly the stated conclusion.
- The domain J/J² is Mathlib's `J.Cotangent`, not a private replacement.
- The target E to the r-fold direct sum is `Fin r → E`; for a finite index set, the
  product module and direct sum module have the same coordinate description.
- The canonical continuous differential δ is `rigJacobianDifferential r I J`.
  `rigPartialDerivative I r i` is the unique A-linear extension of
  `MvPolynomial.pderiv i` preserving every ideal power, and
  `rigJacobianRawDifferential` composes it with the actual quotient map P → P/J.
  `Submodule.liftQ` then induces the map on Mathlib's conormal module. Thus the
  displayed formula on representatives is literally the construction.
- I^c kills the kernel: `hkernel : I ^ c • (rigJacobianDifferential r I J).ker ≤ ⊥`.
- I^c kills the cokernel: `hcoker` says I^c times the top submodule of
  `(Fin r → E) ⧸ (rigJacobianDifferential r I J).range` is contained in zero.
  Using A-linear kernels and cokernels retains the underlying groups of the
  E-linear differential, and therefore precisely the same I-annihilation condition.
- There exists a commutative A-algebra D: `∃ (D : Type u) (_ : CommRing D)
  (_ : Algebra A D), ...`. These existential binders supply the actual instances.
  The universe imposes no restriction: a finite-type A-algebra is a quotient of
  a finite polynomial algebra over A and has a model in A's universe.
- D is finite type: `RingHom.FiniteType (algebraMap A D)`, the dependency's recorded notion.
- Spec D → Spec A is étale over the complement of V(I): for every f in I,
  `Etale (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map ...)))` states that
  Spec D_f → Spec A_f is étale. These D(f) cover exactly the complement of V(I).
  The ring map is the canonical induced localization map, not an arbitrary map.
- An A-algebra isomorphism from D's I-adic completion to E:
  `Nonempty (AdicCompletion (I.map (algebraMap A D)) D ≃ₐ[A] E)`.
  `Nonempty` here asserts existence of precisely the algebra isomorphism requested.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (the abbreviation
  `IsNoetherian A A` and the ideal finite-generation interpretation).
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, with its commutative algebra
  structure. `Mathlib.Algebra.MvPolynomial.PDeriv`: `MvPolynomial.pderiv`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, its compatible quotient
  sequences, `IsAdicComplete`; `Mathlib.RingTheory.AdicCompletion.Algebra` supplies the
  canonical ring and A-algebra structures on ring completions.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (not a new finite-type notion).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away` and the canonical
  `IsLocalization.Away.map` used for the complement cover.
- `Mathlib.RingTheory.Ideal.Cotangent`: `Ideal.Cotangent`, defined as
  `J ⧸ (J • ⊤ : Submodule P J)`, and the lemma identifying this kernel with J².
- New definition dependency: `Sheaf.RingTheory.CompletedPolynomialConormal`,
  `AlgebraicGeometry.rigJacobianDifferential` and its listed helper declarations.
- The stated proof dependency `lem-weil-pbc-completion-exact-finite-modules` matches
  `AdicCompletion.map_injective`, `map_exact`, `map_surjective`; its module
  `Mathlib.RingTheory.AdicCompletion.Exactness` is a non-public proof import.
  The finite-type Noetherian proof dependency is already supplied by FiniteType.
  The four specialized perverse algebraization/shrinking proof dependencies have no
  recorded Lean module on the base, so there is no module to import for them yet.

Edge cases checked against the formulas and source:

- r = 0: the target is the zero-coordinate module; no chosen variable is required.
- c = 0: I^0 is the unit ideal, so both cohomology groups must vanish.
- I = 0: the complement is empty; f = 0 localization is the zero ring, so the
  localized étale assertion is vacuous. Polynomial completion is the polynomial ring.
- I = A: the polynomial completion and complete quotient E are zero; D may be zero,
  and its spectrum is empty. No `Nontrivial` assumption excludes this case.
- J = P and the zero base ring: quotient, completions and étale conditions still make sense.
- Nilpotents and zero divisors in A or I are allowed. In particular no regularity of
  any generator enters the statement.

Searches made (using the prescribed msearch wrapper): LeanFinder for algebraization
of a complete algebra with torsion completed-conormal cohomology returned smooth
lifting, flatness and completion API, but no matching algebraization statement.
Loogle `AdicCompletion, MvPolynomial.pderiv` returned 0 hits.
LeanSearch for continuous partial derivatives and the completed polynomial conormal
map found `MvPolynomial.pderiv`, `Ideal.Cotangent` and ordinary Kähler differentials;
these are reused, but do not supply the completed arrow. LeanFinder for that arrow
returned ordinary polynomial cotangent maps, not a completion map. The Mathlib
RingTheory grep `AdicCompletion.*(deriv|pderiv)|(deriv|pderiv).*AdicCompletion` had no hits.
Direct rg searches in WeilConjectures and lean/Sheaf for `rigPolynomialCompletion`,
`rigJacobian`, `completedConormal`, `completedPolynomial`, and `CompletedPolynomial`
had no matches. Searching the item's ID in WeilConjectures found no declaration.
`tools/blueprint_refs.py search 'completed conormal differential'` returned zero
blueprint nodes. DAG text searches found the item and sibling statements that use
the same notion, but no definition node for it. The existing
`CompletedDifferentialFiniteConormal` module was read: it states finite completed
Kähler differential properties over local rings, not this completed-polynomial map.
The exact new-node search outputs are recorded in its `mathlib_searches`.

No STATEMENT-DISPUTED finding or mathematical node correction is needed.

## New nodes

`def-per-completed-polynomial-conormal` defines the continuous partial derivatives
on the completion of A[x_1,...,x_r] and the induced conormal arrow J/J² → (P/J)^r.
Source: the completed naive cotangent presentation (NL) and Tag 0AJU in
`restricted.tex`. The searches above found no existing completed arrow or DAG
owner. The node cites the Noetherian-ring, polynomial-ring and completion nodes;
it uses Mathlib's `Ideal.Cotangent` rather than defining J/J² again.
Its module records six declarations, including the two named proof obligations
needed by its constructions. `existsUnique_rigPartialDerivative` characterizes an
extension uniquely as an A-linear filtration-preserving extension of polynomial
partial differentiation. The subsequent choice takes that unique map, so it is
permitted unique-data choice, not an unspecified object from a mere existence claim.
The second obligation says the raw map kills J², and is exactly the well-definedness
condition for `Submodule.liftQ`. Both proofs are postponed with source and proof
plans in their docstrings, owned by this definition node. The other definitions have
actual bodies. The two proof obligations are included in the node's mathematical
statement and `lean.declarations`.

## Second reading by Q93

A separate pass by this worker reread the node, source, and both modules. The
dispatcher expressly prohibits starting another agent; no independent worker is
claimed here. The maintainer will provide the independent delivery review.

The second pass matched the ring, ideal, finite variables, completed presentation,
complete quotient, common exponent, both annihilation conditions, finite-type
model, étale complement, and A-algebra completion isomorphism as detailed above.
It found and repaired the retained draft's incorrect kernel condition (it had
multiplied the entire source into the kernel instead of annihilating the kernel),
its attempt to complete a partial derivative as a polynomial-linear map, and its
private replacement of Mathlib's conormal quotient. The construction now uses
unique continuous A-linear extension and `Ideal.Cotangent`. The zero-variable,
zero ideal, unit ideal, zero quotient and exponent-zero cases are all included.
The localized étale map is canonical and is stated using the recorded scheme
notion. The new node changes neither the item nor its source statement; the only
added dependency supplies the notion explicitly used in its hypotheses.
