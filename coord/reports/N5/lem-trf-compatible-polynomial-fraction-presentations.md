## Worker report

The module `Sheaf.RingTheory.CompatiblePolynomialFractionPresentations` states
`Algebra.exists_compatible_polynomial_fraction_presentations`, with `sorry` as its only
proof. No definitions, new nodes, dependency repairs, or statement corrections are needed.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Commutative k-algebras P and Q, essentially of finite type | Independent `Type v` and `Type w` binders, `CommRing`, `Algebra k`, and `EssFiniteType k` instances |
| Arbitrary commutative k-algebra A | `(A : Type z) [CommRing A] [Algebra k A]` |
| Surjective k-algebra maps u and v | `u : P →ₐ[k] A`, `v : Q →ₐ[k] A`, `hu : Function.Surjective u`, `hv : Function.Surjective v` |
| Nonnegative finite lengths r, s | `∃ (r s : ℕ)` |
| Families p, q and their cross-lifts | `p : Fin r → P`, `q : Fin s → Q`, `qLift : Fin s → P`, `pLift : Fin r → Q` |
| D = k[x_i,y_j] and maps f, g | `MvPolynomial (Fin r ⊕ Fin s) k` with existential algebra homomorphisms f and g |
| f(x_i) = p_i | First universal conjunct, `f (MvPolynomial.X (Sum.inl i)) = p i` |
| f(y_j) = q-tilde_j | Second conjunct, `f (MvPolynomial.X (Sum.inr j)) = qLift j` |
| g(x_i) = p-tilde_i | Third conjunct, `g (MvPolynomial.X (Sum.inl i)) = pLift i` |
| g(y_j) = q_j | Fourth conjunct, `g (MvPolynomial.X (Sum.inr j)) = q j` |
| Images of the cross-lifts agree | Fifth and sixth conjuncts, `u (qLift j) = v (q j)` and `v (pLift i) = u (p i)` |
| Equal composites, denoted h in the node | `u.comp f = v.comp g`; h is an abbreviation for this common map, not additional data |
| Every p has a first-block numerator and unit denominator | `∀ x : P, ∃ a t : MvPolynomial (Fin r) k`, followed by `IsUnit (f (MvPolynomial.rename Sum.inl t))` and the specified multiplication identity |
| Every q has a second-block numerator and unit denominator | `∀ y : Q, ∃ c z : MvPolynomial (Fin s) k`, followed by `IsUnit (g (MvPolynomial.rename Sum.inr z))` and the specified multiplication identity |
| No locality or regularity | Neither predicate is a binder |
| Empty sequences allowed | Both lengths range over all naturals; no positivity hypothesis |

The block inclusions are Mathlib's `MvPolynomial.rename Sum.inl` and
`MvPolynomial.rename Sum.inr`. These embed the polynomial subalgebras by extending
monomial exponents by zero on the other block. Thus quantifying the numerators and
denominators before applying these inclusions expresses precisely membership in the
specified polynomial subalgebras, rather than allowing arbitrary mixed polynomials.

Dependency declarations read and used:

- `def-weil-pbc-essentially-finite-type-algebra`: its Mathlib match is
  `Algebra.EssFiniteType` in `Mathlib.RingTheory.EssentialFiniteness`. Read its class,
  docstring, `Algebra.essFiniteType_iff`, and
  `Algebra.essFiniteType_iff_exists_subalgebra`. The last identifies exactly the
  localization-of-finite-type-algebra condition in the node.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and `MvPolynomial.algHom_ext`
  from `Mathlib.Algebra.MvPolynomial.Basic`, plus `MvPolynomial.aeval` from
  `Mathlib.Algebra.MvPolynomial.Eval`; the public Rename import exposes these.
  Read the full signatures and docstrings and the definition of `MvPolynomial.rename`.
- Proof dependency `def-weil-pbc-finite-type-algebra`: its recorded ring-map declaration
  is `RingHom.FiniteType` in `Mathlib.RingTheory.FiniteType`. This module is imported
  for the postponed proof. Read `Algebra.FiniteType.iff_quotient_mvPolynomial''`, the
  polynomial-surjection form used in that proof. The other two proof dependencies
  are already public imports because they also occur in the statement.

Source check: read Stacks Algebra `definition-essentially-finite-p-t` (00QM) and
`lemma-lci-local` (00SF), including the proof's localized polynomial presentations.
The simultaneous compatible-map construction is the agent refinement explicitly
identified by this node, not a claim that Stacks prints this precise lemma. The
declaration docstring includes all four proof steps: localization models and finite
generators; cross-lifts and polynomial universal property; first-block fractions;
second-block fractions, including the empty and zero-ring cases.

Edge cases checked mathematically before writing: r = 0 and s = 0 give the coefficient
algebra for the respective block and vacuous variable equations. Zero P or Q is allowed
and forces A to be zero by the existence of the corresponding ring map; in the zero
ring the unique element is a unit, so the fraction clauses remain meaningful. Nonzero
P and Q with A zero are also included; their composites agree automatically but their
fraction clauses still assert real content. There is no domain, local-ring, regularity,
nonzero-target, finite-type-target, or characteristic restriction. The four carrier
universes are independent and explicitly bound; finite polynomial variables impose
no equality among them. No statement dispute or node fault was found.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: “A common finite polynomial algebra maps compatibly to two essentially
  finite type algebras surjecting onto the same algebra, with unit denominator fractions
  in two variable blocks”. Eight hits, including `Algebra.FiniteType.iff_quotient_mvPolynomial''`
  and `Algebra.Generators.toAlgHom_ofComp_surjective`; none supplies this simultaneous
  conclusion and both fraction clauses.
- Loogle: `Algebra.EssFiniteType, MvPolynomial`. Zero hits.
- LeanSearch: “Two essentially finite type algebras surject onto the same algebra and
  admit compatible finite polynomial presentations with unit denominators”. Eight hits,
  including `Algebra.EssFiniteType.of_surjective` and finite-type presentation tools;
  none is this statement.
- Mathlib grep through the wrapper:
  `essFiniteType_iff|iff_quotient_mvPolynomial|rename.*AlgHom` under `RingTheory`.
  Twenty-five hits, identifying the individual finite-type and essential-finite-type
  presentation criteria. Read their source; neither combines the two algebras and lifts.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `compatible.*polynomial|polynomial.*fraction|essFiniteType_iff|EssFiniteType`.
  Hits concern individual presentations and other fraction constructions; the existing
  CI-kernel-invariance consumer describes this construction in its proof but has a
  different theorem statement. A narrower file-list search for the first two patterns
  was also inspected. No existing exact statement was found.
- Direct `rg` for the item id under `lean/WeilConjectures`: zero hits.
  Direct `rg` for `exists_compatible_polynomial_fraction_presentations` and
  `compatiblePolynomialFractionPresentations` in both libraries and
  `dag/lean_names_upstream.json`: zero hits.

## Second reading by N5

This is a second pass by the same worker; the dispatcher's brief prohibits starting
another agent. The maintainer supplies the independent delivery review.

Reopened the node and the finished module and compared every row of the correspondence
table. The six variable/lift equations have the correct domains, codomains and order;
the seventh conjunct is equality of the two algebra homomorphisms to A. The final two
conjuncts use the first block with f and the second block with g throughout, including
both numerator and denominator. The multiplication order matches the node. The symbol
h introduces no extra requirement because it merely names the equal composites.
All universes and all variables are explicit, and no typeclass restricts A, P or Q to
be nonzero. No mismatch was found and no statement change was needed.
