## Worker report

The module `Sheaf.RingTheory.LocalEssentiallyFiniteTypePolynomialCover` states
`Algebra.exists_local_essentially_finite_type_polynomial_cover`. Its only theorem proof is
`sorry`. There are no new definitions, new nodes, dependency repairs, or statement changes.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0GSG,
`lemma-mod-injective-valuation-ring`, lines 5044–5071, especially the reduction writing B as a
quotient of a polynomial algebra localized at a prime. This algebraic reduction does not use
the valuation-ring hypothesis of the surrounding module-injectivity lemma, as the accepted
node's six-step proof makes explicit. That full proof is reproduced in the declaration's
docstring, including the construction of the prime, the fraction map, its surjectivity,
both locality equalities, and the empty-relation presentation.

Clause-by-clause correspondence:

- The two commutative local rings are `{A : Type u} {B : Type v}` with `[CommRing A]`,
  `[CommRing B]`, `[IsLocalRing A]`, and `[IsLocalRing B]`. Their universes are independent.
- The homomorphism φ is the structure map of `[Algebra A B]`, namely `algebraMap A B`.
  Every homomorphism of commutative rings defines such an algebra structure. The named
  hypothesis `hlocal` is exactly `Ideal.comap (algebraMap A B) (maximalIdeal B) =
  maximalIdeal A`; no extra property of φ is assumed.
- Essential finite type is `[EssFiniteType A B]`, the dependency's Mathlib class.
- The integer n ≥ 0 is `n : ℕ`. The polynomial algebra P is literally
  `MvPolynomial (Fin n) A`, allowing the empty list of variables.
- The prime ideal is `q : Ideal (MvPolynomial (Fin n) A)` with the existential proof
  `(_ : q.IsPrime)`. This proof is bound before `Localization.AtPrime q` is used.
- The surjective A-algebra map is `π : Localization.AtPrime q →ₐ[A] B` with
  `Function.Surjective π`. Its AlgHom type enforces π composed with the A-structure map
  equals the given φ; there is no unrelated A-action or arbitrary ring map.
- The locality of A → P_q is the first conclusion's `Ideal.comap` equality, using the
  canonical A-algebra structure on the polynomial localization. The locality of π is
  the second `Ideal.comap` equality. The displayed `maximalIdeal (Localization.AtPrime q)`
  is exactly qP_q, as `Localization.AtPrime.map_eq_maximalIdeal` states. Thus both equalities
  give precisely the ideals named by the node.
- The final clause is written out as an existential finitely presented commutative
  A-algebra C, a submonoid W of C, and `Nonempty (Localization W ≃ₐ[A]
  Localization.AtPrime q)`. Here `FinitePresentation A C` is the recorded dependency's
  predicate. This is exactly being a localization of a finitely presented A-algebra,
  with compatibility over A built into the isomorphism. It does not assert finite
  presentation of B or finite generation of the kernel of π. The witness can be P itself,
  which lives in `Type u`; choosing C in that universe excludes no input rings or case
  of this polynomial-localization assertion. No independent-universe test-object
  quantifier or size restriction on B occurs.

Dependency declarations read and used:

- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`, with its definition
  through a finite adjoin and localization; `Algebra.essFiniteType_iff_exists_subalgebra`
  identifies this with the node's presentation as the localization of a finite type algebra.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` (the finitely supported monomial
  algebra); its `MvPolynomial.algHom_ext` signature and the evaluation signature
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` were also read. The statement
  only needs the polynomial algebra itself.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, with complement
  submonoid `q.primeCompl`, its local-ring instance, and
  `Localization.AtPrime.map_eq_maximalIdeal` for the extended prime ideal.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, whose signature
  is a finite-variable polynomial surjection with finitely generated kernel.
- Proof dependency `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType` and
  `Algebra.FiniteType` in `Mathlib.RingTheory.FiniteType`.
- Proof dependency `lem-weil-pbc-local-ring-unit-criterion`:
  `IsLocalRing.notMem_maximalIdeal` in `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`.
- Proof dependency `lem-weil-pbc-ring-localization-universal-property`:
  `IsLocalization.lift` and `IsLocalization.ringHom_ext` in
  `Mathlib.RingTheory.Localization.Defs`.

All four statement-dependency modules are public imports. The remaining three proof
modules are direct plain imports. No dependency record is replaced.

Edge cases checked before writing:

- n = 0 is allowed by `Fin 0`, so the polynomial algebra is the base ring, and the
  final finite presentation may use no relations. For example, A → A uses q = m_A.
- When B is a field, its maximal ideal is zero and q is the kernel of polynomial
  evaluation; the localized surjection and locality still have the stated meaning.
- No Noetherian, domain, injectivity, flatness, valuation, or finitely generated kernel
  condition is imposed on A, B, or φ. Non-Noetherian local bases and non-finitely
  generated quotient ideals are included.
- Zero rings are excluded precisely by the existing `IsLocalRing` definition (a unique
  proper maximal ideal), consistently with the source's local-ring convention.
- A and B need not have equal universes. The polynomial localization has the base's
  universe; a surjection to B is a function across universes and imposes no extra
  universe equality. The small finitely presented witness is the polynomial ring.

Searches for an existing full statement (all via msearch unless otherwise stated):

- LeanFinder: “A local essentially finite type algebra over a local ring is a quotient
  of a polynomial ring localized at a prime, with both homomorphisms local”. Eight hits,
  including `Algebra.EssFiniteType.cond`, `.isLocalization`, `.of_isLocalization`,
  `Algebra.essFiniteType_iff_exists_subalgebra`, and `RingHom.finiteType_isLocal`.
  These express localization/finite generation or localness of a morphism property;
  none gives the local surjective polynomial cover and essential presentation clause.
- Loogle: `Algebra.EssFiniteType, IsLocalHom`. Six hits, all concerning formally
  unramified algebras and residue fields/maximal ideals, not this assertion.
- Mathlib grep: `EssFiniteType.*(surj|exists|quotient)|exists.*(surj|quotient).*EssFiniteType`
  in `RingTheory`. Four hits in `EssentialFiniteness.lean`: the finite-subalgebra
  description and preservation under surjections/quotients. Read the signatures;
  none constructs a polynomial cover.
- LeanSearch: “A local essentially finite type algebra admits a surjective algebra map
  from a prime localization of a finite variable polynomial ring”. Eight hits, including
  `Algebra.FiniteType.iff_quotient_mvPolynomial''`, `Algebra.EssFiniteType.of_surjective`,
  and `.of_isLocalization`; none is the full essentially finite type local cover.
- Project rg in `lean/WeilConjectures` and `lean/Sheaf`: searched the item id,
  `EssFinitePresentation`, essential finite presentation phrases, local polynomial cover
  phrases, and proposed declaration names. The item id occurs only as a proof citation
  in `FiniteSourceFibreInjectiveFlatTarget.lean`, not as a declaration.
- Read the nearby `Algebra.EssFiniteType.exists_polynomial_maximal_localization_quotient`
  in `Sheaf.RingTheory.ClosedFibrePolynomialPresentation`. It permits a nonlocal
  structure map and gives a further localization of a quotient of a maximal-ideal
  localization, not the prime-localization surjection and two locality conclusions here.
- The essential-presentation phrase search also found Mathlib's
  `RingTheory/Smooth/Fiber.lean`, explicitly documenting that there is no dedicated
  essential finite presentation class. Its finitely presented algebra/localization
  encoding agrees with the existential clause used here. No duplicate predicate is added.

Validation: `scompile.py` compiled the delivered module both in its sandbox probe and at
its library module path with no errors or warnings. `set_option autoImplicit false`
checks every variable is explicitly bound. The node's `lean.statement` is extracted
verbatim from the theorem signature. No statement dispute or node fault was found.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
