## Worker report

The module `Sheaf.RingTheory.PolynomialPresentationMPseudoCoherence` states
`DerivedCategory.isMPseudoCoherent_restrictScalars_polynomial_presentation_iff`.
Its only theorem proof is `sorry`; it introduces no definitions or auxiliary theorems.
The original node's statement, dependencies and proof plan are unchanged.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-relatively-pseudo-coherent` (Tag 065H), especially the two finite polynomial
presentations, their common polynomial ring and the induction in the proof;
`lemma-add-variable-pseudo-coherent` (Tag 065G) supplies the evaluation input.
The fixed-degree statement is the equivalence (1) and (2) of 065H for two specified
presentations. A surjective finite polynomial presentation already implies finite
type, so no additional finite-type hypothesis is necessary.

Hypotheses and clauses, matched individually:

- Commutative rings R and A are `{R : Type uR} {A : Type uA} [CommRing R]
  [CommRing A]`. Their universes are independent.
- The common R-algebra structure is `[Algebra R A]`. The two maps are
  `α : MvPolynomial (Fin r) R →ₐ[R] A` and
  `β : MvPolynomial (Fin s) R →ₐ[R] A`, so they agree on the prescribed coefficients.
- The finite numbers of variables, including zero, are `{r s : ℕ}`.
  `Fin r` and `Fin s` simply index the displayed variables from zero.
- The two surjectivity hypotheses are exactly `hα : Function.Surjective α`
  and `hβ : Function.Surjective β`. Neither kernel is required to be finitely generated.
- An arbitrary integer is `(m : ℤ)`; exactly that same `m` appears on both sides.
- An arbitrary derived object is
  `K : DerivedCategory (ModuleCat.{max uR uA v} A)`.
  The three `HasDerivedCategory` binders specify the chosen localizations D(A),
  D(P) and D(Q), with independent morphism universes `wA`, `wP`, `wQ`.
  The common module-carrier universe `max uR uA v` can be arbitrarily large and
  contains both coefficient rings; it does not identify ring or localization universes.
- The left clause is `IsMPseudoCoherent m
  ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)`.
  The right clause is the identical expression with β; `↔` is the asserted equivalence.
- Restriction is the existing `ModuleCat.restrictScalars`, whose `RestrictScalars.obj'`
  keeps the module carrier and additive group and uses `Module.compHom` for the action;
  `RestrictScalars.map'` keeps the underlying linear-map function. Thus its termwise
  complex functor keeps groups and differential functions. Its exactness instances
  from `ChangeOfRingsExact` supply preservation of finite limits and colimits.
  `Functor.mapDerivedCategory` is the induced localization of precisely that complex
  functor, with `mapDerivedCategoryFactors` specifying the representative comparison.
  It therefore uses the stated exact restriction, preserving quasi-isomorphisms,
  rather than an arbitrary functor or an assumed comparison.
- Zero variables and zero rings are allowed: there is no positivity or nontriviality
  binder. There is no flatness, finite presentation, Noetherian or boundedness binder.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring` records `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`. Read its definition as `AddMonoidAlgebra R (σ →₀ ℕ)` and
  `MvPolynomial.algHom_ext` in Basic, and the evaluation signature and docstring
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`.
- `def-weil-abstract-derived-category` records
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`. Read their full signatures, localization docstrings and `Q`.
  This module is publicly imported through the exact-functor and pseudo-coherence modules.
- `def-pc-ring-m-pseudo-coherent` records
  `WeilConjectures.RingTheory.MPseudoCoherent`, `DerivedCategory.IsMPseudoCoherent`.
  Read its full definition: a bounded finite-free complex maps to the object, with
  cohomology isomorphisms above m and an epimorphism in degree m. This definition is
  used directly, without a second definition.
- The proof dependency `def-pc-ring-pseudo-coherent-complex` is imported privately as
  `WeilConjectures.RingTheory.RingPseudoCoherent`; its `IsPseudoCoherent` definition
  supplies the meaning of the bounded-above finite-free model in the proof plan.
- The other proof dependency,
  `lem-sfb-m-pseudocoherent-algebra-scalar-restriction`, currently has no Lean record,
  so there is no module to import for it. Its statement was read and is cited in the
  proof docstring exactly as in the accepted DAG proof. It is not needed to type this
  statement. All already recorded statement-dependency interfaces are usable.
- Additional Mathlib infrastructure used directly is
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` (ordinary restriction and
  exactness) and `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
  (`CategoryTheory.Functor.mapDerivedCategory` and its termwise characterization).

Edge cases checked before drafting: r = s = 0 gives the two coefficient presentations;
r = 0 or s = 0 leaves one of the proof's finite inductions at its base case.
For A = 0 the zero complex and both surjections are allowed, with no `[Nontrivial A]`.
R = 0 forces any R-algebra A to be zero, also allowed. The evaluation argument does not
assume b is regular: over Z/4 with b = 2, the coefficient in the next degree still proves
injectivity of multiplication by t-b. Negative, zero and positive m all use the same
unrestricted integer binder. K = 0 and unbounded K are admitted. No statement fault or
STATEMENT-DISPUTED issue was found.

Searches performed for this delivery (using the prescribed msearch wrapper):

- LeanSearch, `Fixed degree pseudo coherence is independent of finite polynomial
  presentations of an algebra`: eight results, concerning ordinary finite presentation
  and quasicoherent sheaves, not fixed-degree derived pseudo-coherence.
- LeanFinder, `For two finite polynomial presentations of the same algebra a derived
  complex is m pseudo coherent over one if and only if it is over the other`: eight
  results, ordinary polynomial/algebra/module finite presentations and smooth presentations;
  none states this derived equivalence.
- Loogle, `"PseudoCoherent", MvPolynomial`: zero results.
- Mathlib grep, `pseudo.?coher|mPseudoCoherent`: zero results.
- Direct `rg` of the project and upstream source for polynomial-presentation and
  pseudo-coherence terms found the all-degrees statement in
  `Sheaf.RingTheory.PolynomialPresentationPseudoCoherence`, which was read in full;
  it asserts `IsPseudoCoherent`, not the fixed-m assertion of this item. It is not
  an exact match. The scheme-level affine-embedding statement is likewise a different
  statement on different objects. `RelativeMPseudoCoherent` defines an existential
  presentation predicate, not presentation independence.
- Direct `grep -rn` of the upstream source for this node ID returned no matches.
  `rg` for `isMPseudoCoherent_restrictScalars_polynomial_presentation_iff` in
  Mathlib, upstream sources, project sources and `dag/lean_names_upstream.json`
  returned no matches. No existing declaration was duplicated.

A second pass over the node and the completed signature checked each of the binders
and both clauses above. It confirmed that the fixed integer is unchanged, the two
maps preserve the same R-algebra structure, and no boundedness or finiteness of
relations slipped into the signature. The full four-step accepted proof appears
in the theorem docstring, including the evaluation resolution, common action and
both finite inductions. No correction, dependency repair or new node is needed.

Validation: `scompile.py` compiled this file cleanly as a sandbox module (4.8 s)
and as its library module (2.3 s), with no warnings or errors. The prescribed
`deliver2.py --no-push` printed `OK (dry run)` and confirmed that the packet passes
the server preflight and compiles. A local record comparison confirmed that only
the node's `lean` field changed, the recorded signature is verbatim, all Lean lines
are at most 100 characters, and the sole postponed proof is the named theorem above.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
