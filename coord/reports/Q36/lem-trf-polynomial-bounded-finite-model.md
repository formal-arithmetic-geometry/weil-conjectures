## Worker report

States `DerivedCategory.exists_bounded_finite_model_polynomial_scalarExtension` in
`Sheaf.Algebra.Homology.PolynomialBoundedFiniteModel`. Its sole proof is `sorry`;
there are no new definitions, dependency repairs, or statement corrections.

Read Stacks `dualizing.tex`, `lemma-shriek-boundedness` (0BZK), especially its proof's
assertion that polynomial derived scalar extension preserves bounded coherent objects.
The node expands that assertion into a bounded finite representative. Read the whole
item and every statement dependency, its record, and the corresponding declaration and
docstring. The ordinary-module interface in the current record of
`lem-pur-derived-change-of-rings` is already usable, without a one-point-site wrapper.

Hypothesis and clause correspondence:

- A commutative Noetherian ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- The nonnegative number of variables is `(n : ℕ)`, including zero. The specified
  polynomial algebra is `MvPolynomial (Fin n) R`; using `Fin n` merely labels its n
  variables from zero. Its canonical structure map is `MvPolynomial.C`.
- The object in the ordinary module derived category is
  `(K : DerivedCategory (ModuleCat.{u} R))`. The imported ordinary-module construction
  uses the canonical small-Hom derived categories, for arbitrary universe `u`.
- `_hbounded` chooses integers `l t` with `l ≤ t` and asserts
  `IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj K)` for `i < l ∨ t < i`.
  Thus it says exactly that cohomology vanishes outside a finite interval.
- `_hfinite` requires `Module.Finite R` of that same cohomology module for every integer.
- The existential binders choose integers `a b` and
  `G : CochainComplex (ModuleCat.{u} (MvPolynomial (Fin n) R)) ℤ`.
  This is the ordinary-module presentation of the node's explicitly specified
  one-point ringed-site specialization, with P-linear differentials.
- `a ≤ b` supplies the ordered endpoints. The next conjunct asserts `IsZero (G.X j)`
  whenever `j < a ∨ b < j`. The following conjunct requires every `G.X j` to be
  `Module.Finite (MvPolynomial (Fin n) R)`.
- The last conjunct is `Nonempty (Q.obj G ≅ ...obj K)`: an isomorphism in D(P), with
  the exact orientation Q_P(G) to derived scalar extension of K. Here `Q` is the
  localization at quasi-isomorphisms, and the target is the recorded
  `ModuleCat.ordinaryDerivedExtendScalars (MvPolynomial.C : R →+* ...)`.
- No perfectness, flatness of K, finite Tor dimension, free terms, or projective terms
  occur in either the hypotheses or the conclusion.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finite).
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.C`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` supplies its
  `DerivedCategory.homologyFunctor`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.ordinaryDerivedExtendScalars`; read its full signature and the
  `OrdinaryDerivedChangeOfRings` universal pair, K-flat computation, and choice definition.
  Its uniquely characterized universal pair is the already supplied ordinary-module
  realization of the generic ringed-site change of rings, not an arbitrary functor.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- Proof-only imports preserve the recorded plan:
  `Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`, theorem
  `DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`;
  `WeilConjectures.RingTheory.RingPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`;
  `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`,
  `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`.

Edge cases checked before writing:

- n = 0 is allowed; polynomial scalar extension is along the canonical map to the
  polynomial algebra with no variables, canonically the original ring.
- K = 0 admits the zero complex and a = b = 0. No nonzero cohomology is required.
- The zero ring is allowed: no `Nontrivial` hypothesis occurs.
- An interval of length zero is allowed; strict inequalities do not exclude endpoints.
- For R = Z/4 and K = (Z/2)[0], the input is bounded finite but non-perfect; the conclusion
  permits its finite, nonprojective bottom term. The truncation proof never asserts that
  this quotient is free or flat.
- If the finite free representative's upper term bound v lies below l, choosing
  b = max l v still gives a ≤ b; the resulting complex can be zero.

Searches actually run:

- `msearch.py ... leanfinder`: "Polynomial scalar extension of a bounded complex with
  finite cohomology over a Noetherian ring has a bounded complex of finite modules as a
  representative" returned eight hits: FGModuleCat finite limits, adic completion,
  Rep standard complex, local cohomology diagram, strict-support extension,
  finite cotangent H1, vanishing Rep Tor, and Rep resolution Ext comparison.
  None states this result.
- `msearch.py ... loogle "MvPolynomial, CochainComplex"`: zero hits.
- `msearch.py ... grep "polynomial.*(cohomolog|homology)|bounded.*finite.*(model|represent)|pseudo.?coherent"`:
  zero Mathlib hits.
- `rg` of the same concept pattern in `lean/WeilConjectures` and `lean/Sheaf` finds
  proof discussions and related finite projective models, but no exact declaration.
  Read `Sheaf.CategoryTheory.DerivedCategory.NoetherianFlatComplexPerfect`: it assumes
  a bounded flat representative and concludes projective terms, so it is not this item.
  Read `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` in Mathlib's TStructure:
  it provides bounded terms without finite generation, so it is not an exact match.
- `grep -rn "lem-trf-polynomial-bounded-finite-model" lean/WeilConjectures`: no match.
- `rg` for `polynomial.*bounded.*finite|bounded.*finite.*polynomial|exists_bounded_finite.*model`
  in both project roots and `dag/lean_names_upstream.json`: only related results with
  different hypotheses; no theorem naming this result. The final declaration name and
  module name were also checked in those roots and upstream names with no collision.

Validation: prescribed `scompile.py` compiled both its sandbox form and actual module
successfully (6.5 s and 10.7 s); no errors or warnings were printed.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q36

Performed a separate rereading of the node and the completed file. This is a worker
self-check, not an independent-agent review: the dispatcher brief forbids spawning
other agents and assigns the independent review to the maintainer.

Matched R and its two classes, natural n, the exact canonical ring map, K in D(R),
both cohomology hypotheses, all three existential objects, ordered term bounds,
termwise vanishing, termwise finite generation, and the derived isomorphism.
In particular, the isomorphism is in D(P), not just a family of cohomology isomorphisms;
the only module category is the ordinary P-module category the node requests.
No mismatches were found and no statement changes were needed. The four numbered
proof steps in the docstring reproduce the node's finite-free/K-flat, monomial,
and cokernel-truncation argument, including the incoming image in degree a+1.
