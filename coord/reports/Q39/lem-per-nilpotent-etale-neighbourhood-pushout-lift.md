## Worker report

The module `Sheaf.AlgebraicGeometry.NilpotentEtaleNeighbourhoodPushoutLift` states
`AlgebraicGeometry.exists_nilpotent_etale_neighbourhood_pushout_lift` with `sorry`.
It introduces no definition. I read the entire statement and proof of Stacks Tag 0ALT,
`restricted.tex`, `lemma-lift-approximation`, and all five statement-dependency records
and their recorded declarations and docstrings. The source chapter is Algebraization
of Formal Spaces. No statement correction or dependency repair is needed.

Hypothesis and conclusion correspondence:

- A commutative Noetherian base is `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- The two ideals are `(I J : Ideal A)`. Nilpotence is exactly
  `hJ : ∃ N : ℕ, 1 ≤ N ∧ J ^ N = ⊥`.
- The notation A₀ = A/J is expanded as `A ⧸ J` everywhere.
- C is a commutative A-algebra through `[CommRing C] [Algebra A C]`;
  `hCft : (algebraMap A C).FiniteType` is its finite type condition.
- B₀ is a commutative A₀-algebra through `[CommRing B₀] [Algebra (A ⧸ J) B₀]`;
  `hB₀ft : (algebraMap (A ⧸ J) B₀).FiniteType` is its finite type condition.
- C₀ = C/JC is literally `C ⧸ J.map (algebraMap A C)`. Mathlib's
  `Ideal.Quotient.algebraQuotientMapQuotient` supplies its canonical A₀-algebra structure.
- `hC` asserts `Etale` of the restriction `∣_` of `Spec.map` of the structure map
  to the open complement of `PrimeSpectrum.zeroLocus (I : Set A)`.
  Thus only the inverse image of that base open is required to be étale.
- `hB₀` asserts exactly the analogous restriction over A₀, using
  `I.map (Ideal.Quotient.mk J)` for IA₀.
- `h₀ : B₀ →ₐ[A ⧸ J] C ⧸ J.map (algebraMap A C)` is the specified A₀-algebra map.
  `hh₀` says its map of spectra is étale, the affine form of an étale algebra map.
- `hI` says that the quotient map induced by h₀ is an A₀-algebra isomorphism:
  its witness `e` is an `AlgEquiv` between the quotients by the extensions of IA₀,
  and `∀ b : B₀, e (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (h₀ b)`
  forces it to be the induced map, rather than an unrelated isomorphism.
  Since quotient projections are surjective this characterizes that map uniquely.
  Extending IA₀ further is exactly IB₀ and IC₀, respectively.
- The conclusion existentially supplies `B : Type u`, `CommRing B`, `Algebra A B`,
  and `(algebraMap A B).FiniteType`.
- It supplies the actual A-algebra homomorphism `h : B →ₐ[A] C` and
  the A₀-algebra isomorphism `β : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A ⧸ J] B₀`.
- The first concluding `Etale` says that h is étale.
- The equality for every `b : B` is `qC (h b) = h₀ (β (qB b))`.
  Surjectivity of qB makes this precisely equality of the reduction of h with h₀ ∘ β.
  This formulation needs no extra well-definedness helper or chosen reduction map.
- The final `Etale` is the restriction of `Spec B → Spec A` to the same open
  complement of V(I), as required. It does not require global étaleness over A.

Dependency declarations reused:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (line 196).
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (line 217), also
  `Algebra.FiniteType` (line 39), which it uses with the induced algebra structure.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` (line 470) and
  `AlgebraicGeometry.Spec.map` (line 479).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` (line 41).
- `Mathlib.Algebra.Algebra.Hom`: `AlgHom` (line 30).
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`, quotient rings and their projections. These are supplied publicly
  by `Mathlib.RingTheory.Ideal.Over`, whose line 63 supplies the canonical quotient-base
  algebra instance. Ideal extension and powers are Mathlib's `Ideal.map` and `^`.
- Mathlib's `AlgebraicGeometry.morphismRestrict` (`Restrict.lean`, line 569)
  is the existing restriction to the inverse image of a base open.

Available proof dependencies are imported privately: the recorded upstream
`WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal`,
`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`, and Mathlib's separatedness and
finite-morphism modules; étale composition/cancellation is already publicly imported.
The six algebraic-space proof inputs with no Lean record or Mathlib match are not
imported: thickening base change, thickening étale-scheme equivalence, thickening
properties, the open/separated-étale pushout, the universal-pushout lemma, and finite
surjective affine-source descent. None is needed to type the statement. The docstring
records all seven proof steps and the DAG inputs for subsequent proof work.

Edge cases checked against the source and signature:

- J = 0 allows N = 1 and recovers the given reduction; J = top forces a zero base
  and is not excluded by a nontriviality assumption.
- I = 0 makes the complement empty, so both away-from-I hypotheses and the conclusion
  have their intended empty restriction. The mod-I isomorphism then retains its full
  force. I = top makes the complement the whole base and the mod-I quotients zero.
- Zero algebras and empty spectra are allowed: no `Nontrivial` or nonempty binder occurs.
- N = 1 is allowed and says J = 0. N = 0 is excluded exactly as in the node.
- Finite type allows an empty generator list, as required in the nilpotent lifting
  argument. No module-finiteness or finiteness of h has been substituted.
- A, C, B₀ and the output B share an arbitrary explicitly bound universe u, as in
  Mathlib's scheme category; there is no independent smaller test-object universe.
- Both quotient isomorphisms preserve the canonical A₀ structures, and the two
  elementwise equalities enforce the prescribed maps, including identity maps.

Searches actually run for this assignment:

- msearch LeanFinder: "Lift an etale neighbourhood across a nilpotent quotient of a
  Noetherian base with prescribed reduction and etale away from an ideal" returned
  eight hits, including `StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot`,
  `StandardEtalePair.lift`, `Algebra.exists_etale_of_isEtaleAt`, standard étale
  presentations and localization results. None has this pushout/algebraization statement.
- msearch Loogle: `IsNilpotent, Algebra.Etale` returned zero hits.
- msearch grep: `nilpotent.*pushout|pushout.*etale|lift.*approximation` returned zero hits.
- msearch LeanSearch: "Nilpotent lifting of an etale neighbourhood with prescribed
  reduction and an etale map to a fixed finite type algebra" returned eight hits:
  ordinary formally smooth lifting, standard étale lifting, étale loci and quasi-finite
  étale neighborhoods. None supplies the prescribed finite-type model in this statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for nilpotent lifting, étale
  neighborhoods, pushouts and the item id found no equivalent declaration. Nearby
  `FiniteEtaleLiftingApproximation` is a different henselian approximation result.
  The exact proposed declaration name was absent from both trees, Mathlib, and
  `dag/lean_names_upstream.json`.
- Targeted Mathlib searches and full source reads located the quotient-base algebra
  instance, the quotient-map interfaces, `morphismRestrict`, the spectrum map,
  Noetherian and finite type definitions, and `Etale`. No new notion is needed.

Validation: the delivered file was compiled with `scompile.py` against the live server
library in module mode, both as a sandbox module and at its actual library module path;
both passed with no errors or unexpected warnings. Every variable and universe is bound
explicitly, and `autoImplicit` is false. The only postponed theorem is this node's own
statement. The node copy changes only `lean`. No mathematical dispute was found.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
