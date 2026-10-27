## Worker report

The module `Sheaf.RingTheory.KoszulSubstitutionUnitModIdeal` states
`ExteriorAlgebra.koszul_substitution_unit_mod_ideal`, with its proof `sorry`.
It asserts existence of the chain map with every component prescribed to be the
exterior power of the given substitution, its quasi-isomorphy, and invertibility
of its specified image in the derived category. No definitions, helper nodes,
dependency repairs, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- The commutative ring is `(A : Type u) [CommRing A]`, including the zero ring.
- The nonnegative length is `(r : ℕ)`, and the two tuples are `(a b : Fin r → A)`.
  `Fin r` relabels the source's one-based indices without changing the tuple.
- The common ideal is `(I : Ideal A)`, with
  `ha : Ideal.span (Set.range a) = I` and
  `hb : Ideal.span (Set.range b) = I`. These are both equalities in the node.
- The free module E is exactly the dependency's `Fin r →₀ A`.
  Its standard vector is `Finsupp.single i 1`. The dependency constructs alpha
  and beta as `Finsupp.linearCombination A a` and `Finsupp.linearCombination A b`.
- The map is `t : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A)`, with the exact compatibility
  `ht : (Finsupp.linearCombination A a).comp t = Finsupp.linearCombination A b`.
- The matrix's row-i, column-j entry is `t (Finsupp.single j 1) i`, the i-th
  coordinate of t(e_j). Its `Matrix.det` is the determinant in the standard basis.
  The condition `hδ : IsUnit (Ideal.Quotient.mk I (Matrix.det ...))` asks only
  for invertibility in A/I, never invertibility in A.
- `∃ T : koszulComplex A r b ⟶ koszulComplex A r a` states that the exterior
  powers form a chain map with exactly the direction in the node.
- `∀ q : ℕ, (T.f q).hom = exteriorPower.map q t` prescribes every component,
  including q=0 and q>r. Thus T is uniquely determined as a complex morphism;
  this existential does not permit choosing an arbitrary comparison.
- `QuasiIso T` is precisely the isomorphism condition on every homology map.
- `IsIso (DerivedCategory.Q.map (HomologicalComplex.extendMap T
  ComplexShape.embeddingDownNat))` expresses the equivalent derived conclusion
  for this same map. The embedding sends q to -q and extends by zero in positive
  cochain degrees. Both equivalent assertions are included explicitly.
- `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` is the chosen localization size
  in the recorded derived-category dependency, with independent explicit u,w.
  It is size infrastructure, available with `HasDerivedCategory.standard`,
  rather than an algebraic condition on A.
- No regularity, properness, Noetherianity, locality or nontriviality instance
  occurs anywhere in the theorem.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.KoszulComplex`:
  `ExteriorAlgebra.koszulComplex`, its terms, `koszulBoundary`, and the fixed
  contraction by `Finsupp.linearCombination`. This is the actual recorded module,
  replacing the historical Sheaf path in the STATE convention.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`. Read their signatures and docstrings.
- `Mathlib.Algebra.Homology.Embedding.Extend`:
  `HomologicalComplex.extendMap` and `HomologicalComplex.extend`.
- `Mathlib.LinearAlgebra.ExteriorPower.Basic`: `exteriorPower.map`, the existing
  exterior-power functor, with its action on decomposable wedges.
- Statement notation uses Mathlib's `Matrix.det`, `Ideal.span`,
  `Ideal.Quotient.mk`, and `QuasiIso`; the coordinate matrix is written directly
  from standard basis vectors, requiring no determinant helper definition.
- Proof imports cover every recorded proof dependency: the recorded modules
  `WeilConjectures.AlgebraicGeometry.KoszulDifferential`
  (`ExteriorAlgebra.koszul_differential`),
  `WeilConjectures.RingTheory.KoszulGeneratorHomotopy`
  (`ExteriorAlgebra.koszul_generator_homotopy`), and Mathlib's
  `LinearAlgebra.ExteriorAlgebra.Basic` (`ExteriorAlgebra`, `ι`, `exteriorPower`),
  `Algebra.Module.LocalizedModule.Basic` (`LocalizedModule`),
  `LinearAlgebra.ExteriorPower.Basis` (`Module.Basis.exteriorPower`),
  `LinearAlgebra.Matrix.Adjugate` (`Matrix.adjugate_mul`, `Matrix.mul_adjugate`),
  `Algebra.Module.LocalizedModule.Exact` (`IsLocalizedModule.map_exact`).
  Their full signatures and relevant docstrings were read in the source.

The theorem docstring follows all six proof steps: construction by the contraction
formula, ideal annihilation by generator homotopies, determinant localization
and adjugate inverse, natural homology/localization comparison, explicit inverse
to localization on homology, and the derived-localization conclusion. The source
was read directly in `literature/stacks-project/more-algebra.tex`, Tag 066A,
second proof paragraph, and Tag 0624. Nothing is proved in the delivered module.

Edge cases checked before writing:

- r=0: the matrix is empty with determinant 1; I=0; K has A only in degree zero.
  Its specified exterior-power map is the identity.
- Zero ring: all modules vanish and every displayed map is invertible; the unit
  condition in the zero quotient is valid. No `Nontrivial A` is imposed.
- I=A: the quotient is the zero ring, so the unit condition permits even a
  noninvertible determinant in A. Both Koszul complexes are acyclic by generator
  homotopies; their specified comparison is a quasi-isomorphism.
- I=0: all generators vanish, and the hypothesis says the determinant is a unit
  in A itself; exterior powers are isomorphisms of zero-differential complexes.
- A=Z, a=b=(2,0), t=diag(1,3): the determinant 3 is a unit modulo (2) but not
  in Z. Compatibility holds, and homology maps are multiplication by 1 or 3 on
  Z/2. Thus the statement correctly asks for quasi-isomorphy and does not assert
  degreewise invertibility. Nonregular tuples are allowed.
- q>r has zero terms on both sides, with the component still prescribed.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder`, query "Exterior power maps on Koszul complexes are
  quasi-isomorphisms when the substitution determinant is invertible modulo the
  generated ideal": eight hits, including representation standard resolutions,
  `exteriorPower.presentation.isPresentationCore`, and generic quasi-isomorphisms;
  none states the determinant criterion.
- `msearch.py ... loogle '"Koszul"'`: zero hits.
- `msearch.py ... leansearch`, query "Koszul substitution determinant unit modulo
  common ideal implies quasi-isomorphism": eight generic `QuasiIso` and
  short-complex results, none the requested criterion.
- `msearch.py ... grep '[Kk]oszul' Algebra/Homology`: only the local-cohomology
  documentation mentioning Koszul homology, with no construction or criterion.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for Koszul maps,
  comparisons, substitutions, and unit-mod-ideal names found various distinct
  Koszul applications. Read `KoszulGeneratorChainMap.lean`: its
  `exists_koszul_generator_chain_map` requires augmentations, prescribes only
  the top component, and has no determinant criterion or quasi-isomorphism
  conclusion. It is not this statement. `KoszulRegularSequenceDualComplex.lean`
  treats comparisons for regular sequences, also a different statement.
- `grep -rn` of the item id in `lean/WeilConjectures` found no declaration.
  `rg` of `dag/lean_names_upstream.json` and both Lean trees for
  `koszul_substitution_unit_mod_ideal` found no existing declaration or name clash.

No statement fault or mathematical dispute was found.

Validation: `scompile.py Q135 lem-sfb-koszul-substitution-unit-mod-ideal` compiled
the delivered module successfully in both sandbox and library-module modes,
within the 60-second file limit (46.7 s and 19.6 s). No errors or unexpected
warnings were reported. Source lines are at most 100 characters. The node copy
differs from the base only by its `lean` record; its recorded signature was
extracted verbatim from the delivered file.

## Second reading by Q135

I reopened the node and the final signature for a second clause-by-clause reading.
The dispatcher explicitly forbids starting other agents, so this is a self-review;
the maintainer's independent delivery review remains separate.

I checked the two ideal equalities independently, the direction alpha composed
with t equals beta, the matrix column convention, quotient unit condition,
degree-by-degree exterior-power equation, quasi-isomorphism assertion, and image
of exactly T under extension and Q. All match. In particular I rejected using
regularity or a unit determinant in A: neither appears in the signature. I checked
that no chain map is assumed as extra input; its existence is part of the
conclusion. The ordinary existential is sufficient because the component equation
uniquely determines the map. No mismatch or signature change was found on this
second reading. There is one named postponed theorem, attached to exactly the
assigned DAG node, and no postponed construction or unbound variable.
