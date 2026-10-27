## Worker report

The delivery states `AlgebraicGeometry.arbitraryRing_relativeDualizing_isomorphic`
in `Sheaf.RingTheory.ArbitraryRingRelativeDualizingIsomorphism` with one `sorry`.
There are no new definitions, additional nodes, dependency repairs, or statement changes.
The node copy changes only `lean`; its recorded signature is copied verbatim from the file.

Source read: `literature/stacks-project/dualizing.tex`,
`definition-relative-dualizing-complex` (0E2C) and
`lemma-uniqueness-relative-dualizing` (0E2D), including the surrounding paragraph
explicitly treating the non-Noetherian case. Definition 0E2C requires R-perfectness
and the unmarked diagonal Hom isomorphism. Lemma 0E2D concludes isomorphism of any
two such complexes. The declaration's proof docstring follows all four steps of
this node's accepted polynomial-duality proof rather than silently reusing the
source's problematic evaluation argument.

Hypothesis and conclusion correspondence:

- Arbitrary commutative rings R and A: `(R A : Type u) [CommRing R] [CommRing A]`.
  The map R to A is `[Algebra R A]`, with map `algebraMap R A`. This encodes every
  commutative ring homomorphism by its induced algebra structure.
- Flatness: `hflat : RingHom.Flat (algebraMap R A)`.
- Finite presentation: `[Algebra.FinitePresentation R A]`.
- B is the actual tensor square: `A ⊗[R] A` throughout the diagonal Hom hypotheses.
- The actual first coprojection p1 is
  `(Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom`.
- D(A), D(R), and D(B) are `DerivedCategory (ModuleCat.{u} ...)`, using the
  library's existing Grothendieck chosen localization, consistently with
  `ordinaryModuleDerivedInternalHom`. Existence of this localization is an
  inferred constructed instance, not an extra mathematical hypothesis.
- M,N in D(A): `(M N : DerivedCategory (ModuleCat.{u} A))`.
- Pseudo-coherence over A is separately `hM : DerivedCategory.IsPseudoCoherent M`
  and `hN : DerivedCategory.IsPseudoCoherent N`, using the recorded bounded-above
  finite-free representative definition, with no Noetherian restriction.
- Finite Tor amplitude over R is separately `hMTor` and `hNTor`: each asserts
  `∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ), ...`.
  The premise `i < a ∨ b < i` says exactly that i lies outside the closed interval.
  `ModuleCat.restrictScalars (algebraMap R A)` followed by `.mapDerivedCategory`
  gives the underlying R-derived object. The derived monoidal tensor with
  `DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj Q)` is
  T tensor_R^L Q[0]. `IsZero` of the value of
  `DerivedCategory.homologyFunctor (ModuleCat.{u} R) i` is exactly H^i vanishing.
  There is a separate existential interval for each complex, with all R-modules
  tested and all integer degrees included; no projectivity, flatness or finiteness
  condition is imposed on Q.
- T1 is `(relativeDualizingDerivedExtension p1).obj T`, using the dependency's
  total left derived ordinary extension of scalars with its K-flat model.
- A as a B-module through multiplication and in degree zero is
  `relativeDualizingModuleDiagonal R A`. Its definition restricts the regular
  A-module along `(Algebra.TensorProduct.lmul' R (S := A)).toRingHom`, then applies
  the single complex functor and derived localization.
- RHom_B(A,T1) is exactly
  `(ordinaryModuleDerivedInternalHom (A ⊗[R] A)).obj (op diagonal, T1)`.
  This is the recorded dependency's ordinary-module presentation of the existing
  derived closed internal Hom, with K-injective construction.
- Each diagonal isomorphism is a `Nonempty (... ≅ relativeDualizingModuleDiagonal R A)`
  hypothesis (`hMHom`, `hNHom`), in D(B). The right-hand A[0] has the multiplication
  B-action, not the regular B-module action.
- The conclusion is `Nonempty (M ≅ N)` in D(A), an actual derived isomorphism.
  No diagonal class, chosen generator, compatibility equation, uniqueness of the
  isomorphism, scalar normalization, Noetherianity, or nonzero-ring assumption
  appears. Thus the node's unmarked conclusion is preserved.

Dependency declarations inspected and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with its definition using the
  induced algebra and `Module.Flat`; the equivalence at an algebra map was read.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, whose
  field is a finite-variable polynomial surjection with finitely generated kernel.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`; the localization and size signatures
  were read. Cohomology uses the same derived category's `homologyFunctor`.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`; the complete definition was read.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`; the full abbreviation and
  docstring were read. Its underlying derived closed structure was also inspected
  in `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`.
- `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`:
  `AlgebraicGeometry.relativeDualizingDerivedExtension` and
  `AlgebraicGeometry.relativeDualizingModuleDiagonal`; their complete signatures,
  bodies and docstrings were read. These definitions have no Noetherian or
  nonzero-ring hypotheses. The same module's convenience FirstPullback/Hom
  declarations were read, but the statement explicitly applies the dependency's
  recorded extension and Hom declarations instead of making another definition.
- Proof-only import `Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel`:
  `CochainComplex.projective_hom_evaluation_model`, whose recorded signature and
  source were inspected. The other three polynomial proof-dependency nodes
  (`lem-sfb-arbitrary-polynomial-dual-properties`,
  `lem-sfb-arbitrary-polynomial-diagonal-hom`, and
  `lem-sfb-relative-perfect-polynomial-dual-detection`) currently have no Lean
  record. They are named step by step in the docstring; there is no module to
  import yet. Their absence is only a future proof prerequisite and does not
  prevent this statement. Finite presentation's proof dependency is already a
  public statement import.

Edge cases checked mathematically before writing:

- A is the zero ring: tensor-square and multiplication module are zero; D(A)
  has only zero objects up to isomorphism. No `Nontrivial` binder excludes this.
- R is the zero ring: the unital algebra A is also zero, reducing to that case.
- R equals A with the identity algebra structure: the diagonal and first extension
  become A and the identity; RHom_A(A,T) identifies T, so the assumption forces
  each supplied object to be isomorphic to A[0], exactly as the conclusion needs.
- Singleton interval a=b, negative endpoints and degrees equal to either endpoint:
  strict inequalities impose vanishing only outside [a,b], as specified.
- Each Tor interval tests zero, arbitrary and nonflat R-modules, including Q=R;
  the latter also gives bounded cohomology, without adding a boundedness binder.
- No polynomial presentation is fixed in the statement and no n>0 restriction
  is introduced; the n=0 presentation is available to the accepted proof route.
- The common universe u is arbitrary and can contain both rings and all test
  modules at the chosen size; there is no independent smaller test universe.
  Choosing a common universe for the ordinary module API is the existing project
  convention, not a restriction to countable, finite or small-cardinality rings.

Searches for an existing statement (all performed for this item):

1. `msearch.py ... leanfinder "Unmarked relative dualizing complexes for a flat
   finitely presented algebra over an arbitrary commutative ring are isomorphic"`:
   8 hits, including `Algebra.Smooth.flat`, `RingHom.Flat.respectsIso`,
   `Module.Flat.projective_of_finitePresentation`, and cotangent/character-module
   flatness results. None states relative-dualizing uniqueness.
2. `msearch.py ... leansearch "Uniqueness up to derived isomorphism of relative
   dualizing complexes over arbitrary flat finitely presented ring algebras"`:
   8 hits, including `Functor.leftDerivedUnique`, `Functor.rightDerivedUnique`,
   `Adjunction.rightAdjointUniq`, quasi-isomorphism localization and ordinary
   module-presentation uniqueness. These concern uniqueness of functors,
   adjoints or presentations, not uniqueness of the two objects in this node.
3. `msearch.py ... loogle '"dualizing"'`: 0 hits.
4. `msearch.py ... grep 'relativeDualizing|semidualizing|dualizing.*[Uu]niq'`:
   0 Mathlib hits.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for relative-dualizing,
   semidualizing and the proposed declaration names; the exact item-id grep in
   `lean/WeilConjectures` returned no matches. The proposed name has no existing
   declaration. The one close uniqueness statement is
   `AlgebraicGeometry.algebraic_relativeDualizing_isomorphic`, in
   `Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism`. Its full signature
   and proof docstring were read: it adds `[IsNoetherianRing R]` and
   `[IsNoetherianRing A]`, so it is a proper specialization, not this statement.
   The arbitrary-base affine-realization theorem concerns realization/comparison
   of supplied pairs and does not assert unmarked algebraic uniqueness.

Validation: the delivered module was compiled by the prescribed `scompile.py`
wrapper, in both sandbox and library-module modes, with no errors or unexpected
warnings. The initial explicit arbitrary `HasDerivedCategory` parameters were
removed after the compiler showed that the recorded ordinary-module Hom fixes
its constructed Grothendieck localization. All ordinary-module objects now use
that same existing model, so no extra comparison or duplicate construction is
required. `autoImplicit` is false; all variables and the universe are bound.
The dry run and delivery results are recorded by the wrapper.

No node fault or STATEMENT-DISPUTED issue was found. Independent review is the
maintainer's review, as required by the dispatcher's direct-delivery brief.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
