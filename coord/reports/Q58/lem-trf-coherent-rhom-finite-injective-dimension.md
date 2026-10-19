## Worker report

The module `Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension` states
`DerivedCategory.coherent_rhom_finite_injective_dimension`, with `sorry` only.
It follows Stacks dualizing.tex, Tag 0G4H, lemma-finite-ext-into-bounded-injective,
and more-algebra.tex, Tag 0A5S, definition-injective-dimension. Both source passages
were opened, including the full proof of 0G4H. The six proof steps in the current
Q80 split are reproduced in the theorem docstring. No statement correction is needed.

Hypothesis and conclusion correspondence:

- A commutative Noetherian ring is `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- `K,L in D(A)` is `(K L : DerivedCategory (RingSiteModules A))` with an explicit
  `[HasDerivedCategory.{w} (RingSiteModules A)]`. The existing `RingSiteModules A`
  is sheaves of A-modules on `Discrete PUnit` with the bottom topology. Such a
  sheaf is an ordinary A-module, with only identity restriction; evaluation at
  `op ⟨PUnit.unit⟩` reads that module. This is the same presentation used by the
  already landed complete-local-coherent-duality consumer. It introduces no
  additional ring, finiteness, or geometric hypothesis. `u` and `w` are independent.
- Every cohomology module of K is finite: `hK : ∀ i : ℤ, Module.Finite A
  (((homologyFunctor (RingSiteModules A) i).obj K).val.obj (op ⟨PUnit.unit⟩))`.
  `hL` states exactly the corresponding condition for L. There is no support
  condition on K, and neither of these binders restricts the integer i.
- L is isomorphic to a bounded complex of injective A-modules: `hI` supplies
  `I : CochainComplex (RingSiteModules A) ℤ`, integers `a b`, vanishing terms
  `q < a ∨ b < q → IsZero (I.X q)`, degreewise `Injective (I.X q)`, and
  `Nonempty (DerivedCategory.Q.obj I ≅ L)`. This is a derived isomorphism, not
  a demand for an actual isomorphism between arbitrary complex representatives.
- The conclusion is `∀ i : ℤ, Module.Finite A ...` on the evaluation of the
  cohomology of `(derivedInternalHomOfUniverses.{u,u,u,w} ⊥
  (CochainComplex.onePointRingSheaf A)).obj (op K,L)`. Thus it is the full recorded
  derived internal Hom, contravariant in K and covariant in L, with its ordinary
  A-module structure. No arbitrary replacement functor or comparison is assumed.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; cohomology is
  `DerivedCategory.homologyFunctor` in `DerivedCategory.HomologySequence`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
  The dependency's other recorded clause `InjectiveResolution` was also read; an
  object resolution concentrated at degree zero is not imposed on this complex L.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, including its full signature,
  localization construction and arbitrary K-injective representative comparison.
- `Sheaf.Algebra.Homology.RingHomExtensionDefs`: `CategoryTheory.RingSiteModules`;
  the constant `CochainComplex.onePointRingSheaf` is re-exported by this module.
  Its existing owning node `def-pc-ring-hom-extension-shared-definitions` is added
  to stmt_deps to record this presentation, without adding any definition.

Proof-only imports cover the stated total module Hom complex, bounded-below
injective K-injectivity, good truncations and the long exact cohomology sequence.
`lem-trf-bounded-above-coherent-rhom` currently has no Lean record: it is mentioned
as the final proof input in the docstring; no declaration or import is invented.
It is unnecessary for typing this statement. There are no new nodes or dependency
modules.

Edge cases checked: zero ring is allowed (no Nontrivial instance); K=0 and L=0
are allowed; the zero injective complex gives a valid witness. Empty support
intervals are permitted and mean the zero complex, consistent with the source.
All degrees are integers, including negative degrees and shifts. The field case
allows a complex K with nonzero finite cohomology in every degree, so unbounded
input remains present. L is not required to have finite injective *terms*: only
its cohomology is finite. Injectivity is in the module category, hence exactly
the extension property in the source. No local, complete, regular or bounded-K
hypothesis has been introduced.

Existing-declaration searches (all results read):

- `msearch.py`: {"t": "2026-10-19T00:21:33Z", "tool": "leanfinder", "query": "Derived Hom from an unbounded complex with finite cohomology into a bounded injective complex has finite cohomology over a Noetherian ring", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective", "CochainComplex.IsKInjective", "CochainComplex.isKInjective_of_injective_aux", "CochainComplex.HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKInjective", "CochainComplex.isKInjective_of_injective", "CochainComplex.cm5b.instIsStrictlyGEI", "DerivedCategory.instIsLEObjCochainComplexIntQOfIsLE", "DerivedCategory.instIsGEObjCochainComplexIntQOfIsGE"], "digest": "a65e705d45dbce89"}
- `msearch.py`: {"t": "2026-10-19T00:21:48Z", "tool": "loogle", "query": "Module.Finite, DerivedCategory", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
- `msearch.py`: {"t": "2026-10-19T00:22:09Z", "tool": "grep", "query": "Finite.*(rhom|RHom)|[Cc]oherent.*[Ii]njective|[Ii]njective.*[Cc]oherent", "sub": "", "ok": true, "n_hits": 21, "note": "", "top": ["Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean", "Mathlib/Order/NonemptyFiniteChains.lean", "Mathlib/CategoryTheory/Limits/Preserves/Lattice.lean", "Mathlib/CategoryTheory/Limits/Preserves/Lattice.lean", "Mathlib/LinearAlgebra/Contraction.lean", "Mathlib/LinearAlgebra/Contraction.lean", "Mathlib/LinearAlgebra/Contraction.lean", "Mathlib/LinearAlgebra/Contraction.lean"], "digest": "5df5c07f94f446ed"}
- `msearch.py`: {"t": "2026-10-19T00:25:40Z", "tool": "leansearch", "query": "Noetherian ring coherent unbounded derived Hom finite injective dimension preserves finite cohomology", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CategoryTheory.injectiveDimension_ne_top_iff", "CategoryTheory.injectiveDimension", "Module.finitePresentation_of_finite", "CategoryTheory.injectiveDimension_le_iff", "Module.IsNoetherian.finite", "isNoetherian_of_injective", "isNoetherian_of_isNoetherianRing_of_finite", "CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc"], "digest": "78cf3fe036b2d8af"}

Direct rg searches of `/WeilConjectures` and `lean/Sheaf` for the node id and
coherent/finite/injective combinations find the existing consumer's proof mention,
not this theorem. Additional searches for derived-Hom definitions found the
recorded generic ringed-site functor and shared ring-site presentation, which are
used instead of copying them. Loogle reports zero matches; LeanFinder gives
K-injectivity and localized shifted-Hom comparison lemmas, and LeanSearch gives
injective dimension of individual objects and ordinary module finiteness. The
Mathlib grep results concern unrelated finite Hom constructions and coherent
spaces. None states preservation of finite cohomology for unbounded coherent
complexes into bounded injectives.

Validation: `scompile.py Q58 lem-trf-coherent-rhom-finite-injective-dimension`
compiled the sandbox file (6.9 seconds) and its intended library module
(3.8 seconds), with no errors or warnings. All variables and universes are
explicit. Only the theorem proof is `sorry`; no data definition is introduced.

The previous worker's stale-assignment notice concerns Q80's merged stage-1
split. This delivery preserves that split and its proof, and supplies only its
stage-2 statement. The current shared node had no Lean record.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
