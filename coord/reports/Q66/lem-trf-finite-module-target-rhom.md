## Worker report

This stage-2 delivery states `DerivedCategory.finite_module_target_rhom` in
`Sheaf.Algebra.Homology.FiniteModuleTargetRHom`. The sole theorem has proof `sorry`.
No definitions, new nodes, dependency repairs or statement corrections are needed.
The retained Q72 report and `reviewed` record concern stage 1: Q72 explicitly wrote
no Lean. The base item has no `lean` or `reviewed_lean` record. Its stage-1 review
therefore does not finish this stage-2 assignment.

Hypothesis and conclusion correspondence:

- A commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- K in the ordinary module derived category: `(K : DerivedCategory (ModuleCat.{u} A))`.
  The published Grothendieck-abelian instance supplies its chosen derived category;
  no additional mathematical assumption is imposed.
- The integer upper bound u of the prose is called `(b : ℤ)` to distinguish it
  from the Lean universe. All integer values, including negative ones, are allowed.
- The finite A-module N: `(N : ModuleCat.{u} A) [Module.Finite A N]`.
- Every cohomology module of K is finite: `hK : ∀ j : ℤ, Module.Finite A
  ((homologyFunctor (ModuleCat.{u} A) j).obj K)`.
- Vanishing above the upper bound: `hKb : ∀ j : ℤ, b < j → IsZero
  ((homologyFunctor (ModuleCat.{u} A) j).obj K)`.
- N[0] is `(singleFunctor (ModuleCat.{u} A) 0).obj N`, the canonical
  degree-zero embedding into the derived category.
- RHom is `(ordinaryModuleDerivedInternalHom A).obj (op K, ...)`, using the
  dependency's recorded ordinary-module interface. This is the existing closed
  derived Hom computed using K-injectives, the ordinary-module presentation of
  the one-object identity-covering site. It is not an arbitrary bifunctor or a
  new definition of RHom.
- Finite cohomology in every degree is the first conjunct `∀ t : ℤ,
  Module.Finite A ((homologyFunctor ... t).obj (...))`.
- Zero cohomology for t below minus the upper bound is the second conjunct
  `∀ t : ℤ, t < -b → IsZero ((homologyFunctor ... t).obj (...))`.
  IsZero is categorical zero for the bundled module, hence precisely a zero module.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor` (available through the
  public dependency imports).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, with its canonical localization comparison.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, exactly the current recorded
  declaration of def-pur-derived-internal-hom. Its public imports preserve the
  generic ringed-site version and its comparisons.

The stated proof dependencies are plain imports:
`Sheaf.Algebra.Homology.SourceHyperExtModuleTarget` with
`DerivedCategory.exists_source_hyperExt_module_target`, and
`Mathlib.Algebra.Category.ModuleCat.Ext.Finite` with `ModuleCat.finite_ext`.
The generic quadrant abutment node has no Lean statement on this base and thus no
module to import. It is a proof-only prerequisite; the theorem docstring retains
its full role and the filtration reindexing. No missing notion is needed to type
the statement. The docstring follows all three proof steps of the item.

Edge cases checked before writing: K=0, N=0, and the zero ring give zero output.
For a field k, K=k[-b] and N=k give nonzero H^{-b}, so the strict bound is sharp,
including negative b. Upper-bounded sources unbounded below are included because
hK is cohomological and hKb supplies only an upper bound. Singular Noetherian rings
may have nonzero Ext in arbitrarily high degree; no upper vanishing conclusion is
asserted. The coefficient and module universe is arbitrary, with the published
ordinary-module interface's standard small Hom convention. No independent test
universe, finite-dimensionality, injectivity, finite projective dimension, bounded
representative or regularity hypothesis is added.

Searches performed through msearch.py:

- leanfinder: "Derived Hom of a bounded above complex with finite cohomology into
  a finite module over a Noetherian ring has finite cohomology and vanishes below
  the negative upper bound". Eight results concerned derived t-structure bounds,
  bounded complexes and projective/injective single complexes; none gives the
  finite generation assertion.
- leansearch: "Derived Hom from a bounded above complex with finite cohomology
  into a finite module has finite cohomology over a Noetherian ring". Eight hits
  concerned right derived functors, chosen derived categories, Hom complexes,
  small Ext, and vanishing between strict truncation ranges; none states this item.
- loogle: "Module.Finite, CategoryTheory.Abelian.Ext". The relevant result is
  `ModuleCat.finite_ext`, for two modules and natural Ext degree, already the
  item's proof dependency lem-sc-ext-noetherian-finite. Other hits were Rees and
  projective-dimension criteria, not this complex-source statement.
- grep (Algebra): `finite_ext|[Ff]inite.*[Dd]erived.*[Hh]om|[Dd]erived.*[Hh]om.*[Ff]inite`.
  Only `Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean:27` was returned.
- rg of lean/WeilConjectures and lean/Sheaf for the exact node id, proposed
  declaration and module name found no pre-existing declaration for this item.
  Concept searches for finite homology and RHom found, among other related
  statements, BoundedAboveCoherentRHom: its source was read. It treats two
  complexes on the ring site and is the parent theorem, not this exact statement.
  SourceHyperExtModuleTarget supplies a spectral sequence rather than its finite
  generation conclusion. OrdinaryModuleDerivedInternalHom supplies the needed
  canonical bifunctor. These are used, not duplicated.

Source read: literature/stacks-project/perfect.tex, lemma-coherent-internal-hom,
Tag 0D0C, including its algebra problem, second Ext spectral sequence and appeal
to finiteness of Ext of finite modules. This statement is its finite-module-target
intermediate case and leaves the source route unchanged.

Validation: scompile.py compiled the delivered module on the server cleanly,
both the sandbox check and library check, under the fixed 60-second per-file limit.
No Lean statements were proved. There is no STATEMENT-DISPUTED flag.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
