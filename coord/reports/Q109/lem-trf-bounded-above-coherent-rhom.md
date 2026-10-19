## Worker report

Item: lem-trf-bounded-above-coherent-rhom. Group Q109, stage 2, 2026-10-19.
The module Sheaf.Algebra.Homology.BoundedAboveCoherentRHom states
DerivedCategory.boundedAbove_coherent_rhom, with its sole proof `sorry`.
No definition or auxiliary theorem is introduced. No statement correction or dispute.

Source read: literature/stacks-project/perfect.tex, lemma-coherent-internal-hom,
Tag 0D0C, especially the algebra problem and its two Ext spectral sequences
(lines 2697--2716). This gives precisely D^-_Coh(A) against D^+_Coh(A).
The node's finer bound follows from the two half-plane support bounds.

Hypothesis and clause correspondence:

- A commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- K,L in the ordinary module derived category: `(K L : DerivedCategory
  (RingSiteModules A))`. This is the existing one-object bottom-topology presentation
  of ordinary modules, also used in the already stated consumer
  DerivedCategory.coherent_rhom_finite_injective_dimension. There is one object,
  only its identity arrow, and only the maximal covering sieve. Evaluation at this
  object and the constant module functor are mutually inverse; hence this encodes
  all A-modules, not a restriction to any class of sheaves. Degreewise evaluation
  preserves kernels and images, so it identifies cohomology and quasi-isomorphisms
  and therefore their derived localizations. We use this presentation directly.
- The choice of localization/morphism size: `[HasDerivedCategory.{w}
  (RingSiteModules A)]`; `w` is independent of `u`. This is the recorded abstract
  derived-category interface, not a bound on K or L or a small-Hom restriction.
- All H^j(K) finite: `hK : ∀ j : ℤ, Module.Finite A
  (((homologyFunctor (RingSiteModules A) j).obj K).val.obj (op ⟨PUnit.unit⟩))`.
- All H^j(L) finite: `hL` is exactly the same formula with L.
- The integers called u,v in the prose are `(a b : ℤ)` in Lean, avoiding a clash
  with the universe u. The upper bound is `hKa : ∀ j : ℤ, a < j → IsZero
  ((homologyFunctor (RingSiteModules A) j).obj K)`; the lower bound is `hLb`
  with `j < b` and L. Universally quantified explicit witnessing bounds express
  the node's conclusion for every choice of bounds satisfying its assumptions.
- RHom is exactly `(derivedInternalHomOfUniverses.{u, u, u, w} ⊥
  (CochainComplex.onePointRingSheaf A)).obj (op K, L)`. It is the dependency's
  actual K-injective/Hom-complex localization, with its contravariant first input.
- Every cohomology module finite: the first conjunct quantifies all `r : ℤ`,
  applies the same homologyFunctor and unique-object evaluation to this RHom,
  and asserts `Module.Finite A`.
- H^r RHom = 0 for r < v-u: the second conjunct is `∀ r : ℤ, r < b - a →
  IsZero ((homologyFunctor (RingSiteModules A) r).obj (... RHom ...))`.
  Zero of this punctual module sheaf is equivalent to zero of its evaluated
  A-module. No vanishing at the endpoint is asserted.

Dependency declarations read and used:

- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing, isNoetherianRing_iff,
  isNoetherianRing_iff_ideal_fg, the recorded noetherian-ring definition.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory and
  HasDerivedCategory; Mathlib.Algebra.Homology.DerivedCategory.HomologySequence:
  DerivedCategory.homologyFunctor and homologyFunctorFactors.
- Mathlib.RingTheory.Finiteness.Defs: Module.Finite, whose data is FG of top.
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses:
  CategoryTheory.derivedInternalHomOfUniverses; read the full signature,
  localization construction, functorial replacement comparison and object comparison.
- Sheaf.Algebra.Homology.RingHomExtensionDefs: CategoryTheory.RingSiteModules;
  Sheaf.Algebra.Homology.KFlatTensorQuasiIso: CochainComplex.onePointRingSheaf.
  The already recorded owning node def-pc-ring-hom-extension-shared-definitions
  is added to stmt_deps so the chosen ordinary-module presentation is explicit.
  It has a usable Lean record and is not a new node or dependency repair.

Proof-only imports are Mathlib.RingTheory.Noetherian.Basic (Submodule.FG.of_le),
Mathlib.Algebra.Category.ModuleCat.Ext.Finite (ModuleCat.finite_ext), and
Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt
(CategoryTheory.exists_boundedAbove_rhom_hyperExt). These are the stated proof
inputs; their signatures and sources were read. The source spectral sequence
lem-trf-source-hyperext-module-target has no declaration/Mathlib match yet, so
there is no module to import for that proof-only input. It is not required to
formulate this theorem. The docstring records all five proof steps of this node,
including both spectral sequences, eventual finite-page stabilization, finite
filtrations, and the empty diagonal for the lower vanishing bound.

Edge cases checked: A may be the zero ring; K or L may be zero; a,b may be any
integers including negative ones and b<a. No a<=b hypothesis is imposed since
the bounds belong to different complexes. With K=A concentrated in degree a and
L=A concentrated in degree b, RHom has its first nonzero degree b-a, confirming
both the subtraction order and the strict inequality. The source can be unbounded
below and the target unbounded above. No boundedness in the opposite directions,
finite projective dimension, regularity, or finite injective dimension is assumed.
Only the declared coefficient/module universe u and independent localization
universe w are used, as in the recorded punctual-site interface.

Searches made (all returned no exact match for this item):

- msearch.py leanfinder: "Derived internal Hom of bounded above and bounded below
  complexes with finitely generated cohomology over a Noetherian ring has finitely
  generated cohomology". Eight hits: t-structure bounds, small Ext, localization
  support, not finite cohomology of RHom of complexes.
- msearch.py loogle: "Module.Finite, CategoryTheory.Abelian.Ext". Five hits,
  including ModuleCat.finite_ext; its full source signature treats two modules
  and a natural Ext degree, not these two one-sided unbounded complexes.
- msearch.py grep: "derivedHom|derivedInternalHom|finite_ext", Mathlib Algebra.
  One hit, Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean.
- msearch.py leansearch: "Derived Hom of coherent bounded above and bounded below
  complexes over a commutative Noetherian ring has finite cohomology".
  Eight hits for right-derived functors, derived categories, Hom cohomology classes,
  t-structure orthogonality and small Ext, none stating the result.
- rg of the upstream WeilConjectures tree and lean/Sheaf for derived/internal Hom,
  module Hom, one-object sites and coherent Hom. Found the existing punctual-site
  definitions, the generic internal Hom, the module-only total Hom, the already
  stated consumer CoherentRHomFiniteInjectiveDimension and adjacent coherent-duality
  modules. Read these interfaces and reused the punctual construction and generic
  internal Hom. The consumer treats finite-injective-dimension targets and arbitrary
  coherent sources, rather than the present independent one-sided bounds.
- grep -rn of the exact item ID in upstream WeilConjectures: no matches.
- rg of both boundedAbove_coherent_rhom and bounded_above_coherent_rhom in Mathlib,
  upstream WeilConjectures and lean/Sheaf: no collisions. Checked the upstream
  declaration index dag/lean_names_upstream.json for the item and chosen name:
  no matches.

Validation: scompile.py Q109 lem-trf-bounded-above-coherent-rhom compiled this
single file in both sandbox and library form: clean, no diagnostics (4.5 s and
3.2 s). Every variable and universe is explicit; autoImplicit is false. The node
copy changes only lean and adds the already recorded definition owner to stmt_deps.
The Lean record stores the multiline declaration signature verbatim.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
