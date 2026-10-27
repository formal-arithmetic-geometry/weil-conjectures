## Worker report

The module Sheaf.RingTheory.FlatFpQuotientPseudoCoherent states
DerivedCategory.isPseudoCoherent_restrictScalars_iff_of_flat_finitePresentation_quotient,
with proof `sorry`. It is exactly the equivalence (1) with (4) of Stacks Tag 0E1T,
lemma-more-relative-pseudo-coherent-is-moot, read in more-algebra.tex. There is no
new definition, dependency repair, or statement correction.

Hypothesis and clause correspondence:

- The commutative rings R, B, A are the three explicit type binders and their
  `CommRing` instances. Their universes uR, uB, uA are independent.
- The composable homomorphisms are `f : R →+* B` and `q : B →+* A`.
  Thus the node's R → A is literally `q.comp f`; no extra compatibility
  or algebra structure is assumed.
- Surjectivity of q is `hq : Function.Surjective q`.
- Flatness of R → B is `hf_flat : f.Flat`, and flatness of R → A is
  `hqf_flat : (q.comp f).Flat`.
- Finite presentation of those same maps is `hf_fp : f.FinitePresentation`
  and `hqf_fp : (q.comp f).FinitePresentation`. These are Mathlib's
  RingHom wrappers for Algebra.FinitePresentation with the induced algebra
  structure, exactly as allowed by the dependency record.
- Ordinary module derived categories are `DerivedCategory (ModuleCat ... A)`
  and `DerivedCategory (ModuleCat ... B)` with separately bound
  `HasDerivedCategory.{wA}` and `HasDerivedCategory.{wB}`. Module carriers
  use a common universe `max uR uB uA v`, allowing arbitrary enlargement
  and including the ring carriers; no equality of ring or localization
  universes is imposed.
- Every M in D(A) is the unrestricted explicit binder
  `M : DerivedCategory (ModuleCat.{max uR uB uA v} A)`.
- Pseudo-coherence over A is `IsPseudoCoherent M`.
- Its restriction over B is
  `(ModuleCat.restrictScalars q).mapDerivedCategory.obj M`.
  `ModuleCat.restrictScalars` keeps the additive group and uses b • m = q(b) • m.
  The exact functor's `mapDerivedCategory` is induced by termwise application
  to cochain complexes, as specified by `mapDerivedCategoryFactors`.
- Pseudo-coherence of that B-object is the right-hand `IsPseudoCoherent`;
  `↔` states both implications, with no boundedness or finiteness imposed on M.
- No Noetherian, flatness of q, or finite-presentation assumption on q is added.

Dependency declarations read and used:

- def-weil-pbc-flat-ring-map: Mathlib.RingTheory.RingHom.Flat,
  RingHom.Flat; its definition is Module.Flat for f.toAlgebra.
- def-weil-pbc-finitely-presented-algebra: Mathlib.RingTheory.FinitePresentation,
  Algebra.FinitePresentation, via RingHom.FinitePresentation (same file).
  The latter definition is precisely the former for f.toAlgebra.
- def-weil-abstract-derived-category:
  Mathlib.Algebra.Homology.DerivedCategory.Basic, DerivedCategory and
  HasDerivedCategory. The canonical localization Q is used by the existing
  pseudo-coherence definition and exact-functor API.
- def-pc-ring-pseudo-coherent-complex:
  WeilConjectures.RingTheory.RingPseudoCoherent,
  DerivedCategory.IsPseudoCoherent. Its full definition asks for a bounded-above
  complex whose terms are finite free, with Nonempty (Q.obj E ≅ M).
- The stated proof dependency def-weil-pbc-mv-polynomial-ring is imported from
  Mathlib.Algebra.MvPolynomial.Basic. The finite-presentation proof dependency
  is already a public statement import.
- The two proof-only nodes lem-sfb-flat-fp-polynomial-pseudocoherent and
  lem-sfb-pseudocoherent-algebra-scalar-restriction have no recorded Lean
  declaration in the read snapshot, so there is no module to import for them.
  They are not needed to type this theorem. Its proof docstring reproduces the
  node's three steps, identifying exactly where each future input applies.
- The restriction interface uses Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
  and Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor. The general-universe
  exactness instances avoid an artificial equality of universes.

Edge cases checked mathematically before writing:

- q an identity: the restriction is the identity on representatives, and the
  equivalence reduces to pseudo-coherence of the same derived object.
- A the zero ring: allowed, since no Nontrivial instance is assumed; every
  A-module is zero and both derived objects have the zero finite-free model.
- B the zero ring: surjectivity forces A zero, also covered.
- M zero, or arbitrary shifts of M: no nonzero or degree bound is imposed.
- For a nonregular quotient, take R = k, B = k[t], A = k[t]/(t²).
  Both algebras are flat finitely presented over k, although q is not flat;
  the statement includes this case and the common polynomial argument applies.
- Non-Noetherian bases are retained, for example a polynomial ring in infinitely
  many variables, with B = R[t] and A = R. The common polynomial proof never
  invokes Noetherianity.
- The proof's number of variables may be zero. No positive-variable assumption
  occurs in the statement or its proof description.

Searches (2026-10-24):

- msearch.py LeanFinder: "A surjection between flat finitely presented algebras
  preserves and reflects pseudo coherent objects under restriction of scalars".
  Eight hits, concerning faithfully flat descent, flatness and algebra finite
  presentation; none states this derived pseudo-coherence equivalence.
- msearch.py LeanSearch: "Pseudo coherent derived complex restrict scalars along
  quotient flat finitely presented algebras". Eight hits, on module restriction
  pseudofunctors, presentations and ordinary flatness, with no match.
- msearch.py Loogle: `"PseudoCoherent"`, zero hits.
- msearch.py grep of Mathlib: `PseudoCoherent|pseudoCoherent|pseudo_coherent`,
  zero hits.
- rg of WeilConjectures and Sheaf for IsPseudoCoherent and scalar restriction,
  followed by reading RingPseudoCoherent and the nearby
  PolynomialPresentationPseudoCoherence module: the former is the required
  definition, the latter is invariance between two polynomial presentations
  (Tag 065H), not the quotient theorem. FiniteFreeAlgebraPseudoCoherentResolution
  is a different finite-free algebra resolution input. No identical statement.
- grep for the item id in WeilConjectures: no hits. rg for the chosen declaration
  in WeilConjectures, Sheaf and dag/lean_names_upstream.json: no hits.

The example Sheaf.CategoryTheory.CompactObject is withdrawn; its node now records
WeilConjectures.CategoryTheory.CompactObject, which was read for the example's
actual definition and documentation conventions. All four statement dependencies'
recorded declarations and docstrings were read in the source files.

No STATEMENT-DISPUTED issue was found. The source proof has a direction typo
"A → B is surjective"; the statement and this delivery consistently use B → A.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
