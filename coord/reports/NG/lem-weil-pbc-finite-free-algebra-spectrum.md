## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum` states
`AlgebraicGeometry.specMap_isFiniteLocallyFree_of_basis`, with `sorry` as the entire proof.
No definitions, dependency modules, or statement corrections were needed.

Hypothesis and conclusion correspondence:
- A commutative ring A: `(A : Type u) [CommRing A]`.
- A commutative A-algebra S: `(S : Type u) [CommRing S] [Algebra A S]`.
- An A-module basis indexed by a finite set: `{I : Type v} [Finite I]
  (_b : Module.Basis I A S)`. The supplied basis is exactly the witness of freeness in
  `Module.Free.exists_basis`; the explicit witness adds no assumption beyond the node.
- The structural morphism Spec S → Spec A:
  `Spec.map (CommRingCat.ofHom (algebraMap A S))`.
- Finite, flat, and locally of finite presentation: the conclusion is
  `.IsFiniteLocallyFree`, the upstream class extending precisely `IsFinite`, `Flat`, and
  `LocallyOfFinitePresentation` on that same morphism.
- No Noetherian or nonzero hypothesis: neither is a binder or instance requirement.

The rings share the scheme universe `u`; any pair of ring types can be placed in a common
universe by cumulativity. The basis index has its own universe `v`; there is no restriction
on its size beyond finiteness. Every variable and universe is explicitly bound.

Statement dependencies inspected and used:
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` (basis existence), using its
  `Module.Basis` witness explicitly.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (full class and docstring inspected).

Proof dependencies are imported without `public`: `Mathlib.RingTheory.Finiteness.Defs`
(`Module.Finite`), `Mathlib.AlgebraicGeometry.Morphisms.Finite`
(`AlgebraicGeometry.IsFinite.SpecMap_iff`), `Mathlib.RingTheory.Flat.Basic`
(`Module.Flat.of_projective`, `Module.Flat.of_free`),
`Mathlib.AlgebraicGeometry.Morphisms.Flat` (`AlgebraicGeometry.Flat.SpecMap_iff`),
`Mathlib.RingTheory.FinitePresentation` (`Algebra.FinitePresentation`), and
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
(`AlgebraicGeometry.LocallyOfFinitePresentation`).
The five-step node proof is reproduced in the theorem docstring, including the finite
multiplication-table presentation and inverse maps. Source checked directly in
`literature/stacks-project/morphisms.tex`, lemma-finite-flat (Tag 02KB), and
`literature/stacks-project/algebra.tex`, lemma-finite-finite-type (Tag 0D46).

Edge cases checked mathematically: an empty basis forces S to be the zero ring, whose
spectrum is empty; the defining unit relation is 1 = 0, and all three morphism properties
hold. If A is zero then any unital A-algebra is zero, with no nontriviality required. A
one-element basis and arbitrary non-Noetherian A are included. Nothing requires positive
rank, surjectivity of spectra, or reducedness; finite free nonreduced algebras are included.

Searches for reuse:
- msearch LeanFinder: “The spectrum of a finite free commutative algebra is finite flat and
  locally of finite presentation”: eight hits, including `Algebra.Smooth.exists_finiteType`,
  `Algebra.QuasiFinite.finite_primeSpectrum`, and smooth descent results; none states this
  conclusion under precisely the finite-basis hypothesis.
- msearch Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Flat`: eight hits, all
  flat-rank results such as `Scheme.Hom.isLocallyConstant_finrank`; none is this statement.
- msearch grep: `finiteLocallyFree|finite_free|IsFiniteLocallyFree` in AlgebraicGeometry:
  zero hits.
- msearch LeanSearch: “A finite free algebra gives a finite locally free morphism of affine
  schemes”: service unavailable (Internal Server Error), zero hits.
- rg in upstream WeilConjectures and project lean/Sheaf for spectrum/finite-free name
  combinations: no matching theorem (one unrelated finite-free complex model call).
  Inspecting upstream FiberDegree finds the required class but no theorem of this form.
- grep for the exact blueprint id in upstream WeilConjectures: no hits.
- rg for the proposed declaration name in Mathlib, WeilConjectures, project lean/Sheaf,
  and dag/lean_names_upstream.json: no collision.

Validation: the module compiles cleanly through scompile.py on the server, nice 19,
two threads, 60 seconds per file (reported compile time 1.4 s). No warnings or errors.
There is no STATEMENT-DISPUTED issue or node fault.

## Second reading by NG

I independently read the item node, its five proof steps, the proposed module, the three
statement dependency nodes and their actual declarations, and the recorded proof dependencies.
I read morphisms.tex, lemma-finite-flat (Tag 02KB), including the preceding definition and
its full proof, and algebra.tex, lemma-finite-finite-type (Tag 0D46), including its explicit
presentation. The source has arbitrary commutative rings here: local Noetherianity is needed
only for the separate equivalence with finite flatness alone, not for this assertion.

The node's objects, hypotheses and conclusion, matched individually:

- The commutative base ring A is `(A : Type u) [CommRing A]`: exact.
- The commutative A-algebra S is `(S : Type u) [CommRing S] [Algebra A S]`: exact;
  the module structure is the one supplied by this same algebra structure.
- A basis indexed by a finite set is `{I : Type v} [Finite I]
  (_b : Module.Basis I A S)`: exact. I opened `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic` and `Module.Basis` in
  `Mathlib.LinearAlgebra.Basis.Defs`. The latter has `repr : S ≃ₗ[A] (I →₀ A)`,
  precisely uniqueness and existence of finite coordinates. Taking the basis as an argument
  renders the hypothesis that such a basis exists: the conclusion does not depend on the
  choice. No separate free or finite-module assumption is imposed.
- The structural morphism is `Spec.map (CommRingCat.ofHom (algebraMap A S))`: exact.
  I opened `Spec` and `Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`; this is the
  contravariantly induced map from Spec S to Spec A for the specified algebra map.
- Finiteness is the `IsFinite` superclass of the conclusion `.IsFiniteLocallyFree`: exact.
- Flatness is its `Flat` superclass: exact, on the same structural morphism.
- Local finite presentation is its `LocallyOfFinitePresentation` superclass: exact.
  I opened `Scheme.Hom.IsFiniteLocallyFree` in upstream Morphisms/FiberDegree.lean:
  it extends precisely these three classes and imposes no further condition. I also read
  the affine criteria in Mathlib Morphisms/Finite.lean and Morphisms/Flat.lean and the
  affine-open definition in Morphisms/FinitePresentation.lean. These agree with the
  dependency nodes, including the pointwise formulation of local finite presentation.
- The exclusion of Noetherian and nonzero-ring hypotheses is respected: neither appears.
  No positive rank, reducedness, field, characteristic, or spectral surjectivity is assumed.

Edge cases: `[Finite I]` permits I empty (n = 0). A basis then forces S to be the zero
ring; its empty spectrum has a finite, flat, locally finitely presented map to Spec A.
The unit relation in the proof plan is 1 = 0, so the presentation still works. If A is the
zero ring then S is zero as a unital algebra, and the assertion still includes every finite
basis index (without asserting uniqueness of rank over the zero ring). Rank one and
nonreduced finite free algebras, such as dual numbers, are included. No characteristic is
restricted. Universes u and v are explicitly declared, all variables are bound, and v is
independent for the finite index. The shared ring universe is the usual universe of the
scheme category; both ring types can be regarded in a common larger universe, so it
excludes no pair of rings. There is no potentially vacuous quantification over test objects.

Independent reuse searches, using different wording from the worker:

- msearch LeanFinder: "A finite basis for an algebra induces a finite locally free map on
  prime spectra": eight hits about finite type, localizations and quasi-finiteness;
  no matching theorem.
- msearch Loogle: `Module.Basis, AlgebraicGeometry.Spec.map`: zero hits.
- msearch grep: `IsFiniteLocallyFree.*Spec|Spec.*IsFiniteLocallyFree|
  specMap_isFiniteLocallyFree`: zero hits.
- msearch LeanSearch: "The affine spectrum of a commutative algebra with a finite module
  basis is finite locally free": unavailable (Internal Server Error), recorded as such.
- Direct rg in Mathlib AlgebraicGeometry, upstream WeilConjectures, and project lean/Sheaf
  for `IsFiniteLocallyFree`, `isFiniteLocallyFree`, `finiteLocallyFree`, and spectrum/basis
  or finite-free combinations found the existing morphism class, many module-sheaf
  results, and descent/degree statements, but no existing theorem for this item's map.
  In particular I inspected upstream FiberDegree and the project's
  FiniteFlatRestrictionProjective: the latter is restriction of scalars for projective
  modules, not the spectrum statement. No collision for the proposed theorem name was
  found in dag/lean_names_upstream.json or these Lean trees.

No mismatch was found, and no Lean or node changes were needed. There are no new definition
nodes, dependency modules, or statement corrections to review. The five numbered docstring
steps reproduce the node's finite-span argument, free-flat argument, multiplication-table
presentation, explicit inverse, and affine local-presentation argument, including the empty
basis. Source and blueprint markers, imports, namespace, line lengths, and the sole
sorry-only theorem satisfy the conventions. No definitions or additional proofs are present.
The node's lean.statement is verbatim the theorem signature before `:=`.

Independent server validation with scompile.py: clean, 1.4 seconds, nice 19, two threads,
60-second limit; no warnings or errors. The statement is ready unchanged.
