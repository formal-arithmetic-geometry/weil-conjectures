## Worker report

The module `Sheaf.RingTheory.EtaleCotangentVanishing` states
`Algebra.CotangentResolution.isZero_cotangentComplex_of_etale`, with `sorry` as its
only proof. No definitions, extra nodes, dependency repairs or statement corrections
are introduced.

Source read: `literature/stacks-project/cotangent.tex`, labels
`lemma-when-zero` (Tag 08R2), case (5) and its reduction to case (1),
`lemma-derived-diagonal` (08R0), and `lemma-bootstrap` (08R1), lines 1575–1648.
The source says étale maps have zero cotangent complex, using flatness of both
the map and its multiplication diagonal and then the bootstrap argument. The
three proof steps of the node are reproduced in the theorem docstring.

Hypotheses and conclusions, checked against the unchanged node:

- “A homomorphism of commutative rings R → C” is encoded by
  `(R C : CommRingCat.{u}) [Algebra R C]`; its ring homomorphism is
  `algebraMap R C`. Bundling imposes no nonzero, domain, local or finiteness
  condition on either ring.
- “Finitely presented as an algebra” is `[FinitePresentation R C]`, precisely
  the declaration recorded by `def-weil-pbc-finitely-presented-algebra`.
- “For every R-algebra D and square-zero ideal J” is the explicitly bound
  `∀ (D : Type u) [CommRing D] [Algebra R D] (J : Ideal D), J ^ 2 = ⊥ → ...`.
  D has the same universe as the rings, so the test class is not vacuous and
  includes C, polynomial extensions and the square-zero extensions needed by
  the infinitesimal criterion. Every collection of rings can be put in a common
  containing universe. Mathlib's `Algebra.FormallyEtale.iff_comp_bijective`,
  read in `Mathlib/RingTheory/Etale/Basic.lean:86`, has exactly this test universe
  `max u v`, which is u here.
- The reduction map is `(Ideal.Quotient.mkₐ R J).comp`, with its full type
  `(C →ₐ[R] D) → C →ₐ[R] D ⧸ J` written explicitly. The hypothesis is
  `Function.Bijective`, so it includes both existence and uniqueness of lifts.
- The “standard cotangent complex” is the dependency's `cotangentComplex κ`
  at `Arrow.mk (CommRingCat.ofHom (algebraMap R C))`. The parameter
  `κ : Coherence.{u}` supplies the standard polynomial construction already
  specified by the dependency; it is not an arbitrary complex assumed to have
  any vanishing property. That dependency's `exists_coherence` supplies these
  data, with prescribed terms, operators and differential generators. The
  derived-category instances for every bundled ring are the same size
  convention used by that interface, with morphisms in universe u+1.
- “Is zero in D(C)” is the first conjunct `IsZero (cotangentComplex κ ...)`,
  where the object lies in `DerivedCategory (ModuleCat.{u} C)`.
- “Equivalently H^i(L)=0 for every integer i” is the second conjunct
  `∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).obj ...)`.
  These are cohomology functors since this is the integer-indexed cochain
  derived category. Both formulations are asserted; no degree is excluded.
  `IsZero` applies to category objects, not to bare types.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `cotangentComplex`,
  `derivedDifferentials`, `differentialComplex` and the prescribed standard
  terms and operators. The full module, structure fields and docstrings were
  read, including `exists_coherence`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the recorded abstract-derived-
  category node also specifies cohomology via
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, with
  its quotient-of-polynomial-algebra docstring and full class signature read.

Proof-plan import:
`Sheaf.Algebra.Homology.FlatSurjectionDerivedSelfTensor` is imported non-publicly
for `lem-trf-flat-epimorphism-derived-self-tensor`. Its declaration and docstring
were read. The three other proof dependencies currently have no recorded Lean
module, so they cannot yet be imported. They remain named in the proof docstring;
no missing proof dependency is needed to type this statement.

Edge cases checked: identity ring maps, the zero target ring (including a zero
source), J=0, square-zero ideals in rings of arbitrary characteristic, and all
negative, zero and positive integer degrees. No `Nontrivial`, characteristic,
Noetherian, nonempty spectrum or finite-rank hypothesis is imposed. In particular
positive-degree cohomology is also included, even though the standard complex has
zero positive terms. Finite presentation is retained even though the source also
proves vanishing under the broader weakly-étale hypothesis.

Searches actually run using the prescribed msearch wrapper (logged in searches.jsonl):

- LeanFinder: `etale ring homomorphism standard cotangent complex is zero in derived category`.
  Eight hits: principally `Algebra.FormallyEtale.subsingleton_h1Cotangent`,
  `Algebra.Etale.formallyEtale`, `Algebra.formallyEtale_iff`, and related results.
  None concerns the full standard derived cotangent complex.
- LeanSearch: `etale algebra cotangent complex vanishes in every degree`.
  Eight hits, again for Kähler differentials, H1 and formal étaleness; no full
  derived-category vanishing statement.
- Loogle: `Algebra.FormallyEtale, Algebra.Etale`.
  Three hits: `Algebra.Etale.formallyEtale`, `Algebra.Etale.mk` and
  `Algebra.etale_iff`. These identify the hypotheses, not the conclusion.
- Mathlib grep: `cotangent|H1Cotangent`, subdirectory `RingTheory/Etale`.
  Thirteen hits, for H1 and differential modules; no full derived vanishing.
- Direct rg searches of `WeilConjectures` for this node id,
  `cotangentComplex|cotangent.*[Vv]anish`, and the proposed declaration name
  gave no full standard-cotangent vanishing declaration. Searches of the
  project's `lean/Sheaf/RingTheory` for
  `cotangentComplex|etale.*cotangent|Etale.*cotangent` found the coherence
  construction and unrelated conormal/first-homology results; no duplicate.
  `dag/lean_names_upstream.json` was also searched for cotangent and read.
  Mathlib, upstream and side sources were searched for the proposed full name;
  it did not exist.

Validation: `scompile.py Q96 lem-trf-etale-cotangent-vanishing` compiled this file
both as a sandbox module and at its final library module name, cleanly, with
1.8 seconds reported for each. The first attempt exposed an instance-elaboration
mismatch with unbundled ring binders; using the dependency's bundled ring
interface repaired it without changing the mathematical statement. Every
variable and universe is explicitly bound (`set_option autoImplicit false`).

No statement dispute or node fault was found. Only the item's `lean` field is
changed in the node copy.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
