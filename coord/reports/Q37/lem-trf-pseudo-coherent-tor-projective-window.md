## Worker report

The module `Sheaf.RingTheory.PseudoCoherentTorProjectiveWindow` states
`DerivedCategory.exists_finiteProjective_model_of_torAmplitudeIn`, with one postponed
proof (`sorry`). It gives a finite projective representative in the specified Tor
interval, over an arbitrary commutative ring. No definitions, helper nodes, dependency
repairs, or changes to the mathematical node statement were needed.

Source checked directly: `literature/stacks-project/more-algebra.tex`,
`lemma-perfect`, Tag 0658, final assertion and proof (lines 18889–18914 in this checkout).
The source chooses the finite free upper-bounded model, then good truncation at the
lower endpoint, whose bottom opcycles are finitely presented and flat.

Hypothesis and conclusion correspondence:

- Arbitrary commutative ring A: `{A : Type u} [CommRing A]`. There is no Noetherian,
  domain, local, nonzero, characteristic, or flatness hypothesis on A.
- Integers a ≤ b: `(a b : ℤ) (hab : a ≤ b)`; both exact endpoints remain in the conclusion.
- Object of D(A): `(C : DerivedCategory (ModuleCat.{u} A))`, with
  `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` recording only the localization size.
  The coefficient/module universe is arbitrary u and the localization morphism
  universe is separately arbitrary w, as in the existing ring Tor-amplitude API.
- Pseudo-coherence: `(hC : IsPseudoCoherent C)`, the recorded dependency definition,
  with a bounded-above finite-free representative; no substitute finiteness property.
- Tor amplitude: `(hTor : torAmplitudeIn (ModuleCat.{u} A) a b C)`. Unfolding the
  existing predicate quantifies over EVERY ordinary A-module N in `ModuleCat.{u} A`,
  tensoring C with `singleFunctor _ 0 |>.obj N`, then requires the derived homology
  to be ≥ a and ≤ b. By `DerivedCategory.isGE_iff` and `isLE_iff` this is exactly
  vanishing in all degrees i < a or b < i. It does not restrict N to flat, finite,
  finitely presented, or projective modules. The derived monoidal structure is the
  existing K-flat construction, not an arbitrary monoidal structure. Its comparison
  `QObjTensorQObjIsoOfKFlatLeft` computes the tensor by total ordinary tensor on a
  K-flat first factor, exactly as stipulated by the node.
- Existence of an ordinary cochain complex: `∃ P : CochainComplex (ModuleCat.{u} A) ℤ`.
- Zero terms outside the prescribed interval:
  `∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)`.
  This is vanishing of the TERMS, not merely their cohomology.
- Every term is a summand of a finite free module:
  `∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)`.
  This standard equivalent form uses the recorded `Module.Projective` dependency.
  Mathlib's `Module.Finite.exists_comp_eq_id_of_projective` (in
  `Mathlib.RingTheory.Finiteness.Projective`) explicitly supplies a retraction of
  `Fin n → A` onto each such term. Conversely a retract of a finite free module is
  finite and projective, so neither a stronger nor weaker term condition is imposed.
- Isomorphism with the given object: `Nonempty (Q.obj P ≅ C)` uses the recorded
  localization functor; it asserts existence of the isomorphism, without choosing data.

Statement dependency declarations read and used:

- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q`.
- `def-pc-ring-pseudo-coherent-complex`:
  `WeilConjectures.RingTheory.RingPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`.
- `def-pc-module-kflat-complex`:
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`,
  `CategoryTheory.MorphismProperty.kFlat`. The canonical Tor-amplitude interface is
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`,
  `DerivedCategory.torAmplitudeIn`. Its module resolutions are provided by
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`,
  `ModuleCat.hasFunctorialFlatResolution`. These are existing constructions.
- `def-weil-pbc-projective-module`: `Mathlib.Algebra.Module.Projective`,
  `Module.Projective`, with its splitting and lifting characterizations.

All stated proof prerequisites are imported privately (the four statement dependency
modules are public). The proof docstring follows all five DAG proof steps, including
independence of the K-flat representative in step 3 and the degree-a+1 boundary check:

- `WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel`,
  `DerivedCategory.exists_finiteFree_model_isStrictlyLE`.
- `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`,
  `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`,
  `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft`.
- `WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion`,
  `Module.Flat.opcycles_of_exactAt`.
- `Mathlib.Algebra.Module.FinitePresentation`, `Module.FinitePresentation`.
- `Mathlib.RingTheory.Flat.EquationalCriterion`,
  `Module.Flat.projective_of_finitePresentation` (the dependency's mathlib_match).

Edge cases checked before writing: a=b gives a single finite projective module in that
degree, rather than an arbitrary bounded interval. C=0 permits the all-zero complex in
every ordered interval. The zero ring is allowed and yields zero modules. Negative and
positive endpoints are both integers. Zero terms are finite projective, equivalently
summands of A^0. No assertion of free terms is made at the lower endpoint; it may only
be a finite projective summand. Over a non-Noetherian ring, the bottom term's finite
presentation follows from the two adjacent finite free terms and needs no ring hypothesis.

Searches for an existing exact statement (2026-10-24, msearch.py, recorded also in
`searches.jsonl`):

- LeanFinder: “A pseudo coherent complex with Tor amplitude in a b has a finite
  projective representative supported in the same interval”. Eight hits, including
  `CochainComplex.isKProjective_of_projective`, `CochainComplex.IsKProjective`, and
  projective-resolution/Tor facts. None constructs finite projective terms in the
  specified interval from pseudo-coherence and amplitude.
- Loogle: `"Module.Projective", "CochainComplex"`. Zero hits.
- Mathlib grep: `PseudoCoherent|torAmplitude|finiteProjective`, under Algebra/Homology.
  Zero hits.
- LeanSearch: “A pseudo coherent derived object of Tor amplitude a b has a finite
  projective model concentrated in exactly a through b”. Eight hits, including
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` and ordinary Tor facts. The former
  has no finite/projective term condition; none is this statement.
- Read-only rg searches of `lean/WeilConjectures` and `lean/Sheaf` for Tor amplitude,
  pseudo-coherence, finite-projective windows, and the blueprint id. No exact match.
  In particular the existing
  `DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude` was opened in
  `WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect`:
  it only promises SOME bounded interval, not the specified [a,b], and therefore cannot
  replace this statement. The generic flat-model theorem supplies flat terms only.
  The blueprint-id search of `lean/WeilConjectures` had no hit.

Validation: prescribed scompile.py compiled both the sandbox and named library module
successfully (3.5 seconds each), with no errors or unexpected warnings. All binders and
universes are explicit. No statement dispute or node fault was found.

## Second reading by Q37

A separate second pass by the same worker was used because this dispatch explicitly
forbids starting other agents; the maintainer performs the independent review. I reopened
the node and module and checked the complete correspondence above. In particular I
checked the exact a,b in both hypotheses and conclusion, termwise zero rather than
cohomology zero, finite AND projective rather than merely projective, all testing modules
rather than flat ones, and Q(P) ≅ the original C rather than an unrelated representative.
I reread `IsPseudoCoherent`, `torAmplitudeIn`, `homologyConcentratedIn`, and
`Module.Projective` at their recorded sources and checked the finite-retraction theorem.
The five-step proof docstring retains the K-flat model comparison and bottom-truncation
cohomology calculation from the DAG. No mathematical mismatch was found and no correction
was needed. The original statement, dependencies, and proof fields are unchanged.
