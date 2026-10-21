## Worker report

The module `Sheaf.Paper.StratifiedTorIntervalDevissage` states
`AlgebraicGeometry.ProEtale.torAmplitudeIn_of_constructible_of_uniform_local_model`,
with a single `sorry` as its entire proof. No definition or other theorem is introduced.
The node changes only in `lean`; its mathematical statement, dependencies and proof plan
are unchanged. No node fault or statement dispute was found.

Hypothesis and conclusion correspondence:

- A prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure with its extended
  absolute value is the existing `PadicAlgCl ℓ`. Its finite subextensions are the existing
  `PadicAlgCl.FiniteIntermediateField ℓ`; their field topology is the restricted norm
  topology. Choosing this standard model loses no algebraic-closure isomorphism class.
- A commutative condensed coefficient ring is `(Λ : Profinite.CondensedRing.{u})`
  with `[IsCommMonObj Λ.X]`. The abbreviation is the recorded general ring-object
  encoding, not a requirement that arbitrary condensed rings have topological presentations.
- The explicit `_hΛ` disjunction restricts this ring to precisely the node's list.
  Its first branch is a finite commutative discrete topological ring `A`, killed by
  `ℓ ^ n` for some natural `n`, with a ring-object isomorphism from Λ to
  `Mon.mk (Profinite.continuousMapRingObj A)`. The other branches are, in order,
  `continuousMapRingObj ℤ_[ℓ]`, `padicIntegersRingObj ℓ E`,
  `continuousMapRingObj ℚ_[ℓ]`, `continuousMapRingObj E`, and `padicAlgClRingObj ℓ`.
  In the two `E` branches, `E` ranges over finite intermediate fields. `Nonempty` here
  asserts an isomorphism of the already constructed condensed rings, including their
  multiplication and units; it does not choose or supply missing ring data.
  Finite rings can be represented in `Type 0` without losing any isomorphism class.
  This follows the existing continuous-map and adic constructors' universe convention.
- Integers `c ≤ d` are `(c d : ℤ) (_hcd : c ≤ d)`.
- The premise on **every scheme** is `hlocal : ∀ (S : Scheme.{u}) (N : Mod ...), ...`.
  There are no compactness, separation or constructibility restrictions on `S` or `N`.
  Its antecedent is exactly `HasFiniteConstantLocalModel Λ.X S N`.
- The premise's consequent is `DerivedCategory.torAmplitudeIn _ c d
  ((DerivedCategory.singleFunctor _ 0).obj N)`: the module in degree zero, tested
  against every module sheaf using the relative derived tensor over Λ_S.
- Every qcqs scheme is `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]`.
  The module binder is the same internal-module category over `condensedRingObj Λ.X X`.
- Constructibility is the recorded `hM : IsConstantModelConstructible Λ.X X M`.
  On qcqs X this definition is `IsFiniteConstantStratified`: it uses
  `Scheme.Stratification`, a finite partition by **constructible** locally closed
  subscheme images, and requires finite constant local models on the strata.
  `Scheme.Stratification` contains the finite locally closed data of the recorded
  `Scheme.FiniteLocallyClosedStratification` together with the constructibility condition
  required here. Its immersed domains are arbitrary schemes, including nonreduced ones.
  It does not require any stratum to be globally open.
- The conclusion is the same `DerivedCategory.torAmplitudeIn _ c d` on `M[0]`.
  The endpoints are unchanged, with no dependence on the number of strata.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, the recorded
  declaration of sk-def-sfb-condensed-ring. Its public import retains the continuous
  coefficient constructors. Those constructors use pointwise operations on continuous maps.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing` (recorded for sk-def-sfb-qlbar-condensed), its
  underlying `padicAlgClRingObj`, and `padicIntegersRingObj`. Read their signatures,
  definitions and docstrings. Qbar sections are finite-subextension-valued continuous maps.
  `...Condensed.FiniteSubextension` supplies the existing coercion of a finite intermediate
  field to its normed field carrier.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `finiteConstantLocalModel_iff_exists_cover` and
  `finiteConstantLocalModelOnCover_iff_scalarMatrix` identify the existing
  `HasFiniteConstantLocalModel` with the node's ordinary scalar-extension models and
  scalar-matrix presentations on the same cover.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`, and
  `IsConstantModelConstructible`. These are reused without private copies.
- `Sheaf.Paper.ConstantModelTorAmplitude`:
  `constantModelConstructibleFiniteTor_wellDefined`, including interval isomorphism
  invariance. Its definitions are the imported `DerivedCategory.torAmplitudeIn` and
  `singleFunctor` from the existing derived-category API. Read `torAmplitudeIn` itself
  in `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`: its tensor is the
  derived monoidal tensor, and its test modules are all objects in degree zero.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, read with its topological parent.
  The constructibility predicate already specializes this general notion as described above.

The remaining imports preserve every stated proof dependency:
`Scheme.exists_finite_open_closed_refinement` from
`Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`;
`Scheme.proEtale_torInterval_local_detection` from
`Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection`;
`Scheme.proEtaleSheafInverseImage` and `proEtaleBaseChangeCoverPreserving` from
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`;
`cartesianCoefficients` and its canonical exact inverse-image lift from
`Sheaf.Paper.CartesianCoefficients`;
Mathlib's `Adjunction.leftAdjointCompIso` (the recorded mathlib_match for
`def-sfb-module-upper-star-comp`) from `Mathlib.CategoryTheory.Adjunction.CompositionIso`;
and `Scheme.proetalePrecoverage` from `Mathlib.AlgebraicGeometry.Sites.Proetale`.
The docstring gives all four proof steps: finite scheme-theoretic open/closed refinement,
pullback of scalar matrices, the uniform bound on leaves including empty leaves, and
upward induction using interval detection with no enlargement.

Edge cases checked: empty X and empty strata are permitted (the empty cover supplies a
vacuous local model); zero modules satisfy every interval, so no `0 ∈ [c,d]` assumption
is appropriate; `c = d` is permitted; intervals wholly outside degree zero are retained
as conditional assertions, even when the global hypothesis is impossible for a nonzero
coefficient ring. Single-stratum and disconnected partitions require no new hypothesis.
Nonreduced stratum schemes and partitions with no globally open stratum remain included.
The finite coefficient case includes the zero ring and all ℓ-power torsion exponents.
The ring Z/ℓ² does not falsely imply a uniform bound for F_ℓ: the premise fails there.
No assumption that ℓ be invertible on X, no base field, no Noetherian assumption and no
quasi-coherence condition is present. The free universe `u` is shared consistently by
schemes, profinite sets and coefficient sheaves; module sections use `Ab.{u+1}`.

Searches actually run through msearch.py:

- LeanFinder: "Uniform Tor amplitude for finite constant local models implies the same
  Tor amplitude for constructible module sheaves on qcqs schemes". Eight hits on qcqs
  scheme sections and generic finite presentations of sheaf modules; no matching theorem.
- Loogle: `"Constructible", "torAmplitude"`. Zero hits.
- Mathlib grep: `constructible.*[Tt]or|[Tt]or.*constructible|strati.*[Tt]or`.
  Three unrelated PrimeSpectrum ChevalleyComplexity hits; no matching theorem.
- LeanSearch: "A uniform Tor amplitude bound for finite constant local model sheaves
  extends to constructible sheaves by open closed stratification induction".
  Eight hits on sheaf limits, constant sheaves, and condensed locally constant functors;
  no matching statement.
- Local `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `torAmplitudeIn_of.*[Ss]trati`, `[Ss]trati.*torAmplitudeIn`,
  `constantModel.*[Tt]or`, and related local-model/constructibility names found the reused
  definitions and neighboring cohomology-interval theorem, but no statement of this item.
  The prescribed `grep -rn` of the item id in `WeilConjectures` returned no match.
  Searching admissibility found `IsLocalizingAdmissibleCoefficient`; inspection showed
  it includes the extra all-continuous-map Qbar case, so it is not the exact list here.
  The theorem's hypothesis lists the six existing coefficient constructions directly;
  no new admissibility definition is introduced.

Validation: scompile.py checked the sandbox form and named library module separately,
with exit 0, no warnings or errors (4.2 s and 4.1 s). The first attempt lacked
`open scoped CategoryTheory.Obj`, needed to expose the bundled ring object's instances;
adding the existing scope fixed elaboration without changing any mathematical binder.

## Second reading by Q03

This is the author's separate rereading, not an independent agent review; the dispatch
brief forbids starting other agents and assigns independent review to the maintainer.
I reopened the node and completed module and matched every clause as listed above.
I specifically checked that `hlocal` quantifies over arbitrary schemes, while qcqs
instances occur only on the conclusion's X; that both Tor tests use the same c and d;
that the algebraic-closure branch is `padicAlgClRingObj`, not all continuous maps;
and that the finite-ring branch retains annihilation by an ℓ power. No mismatch found.
The existing constructibility definition uses exactly finite constructible locally closed
immersed strata and imposes neither reduction nor an open-stratum condition. The general
stratification module is imported, without recreating its record. No statement correction,
new node, dependency-record change, hidden axiom, proof beyond `sorry`, local definition,
local notation, or additional conclusion was introduced. Every universe and binder is
explicit. The proof docstring follows the node's four steps and treats empty leaves.
