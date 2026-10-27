## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveBundleAffinePresentations` states
`AlgebraicGeometry.exists_affine_projectiveBundle_presentations`, with its sole proof
`by sorry`. No definition, helper theorem, dependency module or new node is added.
The item node changes only in `lean`.

I read Stacks `morphisms.tex`, the proof of Tag 01WB,
`lemma-characterize-locally-projective` (affine neighbourhood, generators, graded
quotient and closed immersion), and the finitely globally generated paragraph of
Tag 087S, `lemma-projective-over-quasi-projective-is-H-projective`. They give the
specified local ranks and projective-space embeddings without any global bound.

Clause-by-clause rendering:

- Any scheme S: `(S : Scheme.{u})`, with u explicitly declared and `autoImplicit false`.
- A finite-type quasi-coherent module: `(E : S.Modules)` and
  `(hE : E.IsQuasiCoherentFiniteType)`, the dependency's exact conjunction of
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`.
- An affine open covering: existential `I : Type u`, `U : I → S.Opens`, the equality
  `(⨆ a : I, U a) = ⊤`, and `∀ a, IsAffineOpen (U a)`. This existential index universe
  loses no cover-existence case: neighbourhoods may be indexed by the points of S.
  No `Finite I` or `Nonempty I` assumption occurs.
- Nonnegative local integers: `n : I → ℕ`. Each family has exactly `n a + 1` members.
- Sections on the actual restricted module: existential
  `s : ULift.{u} (Fin (n a + 1)) → (E.restrict (U a).ι).sections`.
  `Scheme.Modules.restrict` is Mathlib's restriction functor along the open inclusion.
  The ULift is the explicit universe lift needed by the sheaf free-module API and
  the projective-space coordinate API; it has the same ordered finite coordinates.
- Generation: `Epi ((E.restrict (U a).ι).freeHomEquiv.symm s)`. This is precisely
  the `epi` field of the recorded `SheafOfModules.GeneratingSections`, specialized
  to the displayed family. It expresses local lifting/surjectivity as a sheaf,
  rather than requiring surjectivity on every open's sections.
- Quasi-coherence and finite type of the restriction: existential proof
  `hq : (E.restrict (U a).ι).IsQuasicoherent`, followed by
  `(E.restrict (U a).ι).IsFiniteType`. Binding the proof explicitly makes the
  canonical symmetric graded algebra well typed; hq is concluded, not assumed.
- The source P(E restricted):
  `(@SymmetricAlgebraSheaf.gradedAlgebraData (U a).toScheme
    (E.restrict (U a).ι) hq).relProj`.
  This is exactly the canonical symmetric-degree graded algebra and relative Proj
  used by `IsProjectiveBundle`; no abstract realization or arbitrary algebra is used.
- The target P to the specified local dimension:
  `ℙ(ULift.{u} (Fin (n a + 1)); (U a).toScheme)`, the recorded integral-base-change
  projective space with exactly n a + 1 homogeneous coordinates.
- The closed immersion of U-schemes: existential morphism j between those exact
  schemes, `IsClosedImmersion j`, and
  `j ≫ ℙ(ULift.{u} (Fin (n a + 1)); (U a).toScheme) ↘ (U a).toScheme =
    (@SymmetricAlgebraSheaf.gradedAlgebraData (U a).toScheme
      (E.restrict (U a).ι) hq).relProjHom`.
  Composition is in Lean's diagrammatic order, so this is precisely projection
  after j equals the source projection.
- The stated consequence H-projective is retained explicitly as `IsHProjective`
  of that same structural morphism. It follows from the displayed embedding and
  uses the exact recorded convention; it imposes no new hypothesis.
- No finite bound on I or uniform bound on n is included.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`; its definition is
  exactly the quasi-coherent / finite-type conjunction. The additional coherence
  clause of pqf-def-coherent is not needed in this item.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.GeneratingSections`, its `epi` field, and `IsFiniteType`.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.restrict`,
  `restrictFunctor`, `restrictAppIso`, the canonical restriction construction.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`:
  `AlgebraicGeometry.IsProjectiveBundle` was read to match its exact source construction;
  its public import exposes the canonical
  `SymmetricAlgebraSheaf.gradedAlgebraData`, `Scheme.GradedAlgebraData.relProj`
  and `relProjHom` used here.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, whose field is the finite-coordinate embedding;
  its public projective-space module supplies `ProjectiveSpace` and its projection.

The stated proof-dependency modules are imported nonpublicly, as required:
`Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`,
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`, and
`WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`.
The affine-opens-basis dependency is already available through Mathlib.
`lem-trf-symmetric-sheaf-map-degreewise-surjective` has no recorded Lean module,
so there is no module to import for that proof-only dependency. No statement
prerequisite is missing and no import cycle was introduced.
The theorem docstring includes all five accepted proof steps and their DAG ids.

Edge cases checked before writing:

- Empty S: choose empty I; the supremum condition is valid since top is empty,
  and every local conclusion is vacuous. No inhabited-cover condition is imposed.
- Zero E on a nonempty affine: choose n = 0 and the single zero generator;
  evaluation onto zero is epi. Its projective bundle is empty, which embeds into P^0.
- E = O: one generator, n = 0, and the usual P(O) ≅ P^0 factorization is allowed.
- Non-quasi-compact S and unbounded local generator ranks: I is arbitrary and n
  is a function, with no common rank bound or finiteness assumption.
- No field, characteristic, separatedness, Noetherianity, local freeness or ample
  sheaf hypothesis was added.

Searches actually run with msearch.py (group Q40, this item):

- leanfinder: `finite type quasi coherent module affine open cover projective bundle closed immersion projective space`.
  Eight hits include `Proj.affineOpenCover`, `Proj.affineOpenCoverOfIrrelevantLESpan`,
  `Proj`, and absolute-Proj properness/basic-open results. They concern a Proj's
  source charts, not the affine cover of the base with specified-rank embeddings.
- loogle: `AlgebraicGeometry.IsHProjective, SheafOfModules.GeneratingSections`.
  Zero hits; service reports unknown identifier `AlgebraicGeometry.IsHProjective`.
  That notion is project upstream, not Mathlib, and was read directly.
- grep: `projectiveBundle|ProjectiveBundle|IsHProjective` in Mathlib AlgebraicGeometry.
  Zero hits.
- leansearch: `A finite type quasi coherent sheaf has an affine open cover on which its projective bundle embeds into finite projective space`.
  Eight hits include `Proj.affineOpenCover`, quasi-compact-cover results and
  quasi-coherent-presentation / finite-type constructors. None is this assertion.
- rg in both project source roots for
  `lem-trf-projective-bundle-affine-presentations|affine.*presentations|projectiveBundle_affine`,
  and the narrower `projectiveBundle.*[Aa]ffine|[Aa]ffine.*projectiveBundle|lem-trf-projective-bundle-affine-presentations`.
  No exact statement or item declaration. The broad pattern has unrelated affine
  presentation hits; the narrow pattern has none.
- Read the neighbouring `GloballyGeneratedProjectiveBundle` and
  `ProjectiveBundleToHProjective` statements. The first assumes global generation
  and returns unspecified finite coordinates; the second assumes an ample sheaf.
  Neither supplies this arbitrary-base affine cover and its specified local ranks.

No statement correction or STATEMENT-DISPUTED issue was necessary.

Validation: scompile.py compiled this file as both sandbox and library module,
with no errors or non-sorry warnings (reported times 2.3 s and 2.2 s).

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
