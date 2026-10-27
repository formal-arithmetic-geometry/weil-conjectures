## Worker report

The module `Sheaf.AlgebraicGeometry.ProperQuasicoherentFibreDimensionVanishing`
states `AlgebraicGeometry.proper_quasicoherent_higherDirectImage_vanishing`.
Its single proof is `sorry`; it defines no new objects. The seven accepted DAG proof
steps and their cited nodes are reproduced in the theorem docstring. All recorded
statement dependency modules and stated proof dependency modules are imported,
with proof-only imports private. No node statement or dependency list was changed.

Source read: `literature/stacks-project/limits.tex`,
`lemma-higher-direct-images-zero-above-dimension-fibre`, Tag 0E7D, statement and
complete proof. Part (1) is the pointwise result; the proof explicitly establishes
vanishing of the whole higher direct image when all fibres have dimension at most d.
It reduces arbitrary proper maps to finite presentation and then to a Noetherian base,
without assuming that the original base is Noetherian or that the module is flat.

Hypothesis and conclusion correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`, with arbitrary explicitly bound universe `u`.
- Scheme morphism f: `(f : X ⟶ Y)`.
- Properness: `[IsProper f]`. The Mathlib class is separated, universally closed and
  locally of finite type; universal closedness supplies quasi-compactness, giving the
  finite-type properness in the node.
- Nonnegative integer d: `(d : ℕ)`. This parametrizes exactly the integers d ≥ 0.
- Every scheme-theoretic fibre has dimension at most d:
  `(hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))`.
  This uses the actual residue-field fibre, not an arbitrary geometric fibre or a
  dimension of its coordinate ring that would require an affine hypothesis.
- Arbitrary structure-sheaf module F: `(F : X.Modules)`; this is definitionally
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
- Quasi-coherence only: `(hF : SheafOfModules.IsQuasicoherent.{u} F)`.
  There is no finite-type, finite-presentation, coherence or flatness assumption.
- Every higher degree i > d: `(i : ℕ) (hi : d < i)`. Since d ≥ 0, all integer
  degrees covered by the node are exactly these natural degrees.
- Vanishing of R^i f_*F:
  `IsZero (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived i).obj F)`.
  This is the ordinary right-derived direct image of structure-sheaf modules,
  the same form used by the recorded open-restriction and quasi-coherence lemmas.
  It is a zero object of Y.Modules, rather than vanishing only of global sections.
- No Noetherian or flatness hypothesis: neither occurs in the binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom category.
  The declaration's local-affineness field supplies precisely schemes.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber` (the
  pullback along `Y.fromSpecResidueField y`), with `fiberι` and
  `fiberToSpecResidueField` read to confirm which fibre is being measured.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, defined as the order
  Krull dimension of irreducible closed subsets, valued in `WithBot ℕ∞`.
- Recorded `Sheaf.AlgebraicGeometry.CoherentFiniteType` (pqf-def-coherent): its
  public interface exposes Mathlib's `SheafOfModules.IsQuasicoherent`. The conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` and the coherent predicate were read;
  neither is imposed, because the item requires only quasi-coherence.
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `AlgebraicGeometry.RingedSpace.moduleDirectImage`, whose actual data is Mathlib's
  module pushforward along the opens map and the structure-sheaf homomorphism.
  The recorded `derivedModuleDirectImage` and its resolution comparison were read.
  Ordinary `Functor.rightDerived` applied to this very moduleDirectImage is used,
  following `ordinaryHigherImage_isQuasicoherent` and
  `nonempty_higherDirectImage_openRestriction_iso`, the proof dependencies.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `CategoryTheory.Functor.rightDerived`
  is publicly imported because it occurs in the exported statement.

Edge cases checked before writing:

- Empty fibre has Krull dimension bottom, hence satisfies every nonnegative bound;
  the statement does not assume a nonempty fibre or surjectivity of f.
- An empty source gives zero direct image in the displayed positive degrees.
- Empty target gives the same conclusion and the fibre hypothesis is vacuous.
- d = 0 covers every i > 0, while i = d is intentionally excluded; identity and
  finite morphisms provide the expected dimension-zero examples.
- Zero coefficient modules are permitted. No finite generation is imposed.
- A proper morphism that is not finitely presented is included, as required by
  Tag 0E7D's first approximation step. Arbitrary non-Noetherian bases and nonflat
  quasi-coherent modules are included.
- The universe is arbitrary; the module universe explicitly matches the project's
  standard X.Modules, avoiding Lean's default-to-zero universe for IsQuasicoherent.

Searches (no exact existing theorem found):

- msearch leanfinder: "For a proper morphism of schemes with fibres of dimension
  at most d, higher direct images of every quasi coherent module vanish in degrees
  greater than d". Eight results: affine limit section lemmas and abstract derived
  category vanishing/t-structure lemmas; no geometric module theorem.
- msearch loogle: `SheafOfModules.IsQuasicoherent, "rightDerived"`: zero hits.
- msearch grep, Mathlib/AlgebraicGeometry:
  `higherDirectImage|directImage.*vanish|fibre.*dimension`: one comment in
  EllipticCurve/Weierstrass, no relevant declaration.
- msearch leansearch: "Proper morphism higher direct images quasi coherent sheaves
  vanish above fibre dimension": eight results, all properness/quasi-coherence
  definitions and instances, no matching theorem.
- rg over project `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `0E7D|02V7|zero-above-dimension-fibre`, proper vanishing, fibre-dimension names,
  and higher-direct-image zero statements. The item id occurs as a proof citation
  in ProperTopCohomologyFinite, which proves a different finiteness statement.
  The nearest upstream theorem is
  `Scheme.Modules.isZero_higherDirectImage_restrict_of_topologicalKrullDim_le`
  in `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FibreDimension`.
  Reading its section variables, signature and docstring shows additional finite
  presentation and flatness assumptions, so it is not the arbitrary-base theorem.
  Étale torsion cohomological-dimension results concern a different site/coefficient
  category and a bound 2d, and are not duplicates.

No missing notions, dependency repairs, statement correction, or
STATEMENT-DISPUTED issue was found.

Validation: scompile.py passed for both the sandbox and the final library module,
with no errors or warnings. Initial module-mode compilation exposed two visibility
requirements: public RightDerived (the functor occurs in the signature), and public
GrothendieckCategory.EnoughInjectives (the canonical instance is used to elaborate
that signature). Both were imported explicitly. The universe on IsQuasicoherent
was also made explicit. No injective-resolution hypothesis was added: the recorded
RingedSpace.moduleGrothendieckAbelian instance plus Mathlib's enoughInjectives and
InjectiveResolution instances supplies it for every source scheme.

The final node copy changes only `lean`, and records the theorem signature verbatim.
No new nodes or dependency modules are delivered. Independent review is left to
the maintainer, in accordance with the dispatcher's direct-delivery instructions.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
