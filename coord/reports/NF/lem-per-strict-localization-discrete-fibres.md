## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalizationDiscreteFibres` states
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_discrete_fibres`.
Its only theorem proof is `sorry`; no definitions or helper axioms are introduced.
The node statement is unchanged. The earlier Q54 review was stage 1: the current
node has `reviewed` but no `lean` or `reviewed_lean`, so this is its stage-2 statement.
The preserved sandbox initially contained only dispatcher brief markers, with no
module, node copy, report, or evidence of a completed stage-2 delivery.

Clause-by-clause correspondence:

- A Noetherian scheme is `{X : Scheme.{u}} [IsNoetherian X]`.
  Mathlib's `AlgebraicGeometry.IsNoetherian` means locally Noetherian and compact;
  its local condition is `IsNoetherianRing Γ(X,U)` for every affine open U.
- The points are `(x y : X)`.
- The specified specialization is `(hxy : x ∈ closure ({y} : Set X))`.
  In particular the orientation is x a specialization of y.
- A geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `(s : Spec (.of Ω) ⟶ X)`, using the recorded inline encoding.
- Its centre is exactly x, expressed by
  `(hs : (SpecToEquivOfField Ω X s).1 = x)`.
- The source of the canonical morphism is `strictHenselizationScheme s`.
  The morphism is the recorded `strictHenselizationStructuralMap s`, with no
  additional arbitrary choice of a map or extra hypotheses about that map.
- Discreteness of every fibre is
  `∀ z : X, DiscreteTopology {t : strictHenselizationScheme s |
  strictHenselizationStructuralMap s t = z}`.
  This subtype has the induced topology; it is precisely the topological fibre.
- Nonemptiness of the fibre over y is
  `Nonempty {t : strictHenselizationScheme s |
  strictHenselizationStructuralMap s t = y}`.
- The two conclusions are joined by `∧`. No finiteness, flatness, or surjectivity
  conclusion was added. All variables and the universe are explicitly bound,
  and `set_option autoImplicit false` enforces this.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; consumed through
  `Mathlib.AlgebraicGeometry.Noetherian` and `AlgebraicGeometry.IsNoetherian`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, and
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme`, and
  `Scheme.strictHenselization_properties` (upstream import selection below).
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, characterized by
  `Scheme.exists_strictHenselizationStructuralMap`.

The theorem docstring carries all six DAG proof steps: the affine triple-colimit
comparison, the specified-prime local-base identification and pair/triple
comparison, zero-dimensional fibres, the quotient/localization Noetherian
calculation including the zero ring, the finite-discrete spectrum and fibre
homeomorphism, and faithful-flatness over the local base for nonemptiness.
The following proof-dependency modules are imported without `public`:

- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`:
  `Scheme.etale_local_ring_triples`.
- `Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization`:
  `Scheme.etaleResidueTriples_localized_isStrictHenselization`.
- `Sheaf.RingTheory.StrictHenselizationTriples`:
  `Scheme.strictHenselization_triples`.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn`.
- `Mathlib.RingTheory.Localization.Submodule`:
  `IsLocalization.isNoetherianRing`.
- `Sheaf.RingTheory.StrictHenselizationNoetherian`:
  `Algebra.isNoetherianRing_iff_isStrictHenselization`.
- `Sheaf.RingTheory.FilteredEtaleFiberStructure`:
  `CommAlgCat.filteredEtale_fiber_structure`.
- `Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete`:
  `AlgebraicGeometry.finite_and_discreteTopology_of_topologicalKrullDim_le_zero`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`:
  `PrimeSpectrum.preimageHomeomorphFiber`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`:
  `PrimeSpectrum.localization_comap_isEmbedding` and `localization_comap_range`.
- `Sheaf.RingTheory.StrictHenselizationFaithfullyFlat`:
  `Scheme.strictHenselization_faithfullyFlat`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`:
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`.

Edge cases checked mathematically before stating:

- For the empty scheme, there are no x, y or geometric points, so the statement
  has no instances. It adds no nonemptiness hypothesis on the scheme.
- For y = x the closure condition holds and the closed fibre is nonempty.
- For a field, the strict localization is the spectrum of a separable closure;
  its one-point fibre is discrete and nonempty.
- Fibres outside an affine open neighbourhood of x are empty; `DiscreteTopology`
  on an empty subtype has the intended meaning. Nonemptiness is asserted only
  over the specified generization, never over all points of X.
- Nonreduced schemes are included; the proof uses spectra and the quotient-ring
  calculation and imposes no reducedness, integrality, or characteristic condition.
- No immediate-specialization, dimension-one, finite-type, or finite-morphism
  hypothesis was introduced. On A² at its origin, y may be the generic point
  of any line or of the whole plane.
- The common arbitrary universe u is the recorded strict-henselization and
  geometric-point interface; it imposes no finite/countable size restriction.

Searches for an existing statement:

- `msearch.py leanfinder`, query: "Strict localization of a Noetherian scheme
  has discrete fibres and nonempty fibres over generizations of its centre".
  Eight hits concerned locally Artinian/Noetherian schemes, germ injectivity,
  Jacobson fibres and partial maps; none states this result.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.Scheme.Hom.discrete_fiber, DiscreteTopology`.
  No hits; unknown identifier `AlgebraicGeometry.Scheme.Hom.discrete_fiber`.
- `msearch.py grep`, query `strictHensel|strictLocalization|discrete_fiber`
  in Mathlib/AlgebraicGeometry. One hit was the Fiber module's documentation
  for finite morphisms; it does not apply to a general strict localization.
- `rg` on the upstream WeilConjectures and project lean/Sheaf trees for
  `strictHenselization.*[Dd]iscrete|strictLocalization.*[Dd]iscrete|discrete.*[Hh]ensel`
  and the exact node id found no existing theorem. The exact proposed name
  was also absent from these trees and `dag/lean_names_upstream.json`.
- The source PDF was read with `pdftotext`: ILO Expose XIV 2.1.3 final paragraph
  and 2.1.4 proof, printed page 210, explicitly use discrete fibres and a nonempty
  generic fibre. No statement correction or STATEMENT-DISPUTED issue is needed.

Validation: the delivered module compiled cleanly with `scompile.py`, in both
sandbox and library modes (1.7 seconds each). No warning or error was reported.

## Import compatibility

The recorded strict-localization dependency module
`Sheaf.AlgebraicGeometry.StrictHenselization` and the upstream module
`WeilConjectures.AlgebraicGeometry.StrictHenselization` export the same global
names. The canonical structural map already imports the upstream module.
Following the brief's instruction to prefer the upstream side of duplicate
imports, this module imports the structural-map module and obtains all the
strict-henselization declarations through it. It does not import the conflicting
Sheaf implementation as well. The required global declaration names remain
`Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme`, and
`Scheme.strictHenselization_properties`; no private copy is introduced.

The upstream source was read with `scompile.py --source`: its ring is literally
the colimit of the small representative affine-pointed-etale coordinate diagram,
its scheme is the spectrum, and the properties theorem supplies initiality,
cofilteredness and the limit. These are exactly the recorded node's mathematical
notion. Thus no dependency node needs changing. An initial dry run including a
redundant dependency-record update exposed pre-existing proof/proof_deps
mismatches in that dependency; that redundant update was removed. The delivery
changes only the item's Lean record and adds its module and this report.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
