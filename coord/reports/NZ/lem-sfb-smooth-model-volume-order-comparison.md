## Worker report

The delivery states `AlgebraicGeometry.smoothModel_volumeOrder_comparison`, with one
`sorry` and no other postponed proofs, in
`Sheaf.AlgebraicGeometry.SmoothModelVolumeOrderComparison`. The item's natural-language
statement is unchanged. Three new definition nodes supply the absent trait-specific
interfaces. Their definitions contain real data or explicit predicates, with no choice
from unproved existence and no new axioms. Every file sets `autoImplicit false`.

Source read: the primary BLR scan named in the node, printed pp.104--105 (PDF pages
110--111), order construction and Lemma 1; also pp.106--107 for the component-open
use. The current blueprint unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
is the six-functor stability unit; the item's recorded BLR supporting branch is retained.
`blueprint_refs.py ancestor` returns None, which is preserved for the new nodes.
There is no repair note for this item. The example CompactObject module is withdrawn;
its current node points to `WeilConjectures.CategoryTheory.CompactObject`.

Hypotheses and clauses, in the order of the node:

- The trait is `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  `π` and `hπ : Irreducible π` specify the uniformizer, exactly by Mathlib's
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`. `E`, its field/algebra instances,
  and `[IsFractionRing R E]` specify the fraction field. The special fibre uses the
  canonical residue field at `IsLocalRing.closedPoint R`; no arbitrary residue map is
  supplied. The base scheme is always `Spec (.of R)`.
- Products and fibres are `pullback`, `pullback.fst/snd`, and `M.hom.fiber`/`fiberι`.
  These are the conventions of `def-pc-base-change`, not pointwise set fibres.
- Smoothness is `Smooth`; finite type is `LocallyOfFiniteType` and `QuasiCompact`.
  Separatedness is `IsSeparated`, whose definition is the closedness of the diagonal.
- `Ω`, `[Field Ω] [IsAlgClosed Ω]`, `s`, and `hs` specify a geometric closed point.
  `Scheme.strictHenselizationRing s` is the recorded small affine-neighbourhood colimit.
  `traitStrictBase s` is the spectrum of the canonical comparison isomorphism followed
  by upstream's structural map. `FractionRing` is used for its generic restriction;
  it is the field of fractions once the strict henselization is a DVR.
- `IsBaseDense` tests density on every scheme-theoretic fibre. `IsTraitRationalMap`
  requires an over-base representative on such an open. The carrier is Mathlib's
  existing `Scheme.RationalMap`, not a duplicate quotient. On these reduced separated
  models, equality on an ordinary dense open forces equality on the intersection of
  the representative domains, which is base-dense. Thus this is the source's quotient.
  `IsMaximalTraitRepresentative` requires `p.domain = v.domain`, the actual union of
  representative domains. `IsTraitBirational` records the stated open-isomorphism
  notion, though the comparison does not assume birationality on the special fibre.
- `SmoothTraitModel` contains exactly a smooth separated finite-type structural map
  and an isomorphism of its generic fibre with `G`. Its generic inclusion uses the
  specified isomorphism. It imposes no nonemptiness, irreducibility, group law on the
  model, relative dimension, or connectedness beyond the node's conditions.
- `G : Over (Spec (.of E))`, `[GrpObj G]`, `hGsmooth`, `hGsep`, `hGft`, and `hGqc`
  express the smooth separated finite-type group. `hd` expresses dimension d by
  `topologicalKrullDim G.left = d`; this does not replace it by an extra pure-dimension
  hypothesis. `d : ℕ` includes zero.
- `ω : Γ(traitTopForms G.hom d, ⊤)` is the section of the recorded top exterior
  sheaf, `hω : IsFreeGenerator ω` expresses nowhere vanishing, and
  `hinv : IsLeftInvariantTopForm G d ω` expresses left invariance. The last predicate
  compares multiplication with the second projection using differentials RELATIVE
  TO THE FIRST PROJECTION; using absolute differentials here would be incorrect.
- The first conjunct quantifies over every special component and its generic point,
  and concludes the local ring is a domain and DVR, that the image of π is
  irreducible (hence its uniformizer), and `∃! n : ℤ, IsTraitVolumeOrder ... n`.
  The order relation requires a neighbourhood frame whose pullback to the generic
  fibre is π^(-n)ω, exactly the local-generator definition. For an invertible coherent
  line a stalk generator extends to a frame on a neighbourhood, so no stronger
  global normalization hypothesis has been imposed.
- The second conjunct says every smooth model with nonempty special fibre has a
  morphism from `Scheme.strictHenselizationScheme s` over the trait.
- The third conjunct assumes the two special fibres irreducible, supplies their
  generic points, and uses the integers satisfying the preceding unique-order
  relation. `v`, `hv`, `e`, `he` specify the base-rational map and its generic
  isomorphism with the given identifications, without requiring a group homomorphism.
  `a : Γ(G.left, ⊤)ˣ` and `ha : TopFormPullsTo ... ω (a • ω)` state the multiplier
  equation. `hx : HasTraitUnitSection M s a Set.univ` is precisely the existence of
  a strict-henselian integral point on M at which its value is a unit, i.e. valuation
  zero. The conclusion is `nN ≤ nM` and existence of a representative on the maximal
  domain with `IsOpenImmersion p.hom ↔ nM = nN`. Existence of that representative is
  included, rather than leaving the assertion vacuous.
- The fourth conjunct is separate and does not inherit irreducibility or nonempty
  special fibres. `hM`, `hN` are finiteness of both component sets; `hoM`, `hoN`
  give the common integer n₀ at every component generic point. `hx` requires the unit
  section on EACH source component set (that component plus the entire generic
  fibre). It concludes an open immersion on an existing MAXIMAL representative.
  This covers its entire domain, not only neighbourhoods of component generic points.

Top-form maps are pinned by an explicit equation on every local wedge of universal
differentials. `TopFormPullsTo` and the order relation existentially quantify a map
with this full characterization; the local wedges generate the exterior sheaf, so
this quantifier does not introduce an arbitrary map. No canonical datum is replaced
by `Nonempty` or by a chosen unknown equivalence. Scalar multiplication by π^(-n) is
through the explicitly constructed global-function ring homomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`;
  their scheme, open, and spectrum signatures were read at lines 42, 74, 470, 479.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` and
  `irreducible_iff_uniformizer`, including the domain/local PID/nonfield conditions.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its module-base-change
  declaration and its full documentation specify `pullback`, `fst`, `snd`; those
  actual scheme base-change objects are used, rather than its module-only functor.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and
  `SmoothOfRelativeDimension`; only `Smooth` is assumed. `FiniteType` supplies
  `LocallyOfFiniteType`, and `QuasiCompact` supplies the second finite-type condition.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated` is its diagonal form.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj` on the slice, with `MonObj.mul`;
  the complete group-scheme node's terminology in upstream GroupScheme.Defs was read.
- The geometric-point record uses `IsAlgClosed` and `Scheme.SpecToEquivOfField`;
  the theorem uses its explicitly permitted field-plus-morphism form.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`: `strictHenselizationRing`,
  `strictHenselizationScheme`; `StrictHenselizationExtension` supplies the canonical
  `smallStrictHenselizationColimitIso`, and `Sites.StrictHenselization` supplies
  `strictLocalizationToBase`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials` and `relativeDifferentialsDerivation`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`: `exteriorSheaf` and
  `exteriorSheafSection`, including the degree-zero convention. The later upstream
  exteriorPower construction was inspected but not used as a substitute for this
  dependency's recorded exteriorSheaf.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`;
  its local trivialization definition was read. The local-frame predicate is the
  existing `Scheme.Modules.IsFreeGenerator` in Modules.FreeGenerator.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` in the conclusion;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` is a proof dependency.

Every recorded proof-dependency module currently available was imported privately,
except the modules already imported publicly as statement dependencies. Unstated
proof dependencies (smooth-trait infrastructure, group differentials from identity,
smooth-space étale sections, line-order normalization, local rational spreading,
cotangent criterion, dense-open flat criterion) have no recorded modules; nothing
from their proofs is assumed as a theorem hypothesis. The seven-step proof docstring
names these nodes for stage 3.

Edge cases checked: d=0 uses the empty wedge and includes the zeroth exterior sheaf.
Disconnected G is allowed; the generic inclusion and component sets use the whole G.
Empty special fibres are allowed in the finite-component clause and yield vacuous
component hypotheses, while the conclusion is still an open immersion on the
maximal domain. IrreducibleSpace in the third clause includes nonemptiness. The
section-existence clause only assumes nonempty special fibre. Arbitrary residue
characteristic, nonperfect residue fields, non-henselian R, and negative orders are
retained. One universe u is used for schemes and their coefficient fields as in the
recorded scheme-site interfaces; it can be increased to contain any chosen data.

Searches actually run through msearch.py: LeanFinder on rational generic isomorphisms
and differential orders returned open-immersion basics; Loogle on
`AlgebraicGeometry.PartialMap,AlgebraicGeometry.RationalMap,IsDiscreteValuationRing.valuation`
reported an unknown first identifier and zero hits (not evidence of nonexistence).
LeanSearch on smooth trait maps found ordinary Mathlib rational maps, which are reused.
Additional LeanSearch/LeanFinder queries and exact grep outputs are stored verbatim
in each new node's mathlib_searches. rg of Mathlib, WeilConjectures, Sheaf, the upstream
name index, and the DAG found no existing interfaces under these names. Conceptual
DAG searches found only statement nodes using these notions, not definition nodes.
Blueprint searches for volume and base-dense returned no matches; smooth model found
one unrelated real-compactification node, and top form no matching definition.

No STATEMENT-DISPUTED flag and no statement correction is needed.

## New nodes

`def-sfb-smooth-trait-model` defines the model, canonical generic inclusion, stalk
scalar map and strict-henselian structure map. Its source is BLR 4.3's model convention.
The smooth-model searches found ordinary smooth morphisms, not a model with a specified
generic identification; no existing DAG definition carries it.

`def-sfb-trait-rational-map` defines fibrewise density, the over-base rational-map
predicate, maximal representatives, generic-isomorphism compatibility, and birational
representatives. Mathlib's ordinary RationalMap is reused. The absent part is fibrewise
base-density, not the ordinary rational-map quotient. Source: BLR 2.5 and 4.3 Lemma 1.

`def-sfb-trait-top-form-order` defines only the specific top-form pullback relations,
relative left invariance, normalized local order, component sets and the unit-section
condition. It reuses the recorded differential and exterior sheaves. Source: BLR 4.2
and the 4.3 order construction. Its complete generator characterization prevents
unspecified canonical maps. Search outputs in its node show no existing trait-order
or top-form-invariance interface.

## Second reading by NZ

This is an in-thread second pass; the dispatcher forbids starting other agents, and
an independent maintainer review follows delivery. I reread the node and all four
files with the source's normalization and determinant equations open. I checked each
of the hypothesis/conclusion correspondences listed above. In this pass I changed
the open-immersion assertions to assert existence of the maximal representative,
rather than merely quantify over any supplied maximal representative. I checked that
left invariance uses forms relative to pr1, the multiplier is evaluated on an actual
strict-henselian section of the specified component set, and π^(-n) has the source's
sign convention. All three new nodes' Lean signatures and declaration lists were
then regenerated from their module files. No item statement, proof, or dependency
record was changed; the item only gains these three definition dependencies and lean.
