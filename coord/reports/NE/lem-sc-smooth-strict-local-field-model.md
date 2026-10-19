## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel` states
`AlgebraicGeometry.Scheme.smooth_strict_local_field_model`, with `sorry` as its whole proof.
No definitions or proofs are added. The mathematical statement of the node is unchanged.

Hypothesis and conclusion correspondence:

- Algebraically closed ground field: `(K : Type u) [Field K] [IsAlgClosed K]`.
- Integral scheme: `(Y : Scheme.{u}) [IsIntegral Y]`.
- Smooth finite-type K-scheme: the named structure morphism `f`, `[Smooth f]`,
  `[LocallyOfFiniteType f] [QuasiCompact f]`. These last two classes are precisely finite type.
- Dimension d: `(d a : ℕ)` and `hd : topologicalKrullDim Y = (d : WithBot ℕ∞)`.
- Geometric point: `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)`.
  Its image is `(y : Y)` with `hy : s (IsLocalRing.closedPoint Ω) = y`.
- The structural K-algebra on κ(y) is named by `[Algebra K (Y.residueField y)]` and
  `hκ`, which requires its spectrum map to equal `Y.fromSpecResidueField y ≫ f`.
  This is a specification of the given structure, not an additional condition on Y.
- Likewise `[Algebra (Y.residueField y) Ω]` and `hΩ` specify the chosen geometric embedding:
  its spectrum map followed by the residue-field point equals `s`.
- The integer a is exactly the residue-field transcendence degree, by `ha`.
- R is always the actual `strictHenselizationRing s`. Its K-algebra structure is named
  explicitly and `hK` requires its spectrum map to equal the canonical structural map
  followed by `f`. No arbitrary ring or replacement model is used.
- Regular local domain: the first conjunct is `IsRegularLocalRing R`, followed by an
  existential `IsLocalRing R` instance and an existential `IsDomain R` instance. These
  are conclusions. The instance lets only install these witnesses for the remaining type.
- Dimension d-a: `ringKrullDim R = ((d - a : ℕ) : WithBot ℕ∞)`.
- Chosen residue field: `e : IsLocalRing.ResidueField R ≃+* separableClosure (Y.residueField y) Ω`.
  The following spectrum equation says its composite with reduction and inclusion into Ω,
  followed by the canonical structural map, is the given geometric point s.
  In particular Ω itself has not been mistaken for the chosen separable closure.
- Fraction-field algebraicity via the structural embedding: `i : Y.functionField →+* FractionRing R`
  satisfies the displayed structural-map equation, using `Y.fromSpecStalk (genericPoint Y)`.
  Since Y is integral, its function field is this generic stalk and is the fraction field
  of every nonempty affine coordinate ring. The equation forces i to be the structural
  embedding. `letI := i.toAlgebra; Algebra.IsAlgebraic ...` asserts algebraicity for that map.
- A K-subfield of R: an existential field F with a K-algebra structure and
  `j : F →ₐ[K] R`. Since R is a domain, this field homomorphism is injective, so its image
  is exactly a K-subfield of R. This avoids attempting `Subfield R`, which needs R itself
  to be a field. It does not assume any coefficient-field data in a hypothesis.
- Separably closed: `IsSepClosed F`.
- Reduction identifies F with the residue field: `Function.Bijective ((IsLocalRing.residue R).comp
  j.toRingHom)`. The map itself is the specified reduction, not an unrelated field equivalence.
- Both degree equations: `Algebra.trdeg K F = (a : Cardinal)` and
  `Algebra.trdeg F (FractionRing R) = ((d - a : ℕ) : Cardinal)`. The latter's algebra
  structure is explicitly induced by j followed by the fraction-ring inclusion.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- Scheme conventions: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.SpecToEquivOfField`, `Scheme.fromSpecResidueField`; geometric points are written inline.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`;
  `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`: `Scheme.strictHenselizationStructuralMap`.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDim` and the recorded
  local-dimension convention `topologicalKrullDimAt` (the statement only needs the global one).
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- The existing Mathlib `Scheme.functionField`, `FractionRing` and `separableClosure` supply
  the standard objects already used in the proof dependencies. All recorded, available
  proof-dependency modules are imported without `public`; dependencies without Lean records
  cannot yet contribute a proof import.

Edge cases checked: d=0, a=0, generic points (a=d), closed points (a=0), and positive
characteristic. No divisor, positive-dimensionality or nonzero element is assumed. The empty
scheme is excluded by the node's integrality hypothesis itself. An empty separating basis
still gives K. An arbitrary geometric-point field may be larger than the relative separable
closure; the conclusion uses that relative closure and never identifies it with Ω. The
field F is not assumed perfect or algebraically closed. No local ring or domain structure
on R is assumed. All variables and the universe u are explicitly bound; all constructions
use the same ambient universe as the existing strict-henselization interface.

Searches performed:

- `msearch.py ... leanfinder "A smooth integral scheme over an algebraically closed field has
  a strict henselization with separably closed coefficient field and fraction field
  transcendence degree"`: 8 hits, including formal-unramified field criteria, henselian
  fields, formal smoothness over a perfect field, and HenselianLocalRing.TFAE; none states this result.
- `msearch.py ... loogle "IsRegularLocalRing, Algebra.trdeg"`: 0 hits.
- `msearch.py ... grep "strictHensel|coefficientField|coefficient_field"`: 0 hits in Mathlib.
- `msearch.py ... leansearch "strict henselization of smooth scheme coefficient field"`:
  service unavailable (Internal Server Error); no verdict assigned to this unavailable search.
- `rg` of `WeilConjectures/AlgebraicGeometry` for `strictHenselization|strictLocalization`:
  no results in the pinned checkout; `rg` for the item id and coefficient-field names in
  the full source and `lean/Sheaf` found no existing statement. The project contains a
  private `exists_coefficient_field_section` in `FirstOrderPowerSeriesComparison`, for
  formally smooth adic complete rings, which is a different result.
- Read the strict-henselization colimit construction and structural map, all recorded
  statement-dependency signatures/docstrings, the blueprint's two local-calculation
  paragraphs, the Mathlib regular-local, integral, smooth, residue-field,
  separably/algebraically closed, transcendence-degree and dimension interfaces.

Validation: server single-file compile via scompile.py, nice 19, two threads, 60 seconds;
clean before packaging. No local compiler or library build was run.

## Dependency modules

`def-weil-pbc-strict-henselization-limit`: its recorded upstream module
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization` is absent from this pinned
source checkout. The project's existing `Sheaf.AlgebraicGeometry.StrictHenselization`
constructs exactly the small representative affine pointed-neighbourhood coordinate-ring
colimit and its spectrum. Its `strictHenselization_properties` proves the cofiltered and
limit interpretation, with representative independence separately named in that module.
The dependency copy changes only `lean`, reusing this declaration with `existing: true`.
No replacement module or duplicate definition is delivered.

## Second reading by NE

I reread the node statement, its Stacks/blueprint source place, and the complete Lean signature.
The objects and hypotheses match item by item: an algebraically closed field `K`; an integral
scheme `Y`; the named structure morphism `f` with smooth, locally finite type, and quasi-compact
instances; dimension `d`; an algebraically closed geometric-point field `Ω` and point `s`; its
image `y`; residue and geometric-point algebra structures with `hκ` and `hΩ`; the residue
transcendence degree `a`; and the strict henselization ring with its specified K-structure `hK`.
These structure-map equalities specify the canonical maps associated to the node's conventions,
rather than adding geometric conditions.

The conclusion renders every clause of the node: `IsRegularLocalRing` and existential local and
domain instances for `strictHenselizationRing s`; dimension `d-a`; a residue-field ring
isomorphism to `separableClosure (Y.residueField y) Ω` whose composite point is `s`; an embedding
of `Y.functionField` into `FractionRing` with the structural-map equation and algebraicity; and a
K-subfield `F` with an algebra map into the strict henselization, separably closedness, bijective
reduction, and the two stated transcendence-degree equations. Quantifier order and conjunction
nesting agree with the node. No mismatch was found and no Lean change was needed.

I checked `d = 0`, `a = 0`, `a = d` at a generic point, positive characteristic, empty
transcendence basis, and the empty scheme edge (excluded by integrality). The common universe
`u` is used throughout, so no covered geometric-point or field case is excluded.

Searches were reread from the worker log and repeated with `rg` over Mathlib, the pinned
`WeilConjectures` source, and `lean/Sheaf`; the strict-local coefficient-field statement is not
already declared. LeanFinder/Loogle/grep hits concern general henselian or formal-smooth facts and
do not state this result. The dependency copy for
`def-weil-pbc-strict-henselization-limit` correctly reuses the existing strict-henselization
construction and no duplicate definition is present.

The delivered module compiled cleanly with `scompile.py` (nice 19, two threads, 60 seconds per file).

Maintainer independent reading: the delivered module omitted the already recorded proof-dependency
imports `Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula` (lem-kun-dimension-formula) and
`Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`
(lem-sc-closed-irreducible-dimension-trdeg). Both modules existed at the delivery base, and neither
was imported transitively. The worker claim above that all available proof-dependency modules
were imported was incorrect for the original delivery. The replacement module adds both as
non-public imports, as required by coord/brief-stage2.md §3. No declaration, signature,
mathematical statement, or dependency record changes. The replacement is verified separately
in the independent maintainer review.
