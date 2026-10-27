## What changed

Reduced two of the four original holes while preserving every public signature,
definition, and existing public import of RationalPurityPresentation.

`pbcPurityAmbientProperties` now proves twisted lattice preservation by composing
`pbcPurityPull_mem`, `pbcTateAmbient_mem`, and shift stability of the intrinsic
triangulated subcategory. Both additive and both scalar-linear clauses are proved:
completed module pullback is linear; open extension is its linear left adjoint;
derived proper image is linear by its derived adjunction; composition retains
these properties. The remaining compact-support lattice transport is isolated in
`RationalPurityCompactLattices`.

`pbcPurityCompactScalar_properties` now restricts the actual integral comparison
to the full lattice categories, reflects its component invertibility through the
fully faithful inclusion, and rationalizes. Its naturality proof covers every
rational arrow using the existing uniformizer denominator argument. The private
`purityScalarLift_naturality` is generalized from a natural isomorphism to a natural
transformation, since its proof never uses an inverse. Twisted scalar naturality
uses the hom of its original comparison. The remaining integral finite-free
invertibility input is isolated in `RationalPurityCompactScalarInvertible`.

The two new bridge imports of the item are proof-only. The original zero-hole
coefficient-model API is extracted verbatim to `RationalPurityCoefficientModels`
and publicly re-exported. This preserves the old public environment and gives
the bridge statements the same named coefficient system without repeated literal
records. The extraction follows profiling of the oversized assembly module. Each
new bridge module contains one public statement, with a complete proof in words
and a matching new node. The extracted API has no holes. The item node's proof
and dependencies describe the two actual reductions.

Validation: `lcompile.py --all` compiled all four delivered modules successfully
after import cleanup. No profiling or debug options remain. Every original public
declaration occurs exactly once across the item and its public re-export; no
existing direct importer requires adaptation.

## Proved and sorry left

This is a decomposition, not two complete mathematical proofs: two original holes
are closed by two strictly smaller imported statements. Holes closed:

- `AlgebraicGeometry.Scheme.pbcPurityAmbientProperties` (six clauses, five proved
  directly and only compact-support preservation deferred).
- `AlgebraicGeometry.Scheme.pbcPurityCompactScalar_properties` (naturality proved
  directly on all rational maps; only integral component invertibility deferred).

Two original holes remain unchanged, both at
`prop-pur-rational-purity-transitivity-summands`:

- `AlgebraicGeometry.Scheme.pbcPurityStageA_coherence`.
- `AlgebraicGeometry.Scheme.rationalPurityTransitivitySummands`.

Two holes added:

- `AlgebraicGeometry.Scheme.pbcPurityCompact_lattices`, at
  `lem-pur-lifted-compact-support-lattices`.
- `AlgebraicGeometry.Scheme.pbcPurityCompactScalar_integral_isIso`, at
  `lem-pur-lifted-compact-scalar-invertible`.

The packet therefore has four holes, as did the starting module. No hole occurs
inside a definition or private helper. No axiom is introduced.

## No longer needed

No mathematical dependency is pruned. The original public imports are retained.
The coefficient-model proofs and their proof imports live in the extracted
module; this relocates their work without discarding it. The item drops these
proof imports, which its remaining declarations do not use:

- `Sheaf.Paper.IntegralCoefficientCompletenessTransport` (private import).
- `Sheaf.Paper.PbcConstructibleReductionPullback`.
- `Sheaf.Paper.PbcConstructibleReductionCriterion`.
- `Sheaf.Paper.PbcUniformReductionCriterion`.
- `Sheaf.Paper.IsomorphismComparisonScalarExtension`.
- `Sheaf.Paper.FiniteFieldFiber`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Noetherian`.

The extracted module also omits the unused private imports of
`IntegralCompactSupportUniformRestriction`, `PbcScalarExtension`, and
`PbcFiniteRawScalarComparison`; its public imports include the coefficient
comparison module because the unchanged geometric-bounds proof uses its
`coefficientPrimeUnit` theorem. The original item's public imports are preserved.

The final assembly and its original DAG route remain open, so none of their
planned dependencies is declared obsolete. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

There is a genuine presentation bridge between
`cbcIntegralCompactSupport_uniformRestriction` and this module's ambient image.
The former has `E : Type (u + 1)` and the unlifted valuation ring, while the latter
uses `E : Type u` and `PbcIntegralRing`, an ULift of that ring. The attempted direct
application fails with the compiler's coefficient-universe mismatch. Their data
cannot be identified by definitional equality. The new lattice statement records
only that transport and preservation step, rather than silently changing the
coefficient universe or category.

The source is currently present in lean/, despite an older quarantine rework row.
This delivery starts from that restored current module; no quarantine archive or
Lean attachment is removed. The unit route and all target statements are retained.

## New nodes

`lem-pur-lifted-compact-support-lattices` states preservation by the actual
proper/open image in the lifted PBC lattice presentation. Its source is
Bhatt--Scholze Lemmas 6.7.2 and 6.7.7 and the existing uniform-restriction proof,
with the actual-coefficient constructible-preservation theorem for the proper
factor. It is only one conjunct of the original ambient-properties assertion;
it has no rational functors, scalar-action clauses, or purity conclusions.

`lem-pur-lifted-compact-scalar-invertible` states invertibility of the specified
integral mate on a lattice. Its proof uses the completed finite-free coefficient
module decomposition and the canonical proper/open factorization. It asserts no
rational naturality or coherent family. Fixing the change's coefficient maps
allows arbitrary square proofs by proof irrelevance; no new comparison is chosen.

`def-pur-rational-purity-coefficient-models` attaches the original zero-hole
coefficient-model declarations at their new location. It adds no new
mathematical construction or unfinished proof. The relocation change record is
`coord/changes/Q2-rational-purity-coefficient-models.md`.

Both lemma nodes were checked against zero input, empty schemes, and identity and
ramified extensions where applicable. LeanSearch, LeanFinder/Loogle, Mathlib and
project grep, and blueprint searches found no theorem that specializes directly
to these lifted coefficient statements. The searches and proof steps are in the
node records. No existing definition changes. The public re-export preserves the interface;
there are no current direct importers of the item and no forced adaptations.
The change record lists all new consumers of the extracted module.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
