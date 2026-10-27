## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerP1Uniform.towerP1_uniform_ctf_domains` from
three strictly smaller argument steps, with its original statement unchanged. The
private lemmas `bounds_of_constructibleTor` and `constructibleTor_of_bounds` convert
between the uniform-tower predicate and explicit t-structure/cohomology/Tor bounds.
The proof obtains the precise result at each n, reuses the same input endpoints at
every level, and derives pullback preservation rather than assuming it separately.

Moved the six existing definitions, verbatim and under the same public names, to
`Sheaf.Paper.TowerP1CtfData` to allow the independent proof-step modules to refer to
them without a circular import. The original module publicly re-exports the data.
The original node now owns only the theorem; the data node owns the definitions.
Change record: `coord/changes/A5-tower-p1-ctf-data-relocation.md`.

Validation: all five delivered Lean modules compiled through lcompile.py in import
order. The item has no direct holes; each new statement has a whole `by sorry` proof,
a source, a complete proof in words and its own DAG node. A subsequent compile checks
the final proof imports; deliver3.py performs the final compiler/axiom probes.

## Proved and sorry left

Original holes: 1. Closed: `towerP1_uniform_ctf_domains`
(`lem-sp-tower-p1-uniform-ctf-domains`). Item holes left: 0.
Added holes: 3. This is a decomposition, not a sorry-free proof or positive net hole
reduction; the change is 1 closed minus 3 added = -2 textual holes before the
maintainer's pinned-closure ledger calculation.

Every remaining hole is in namespace `AlgebraicGeometry.ProEtale.SpTowerP1Uniform`:

- `uniformTower_etale_domains`, in `Sheaf.Paper.TowerUniformEtaleDomains`, node
  `lem-sp-uniform-tower-etale-domains`: the bounded-below/etale-origin argument for
  any scheme, without either functor-preservation or local-model conclusion.
- `towerP1_push_ctf`, in `Sheaf.Paper.TowerP1ProperCtf`, node
  `lem-sp-tower-p1-proper-ctf`: proper pushforward preservation alone; its proof
  specializes the uniform bound through the identity compactification and compares
  the normalized realizations. It contains no pullback or domain conclusion.
- `towerP1_level_ctf_model`, in `Sheaf.Paper.TowerP1LevelCtfModel`, node
  `lem-sp-tower-p1-level-ctf-model`: the finite-ring construction at a SINGLE n,
  from only that level's input bounds. It contains no uniform-tower preservation,
  no assertion about other levels, and no proper-image/domain conclusion.

There is no hole in a definition or a private helper. The combination of the
single-level result into uniform pullback preservation is fully proved in Lean.

## No longer needed

The original module's following proof imports are removed there:

- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.Paper.CompactSupportUniformTorBound`
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`
- `Sheaf.AlgebraicGeometry.EtaleChartComparisonIsos`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`

These are replaced by the three proof-step imports. The finite-origin, flat-model,
line-model, comparison, derived-evaluation and flat-pullback ingredients remain
needed below the new steps, and are recorded there. The existing public imports
are preserved through the new publicly re-exported data module.

The following planned detours are not needed on this item's route:

- `lem-pur-twist-sheaf-locally-free` / `Sheaf.Paper.PurTwistSheafLocallyFree`: positive
  quotient finiteness is already a proved instance of the normalized tower module.
- `lem-weil-pbc-projective-space-standard-charts`, `sbc-lem-affine-space-smooth`, and
  `lem-weil-pbc-smooth-local-on-source`: the existing proved
  `ProjectiveLine.smoothOfRelativeDimension_one` supplies the conclusion directly,
  node `lem-sc-projective-line-smooth-relative-dimension-one`.
- `det-pe-finite-tor-comparison-noetherian` /
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`, and the associated
  qcqs preparation `lem-weil-pbc-qcqs-over-affine`: that comparison theorem is in
  coefficient-sized small-model coordinates; `lem-exc-comparison-tor-interval` /
  `Sheaf.AlgebraicGeometry.ComparisonTorInterval` already has exactly the intrinsic
  coordinates needed by LocalModel and preserves the same interval.

No existing module is withdrawn, and no globally pruned module is claimed. The
parent still reaches every necessary geometric/flat-model step through the new nodes.
No unit statement or realized proof step is bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The declared Noetherian comparison theorem uses different small-model categories
from LocalModel. The existing intrinsic interval bridge above avoids inventing a new
comparison or weakening the conclusion. The DAG's chart proof also duplicated an
existing proved projective-line smoothness instance. These are shorter applications
of existing tools, with no statement correction.

The original named blueprint source currently contains the triangle-identity and
Levels paragraphs, rather than the expanded standing-setting restriction. The
expanded six-step proof is retained in the existing node and original theorem
docstring; the new nodes state its domain, proper-image and finite-level pieces
and cite the corresponding existing Stacks-backed declarations.

The whole result is not moved under a fresh name: the one-level lemma has no
uniform premise or conclusion; the domain and proper-image results are separate
strict subarguments. The parent proves the common-interval assembly and the
pullback restriction from that finite-level assertion. Edge cases checked in the
statement design: zero objects, empty base/open, n=0 meaning exponent 1, coincident
interval endpoints, and independent r,s versus a,b. Tor amplitude itself enforces
a<=b. No extra ordering assumption was added to the original precise clause.

## New nodes

`def-sp-tower-p1-ctf-data` owns exactly the six pre-existing data declarations in the
new data module. It defines no new mathematical object and contains no sorry.

`lem-sp-uniform-tower-etale-domains` isolates original step 2, generalizing the
scheme parameter because the domain argument uses only finite coefficients,
constructibility and exact componentwise cohomology.

`lem-sp-tower-p1-proper-ctf` isolates original step 3, preserving the specified proper
image by the uniform bound and normalized presentation comparisons.

`lem-sp-tower-p1-level-ctf-model` isolates original steps 4-6 at a single n. It retains
the global and affine-local witnesses and precise shifted intervals, so that the
proved parent can assemble them with common endpoints.

All four nodes inherit the original chapter and unit, point to the nearest blueprint
ancestor `det-sp-tower-p1-adjunction`, and record actual LeanSearch, LeanFinder and
Mathlib grep queries from searches.jsonl. Whole-blueprint searches for uniform tower
etale origins and projective-line uniform Tor/flat models found no duplicate. The
existing source-library smoothness node and intrinsic Tor bridge are reused.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
