## What changed

Repair: removed the private duplicate `cohomologyMap_comp_explicit` theorem from
`EtaleCohomologyOpenRestrictionNaturality`. Its sole use now invokes the existing
`cohomologyPullbackFunctorial` component directly, so the module no longer restates a
library theorem already provided by `EtaleOpenCohomologyMaps`.

Proved `AlgebraicGeometry.Etale.etale_mayerVietoris_pullback` with its signature and
existing docstring unchanged. The proof explicitly chooses all eleven restriction and
pullback maps. Their eleven identification clauses are reflexivity proofs. It obtains
the two connecting maps and the two exact sequences from the new connecting-map bridge,
proves the whole-scheme restriction squares separately for U and V, and combines the
two intersection restriction squares by `AddMonoidHom.map_sub`. The final connecting
square is the supplied bridge conclusion. This is a reduction into a strict part of the
argument, rather than a renaming of the original existential statement.

Added three modules:

- `Sheaf.AlgebraicGeometry.EtaleOpenCohomologyMaps`: two transparent formulas abbreviate
  exactly the existing statement's open restriction and restricted pullback maps.
  `openCohomologyPullback_restrict` is proved from `cohomologyPullbackFunctorial` and
  cancellation of `upperStarComp` comparisons, using a genuine chain of equalities.
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOpenRestrictionNaturality`: proves
  `openCohomologyPullback_restriction` for arbitrary nested opens, without a cover
  assumption. A private helper expresses a transported composite pullback as a single
  pullback followed by its coefficient morphism. The coefficient equality follows from
  the two rearranged associativity laws in `WeilConjectures.SixFunctors.BaseChange.Pasting`.
  This proves the second kind of square independently of any connecting morphism.
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisConnectingPullback`: states only the two
  exact sequences, their initial injections, and compatibility of their connecting maps.
  It does not assert either kind of ordinary restriction square and does not quantify
  over the eleven already prescribed restriction and pullback maps.

The item's new imports are proof-only. The new modules' public imports provide what
appears in their statements; all remaining imports are used in proofs. Updated the parent
DAG proof to match this assembly and supplied one node for each new module.

Validation: all four delivery modules compiled in import order with no warnings. In
particular the two ordinary naturality lemmas compile with no direct `sorry`. The source
library's enough-injectives, additive inverse-image, finite-limit and finite-colimit
instances were also checked separately using `inferInstance`. No existing definition,
statement, universe, or target was changed. The required deliver3.py dry run is the final
mechanical check; this report contains no second-reader verdict.

## Proved and sorry left

Proved the one original sorry:
`AlgebraicGeometry.Etale.etale_mayerVietoris_pullback`
(node `lem-weil-pbc-etale-mayer-vietoris-pullback`). No `sorry` remains in the item's module.

Also proved:
`AlgebraicGeometry.Etale.openCohomologyPullback_restrict`
(node `lem-weil-pbc-open-cohomology-whole-restriction-naturality`) and
`AlgebraicGeometry.Etale.openCohomologyPullback_restriction`
(node `lem-weil-pbc-open-cohomology-restriction-naturality`), including all their private helpers.

Exactly one new sorry remains:
`AlgebraicGeometry.Etale.etale_mayerVietoris_connecting_pullback`
(node `lem-weil-pbc-etale-mayer-vietoris-connecting-pullback`). Its proof is exactly
`by sorry`; its docstring and node give the resolution construction and transport proof.
This delivery therefore leaves the connecting-map construction for a later worker; it
does not claim that the original result is independent of all unresolved dependencies.

The new statements were checked on empty opens, equal nested opens, the identity
morphism, and the split cover with one open all of X. There is no artificial nonempty,
nontriviality, properness, torsion or degree-positivity assumption. In particular the
difference sign is identical on both sides and the initial degree-zero injections are
present. The intersection on Y is exactly the original `g ⁻¹ᵁ (U ⊓ V)`.

## No longer needed

No existing import was removed: the original public imports are needed by its unchanged
statement. The new proof has only the two new proof imports that it uses.

On this proof branch, the connecting construction no longer needs the general statement
modules `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
(`lem-weil-pbc-module-sheaves-enough-injectives`) or
`Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
(`prop-weil-pbc-inverse-image-exact`). Existing Grothendieck-abelian sheaf and enough-injectives
instances, together with the source library's proved exact inverse-image instances,
provide the precise abelian-sheaf facts required here. These two nodes are absent from
the new construction's proof dependencies. This is branch pruning, not a claim that
these modules have no other callers in the entire target closure.

Every old parent proof dependency is absent from the new parent proof_deps:

- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-etale-mayer-vietoris`
- `prop-weil-pbc-inverse-image-exact`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-cohomology-pullback-functorial`
- `def-weil-pbc-cohomology-pullback`
- `prop-weil-pbc-cohomology-resolution-independent`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-direct-image`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-complex-ses-long-exact-naturality`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-open-restriction-pullback-unit`

Except for the two branch-pruned nodes above, these dependencies are retained in
the new connecting construction or in the ordinary-naturality nodes. They are
removed from the parent assembly, not claimed globally obsolete. Ordinary restriction compatibility
uses composition functoriality and coherence instead of the chain-level section/unit
construction, but the latter is retained where the connecting argument needs it. The
unit `sk-thm-p1` and all its realized statement and proof steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The parent plan cites the chain-level construction inside the Mayer-Vietoris proof as
though it were a usable part of that theorem's Lean signature. The actual
`etale_mayerVietoris` statement gives derived section functors, natural isomorphisms,
and exactness, but does not identify the restriction maps with the prescribed Ext-based
`cohomologyMap` formulas or expose a pullback-natural choice of connecting maps.

Likewise `cohomologyPullbackFunctorial` exposes coefficient naturality, composition and
identity; its Lean signature does not expose the resolution-parametrized clause 2 and
restriction-to-sections clause 5 cited in the parent's natural-language proof. It suffices
for both ordinary squares, which are now proved. The new connecting node explicitly
owns the additional comparison with the chain-level section construction. Its proof
uses evaluation at 1 in the constant integer sheaf to identify the Ext pullback on
representing cocycles with the adjunction-unit section map; a mere nonempty natural
isomorphism is not asserted to supply this compatibility by itself.

The literature source checkout is absent on this machine. The actual proofs of
[Stacks 0A50](https://stacks.math.columbia.edu/tag/0A50) and
[Stacks 01F7](https://stacks.math.columbia.edu/tag/01F7) were read online. The former
constructs the exact complexes; pullback compatibility and nested-open compatibility
are recorded as agent-written consequences, not as statements explicitly made there.
LeanSearch returned Internal Server Error. That failed search is recorded with a null
verdict; LeanFinder, Loogle, local Mathlib and library searches were used instead.

## New nodes

`lem-weil-pbc-open-cohomology-whole-restriction-naturality` records the proved square for
restriction from the whole scheme, as well as the transparent map formulas used by both
new statements. Module: `Sheaf.AlgebraicGeometry.EtaleOpenCohomologyMaps`.

`lem-weil-pbc-open-cohomology-restriction-naturality` records the proved square for any
nested pair of opens. Module: `Sheaf.AlgebraicGeometry.EtaleCohomologyOpenRestrictionNaturality`.
This has no cover or connecting-map hypothesis and is a reusable, independently proved
part of the parent argument.

`lem-weil-pbc-etale-mayer-vietoris-connecting-pullback` records the one remaining
construction/transport step. Module:
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisConnectingPullback`. Its statement asserts only
exactness and the connecting square; the parent supplies and proves the other squares.

No change record is needed: all existing declarations and statement dependencies remain
unchanged, and no existing public import was changed.

## Earlier second reading (a previous round; superseded)

1. Compared the complete parent module with the repository using diff. PASS: the
   existing theorem signature, universe, public imports, and original docstring are
   byte-for-byte unchanged. The only parent changes are two proof-only imports and
   replacement of its proof. No existing definition or target statement changed.
2. Compiled all four modules locally in import order without errors or warnings.
   PASS: exactly one direct sorry remains, in the named connecting theorem listed
   above; both new definitions have explicit map formulas. No forbidden declarations
   or kernel-check bypasses occur. A scratch-copy axiom audit checks all six public
   declarations: the definitions use only propext, Classical.choice and Quot.sound;
   the four public theorems additionally use sorryAx from the still-open results.
   No other axiom occurs. The delivery tool additionally probes every delivered declaration.
3. Read the remaining connecting statement, its docstring, its node, and the Stacks
   construction at https://stacks.math.columbia.edu/tag/0A50. PASS: it is the exactness
   and connecting-square part only; both ordinary kinds of squares are genuinely
   proved separately. Empty-open covers, U=V=X, identity g, and degree zero agree with
   the split sequences and initial injections. Independent LeanFinder, Loogle and
   grep searches for connecting-map naturality found HomologySequence.δ_naturality,
   an ingredient already used in the planned proof, not the etale/Ext comparison.
   Library searches found no theorem with the full prescribed-map conclusion. That
   comparison is substantial and cannot be closed in a few minutes.
4. Read the parent assembly and both ordinary-naturality proofs downward. PASS:
   they use existing composition functoriality, coefficient naturality, inverse-image
   associativity and additivity; the connecting theorem supplies only the unresolved
   construction. Imports serve either signatures or proofs, with proof imports plain.
   Expanded No longer needed to enumerate every old parent proof dependency, and
   distinguished dependencies relocated to the new nodes from the two branch-pruned
   ones. The sk-thm-p1 realized statement and every realized step are untouched; this
   item realizes none of those fixed unit steps.
5. Compared the nodes with the Lean declarations and proof bodies. PASS: the parent
   changes only proof, proof_deps and proof_origin. Each new node has its declaration,
   source, natural-language steps, search records, provenance, blueprint ancestry,
   chapter and unit. Each proof_deps equals the union of its steps' uses; all cited
   nodes exist. The ordinary lemmas match the two applications in the parent, and
   the connecting node records the outstanding construction explicitly.

Changes made by the second reader: expanded the remaining theorem's docstring to
include degreewise exactness, the inverse-image cover and the evaluation-at-1
Ext/sections comparison already described in its DAG node; normalized its sorry
indentation and line widths; completed the parent's dependency-pruning inventory.
No proof term or declaration signature was changed.

## Second reading by D2

1. Compared every delivered module with the repository version. PASS: the original
   target statement, its docstring, and all existing declaration signatures are
   unchanged; the parent only replaces its proof and adjusts proof-only imports.
   The added declarations are recorded in their own modules and nodes.
2. Compiled all four modules in import order with `lcompile.py`. PASS: compilation
   succeeds without warnings; the sole remaining `sorry` is the named connecting-map
   theorem listed in this report. No forbidden declarations or hollow definitions
   occur. The proof declarations use only the permitted library axioms together with
   `sorryAx` from that explicitly open theorem.
3. Read the split-off statement and checked edge cases (empty opens, equal opens,
   identity morphism, and the one-open cover). PASS: it asserts only exactness,
   initial injections, and the connecting square, and is strictly smaller than the
   parent target. Searches found no existing declaration duplicating it.
4. Read the proof downward and checked imports and pruning. PASS: the ordinary
   restriction squares use composition/coherence and additivity, while the connecting
   construction is isolated in the split-off theorem. Proof-only imports are plain
   imports, public imports serve statement dependencies, and the parent DAG records
   the dependencies actually used. The unit realization is unchanged.
5. Compared all DAG nodes with the Lean declarations and proof bodies. PASS: proof,
   proof_deps, proof_origin, split metadata, and module paths agree; each new node has
   the required source, search, blueprint, chapter, and unit fields.

No repair was necessary in the second reading. The required dry-run and final
delivery checks are the remaining mechanical validations.
