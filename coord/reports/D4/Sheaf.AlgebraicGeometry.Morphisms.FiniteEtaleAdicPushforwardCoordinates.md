## What changed

Removed the first worker's new pointwise theorem
`pushforward_coordinates_transition_at`: it was equivalent to the original hole,
not a strictly smaller intermediate result. Its new node was also removed.

Proved the unchanged `pushforward_coordinates_transition_fun` by the original
three-step route: affine base-change bijectivity, transport of the unique inverse
section along the transition, and naturality of finite free coordinates. The
pointwise corollary remains unchanged. All existing definitions and declaration
signatures are byte-for-byte unchanged. Added five plain, proof-only imports to
the item; no existing public import was changed.

Added three separate statement modules under AlgebraicGeometry/Modules:
`CanonicalStructureBaseChangeIsIso` (proved),
`StructureBaseChangeSectionsNaturality` (open), and
`PullbackFreeCoordinatesNaturality` (open). The isomorphism proof is reused from
an existing private helper in `FiniteEtaleAdicSectionsKernel`: importing that
module would create a cycle, and its private declaration cannot be called.
The public helper uses the existing affine base-change and tensor structure-sheaf
results; it does not repeat those results or add a new inverse construction.

Added `PullbackSectionFactorization`, a real construction of the canonical section
transport through a factorization. Its irreducible body avoids expensive matching
of the concrete pullback/sheafification expressions. Both naturality statements
and the main proof use this same constructed map. This removes the normalization
problem without changing any existing definition or splitting a slow proof file.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.FiniteEtale.Adic.pushforward_coordinates_transition_fun`.
The previously proved `pushforward_coordinates_transition` remains proved.

New proved helper:
`AlgebraicGeometry.Scheme.Modules.canonical_structure_baseChange_isIso`
(node `new-sbc-canonical-structure-base-change-isIso`).

New holes added, each in its own module with a source and full mathematical proof:

- `AlgebraicGeometry.Scheme.Modules.structure_baseChange_sections_naturality`
  (node `new-sbc-structure-base-change-sections-naturality`).
- `AlgebraicGeometry.Scheme.Modules.pullback_free_coordinates_naturality`
  (node `new-sbc-pullback-free-coordinates-naturality`).

This is a decomposition, not a completed proof of the coordinate result:
one original hole closed and two strictly separate lower holes added (net -1).
The first lower statement involves neither coordinates nor inverses; the second
involves neither a cover nor a base-change comparison nor inverses. Bijectivity
and uniqueness of the inverse connect them in the actual Lean proof.
No sorry remains in the item's module or in a definition.

## No longer needed

No imports or reachable modules pruned. The rejected new pointwise node was
never in the repository and is omitted from this delivery.

The old direct proof dependency of the core node,
`new-sbc-finite-etale-adic-pushforward-coordinates`, is no longer used by its
proof. This removes the old core/pointwise DAG cycle. The pointwise node's old
proof dependencies `lem-weil-pbc-affine-pushforward-base-change-isIso` and
`lem-weil-pbc-module-pullback-structure-sheaf` are now used transitively through
the core and canonical comparison helper, rather than directly by its congrFun
proof. These two modules remain needed.

## Where the brief, the DAG or earlier work was wrong

The first worker's pointwise split is equivalent to the bundled equality by
funext/congrFun, and its node cited the core result that would cite it back.
Its docstring also lacked a complete natural-language proof, and its node's
initial Lean record was not a verbatim signature. It could not be delivered
as progress. The original repository also had a core/pointwise DAG cycle,
which the corrected proof records remove.

Lean requires registering `P.property : IsFinite P.obj.hom` locally to obtain
affineness. The upstream `pullbackCompOfEq` and `pullbackΓ` declarations live
in `AlgebraicGeometry`, rather than its `Scheme.Modules` namespace.
The generic comparison proof uses existing upstream proof text, not a new
arbitrary existence witness. All new existence choices occur inside a proof; liftSection
remains the original invFun definition, whose value is justified by bijectivity.

The delivery preflight does not recognize declarations introduced with the
irreducible_def macro. The transport is therefore written with an ordinary def
and the standard irreducible attribute, which preserves its construction and
normalization behavior and makes the declaration visible to the delivery parser.

## New nodes

`new-sbc-canonical-structure-base-change-isIso`: identifies the canonical
adjoint of structure restriction with the affine tensor base-change comparison;
proved using the existing two planned dependencies.

`new-sbc-structure-base-change-sections-naturality`: the comparison commutes
with a map of commuting squares; no finite etale, invertibility, coordinates,
or inverse hypothesis occurs. Its proof is adjunction coherence followed by
evaluation on sections.

`new-sbc-pullback-free-coordinates-naturality`: coordinate projections of an
arbitrary module map into finite free commute with pullback through a
factorization. Its proof is tensor associativity and functoriality, independent
of the affine comparison.

Searches were rerun through msearch.py for all three generic statements:
LeanFinder, grep, and LeanSearch (unavailable, recorded without a verdict).
LeanFinder returned relevant pullback/free/adjunction API but no complete
matching theorem. Repository searches found the private canonical comparison
proof described above and no existing complete naturality statements.
`def-sbc-pullback-section-factorization`: the pullback adjunction unit on global
sections followed by the existing composition comparison; no sorry or arbitrary
existence witness enters this function. Its three searches find the existing
component maps, rather than a packaged transport map.

No statement-change record is needed because every existing interface is preserved.

## Second reading by D4

1. Compared the delivered item with the repository by diff. Existing signatures,
   hypotheses, universes, visibility and the four definitions are unchanged.
   The first worker had added only the equivalent pointwise hole, which is removed.
   New statements are in separate modules, and proof-only imports are plain imports.
2. Reviewed the actual reduction and the reused canonical comparison proof.
   Bijectivity supplies a section with the prescribed image, naturality identifies
   the image of its transported section, and leftInverse_invFun with injectivity
   identifies both sections with the original liftSection constructions.
   Neither new hole is merely the original result under another name. No axiom,
   unsafe, opaque, implemented_by, extern, or data sorry is present.
3. Checked both split statements against their tensor/adjunction arguments and
   small cases. The coordinate statement has no index at rank zero; the zero
   module gives zero coordinates; identity transitions give the identity
   comparison; zero rings and empty schemes still have the same canonical maps.
   The structure comparison statement requires only commuting squares: the
   naturality of the adjoint exists without cartesianness or invertibility.
   Every new statement has a matching node, source and complete docstring proof.
   The searches and the inaccessible private existing proof are recorded above.
4. Kept the three-step route of the original coordinate node. No unit statement
   or realized unit step is bypassed: sk-prop-input-spreading's realized records
   are unchanged. Pruning is reported above. Each import is used in a signature,
   construction, instance inference, or the proof; no proof-only import is public.
5. Updated both existing nodes to match the actual proofs and remove the cycle.
   The four new nodes contain their complete verbatim Lean signatures, sources,
   proof steps, dependencies, search records, creation metadata and the same
   chapter/unit ancestry. The isomorphism node records its two actual dependencies;
   the two new naturality holes record their categorical/tensor proofs and their
   constructed transport dependency. The definition node contains its real body
   and no postponed proof or existence witness.

Changes made in the second reading: replaced the equivalent pointwise restatement
with the genuine reduction and its generic modules, reused and exposed the
existing private comparison proof, repaired instance inference and namespace usage,
and corrected the node routes and progress accounting. Comparison maps and
sections are kept abstract inside the proof to avoid expensive unfolding of the
concrete sheaf and inverse constructions; no data definition is changed.

Validation: all five delivered modules compile cleanly through lcompile.py;
the main file compiled in 9.5 seconds. The constructed section transport has no
sorry and the item contains no sorry. A scratch copy with #print axioms checked all existing definitions and the two
existing theorems, all new declarations, and the transport construction. Definitions
and the canonical comparison theorem use only propext, Classical.choice and
Quot.sound. The two split holes and their dependent coordinate theorems additionally
use sorryAx; no other axiom occurs. The scratch probe was removed before delivery.

The delivery dry run passed with review class CODEX (new modules and nodes),
including the compiler and declaration/axiom probes. Source constructions were
checked against [Stacks Tag 02KG](https://stacks.math.columbia.edu/tag/02KG) and
[Tag 01CA](https://stacks.math.columbia.edu/tag/01CA). The free-module definition
dependency is omitted from the two new comparison nodes because neither uses it.
