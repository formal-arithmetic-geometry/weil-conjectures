# AlgebraicGeometry.Scheme.Hom.purityNormalProjection

## Reason

Break a dependency cycle so PurityNormalCone can use the already proved stronger
reesConeComparison_exists theorem. That theorem needs the canonical projection but
not either comparison theorem in PurityNormalCone. Move the projection, its kernel
lemma and its retraction identity to Sheaf.Paper.PurityNormalProjection. All three
names and signatures, and the projection's defining term, remain identical.
PurityNormalCone publicly reexports the foundation, preserving its old API.
No target statement or mathematical definition changes.

ReesConeNormalization now publicly imports the projection foundation and the
unchanged PurityNormalBundle directly. ConormalConeHomExt imports only
PurityNormalBundle, whose cone and algebra objects are all it uses. Both adapted
modules were unclaimed when checked. No WeilConjectures source module changes.
The unchanged regular-immersion proofs are not split or moved.

An initial delivery check timed out when rebuilding ReesConeNormalizedExistence,
a module that had previously compiled in 54 seconds. Profiling showed costly
rewriting through the chosen affine equivalence and definitional comparison of
glued isomorphisms. Its two private isomorphisms are now marked irreducible after
their representative/chart API lemmas. The representative calculation composes
equalities with congrArg instead of rewriting a large expression. Broad simplification in the affine naturality calculation is restricted to the
three equations it uses. These are
proof-performance changes in an unclaimed module; no public attribute changes.

## Old

Declared in Sheaf.Paper.PurityNormalCone:

```lean
noncomputable def purityNormalProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : i.ker.normalCone ⟶ Z :=
  IsClosedImmersion.lift i
    (relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase
    (purityNormalCone_kernel i)
```

## New

Declared verbatim in Sheaf.Paper.PurityNormalProjection, publicly reexported by
Sheaf.Paper.PurityNormalCone:

```lean
noncomputable def purityNormalProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : i.ker.normalCone ⟶ Z :=
  IsClosedImmersion.lift i
    (relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase
    (purityNormalCone_kernel i)
```

The statements of purityNormalCone_kernel and purityNormalProjection_eq are also
unchanged; their sorry proofs are replaced by the quotient-spectrum factorization
and the retraction calculation respectively.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurityNormalCone | H3 | Reexports the unchanged foundation; proves both comparisons. |
| Sheaf.Paper.PurityNormalProjection | H3 (new foundation) | Houses the three unchanged declarations. |
| Sheaf.AlgebraicGeometry.ReesConeNormalization | unclaimed | Replaces its public cone import with the two precise foundations; coneAlgebraIso gains a trailing `eqToIso` whose proof is `rfl` on the live library (see below). Signature unchanged. |
| Sheaf.AlgebraicGeometry.ConormalConeHomExt | unclaimed | Replaces its public cone import with the bundle construction it uses. |
| Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback | unclaimed | Signatures unchanged; the two private relative-spectrum lemmas try the live `rfl` proofs first and fall back to the chosen-equivalence equations (reviewer fix, see below). |
| Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence | unclaimed | Private isomorphisms become irreducible after their API lemmas; congrArg replaces an expensive rewrite. Public signatures and route unchanged. |
| Sheaf.Paper.FiniteSmoothCanonicalInterfaces | unclaimed | Unchanged; existing cone import reexports every old name. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Unchanged; retraction identity and comparisons retain their signatures. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged transitive consumer; no statement or definition changes. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed (quarantined) | Unchanged; DiagonalNormalized uses purityNormalProjection in its projection-compatibility condition. The same declaration and defining term remain publicly available through the existing imports. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed (quarantined) | Unchanged; the diagonal cone comparison uses purityNormalProjection_eq with pullback.diagonal_fst. Its signature and public availability are preserved. |

Users were enumerated with tools/downstream.py on the three changed existing
modules and --uses purityNormalCone_kernel purityNormalProjection
purityNormalProjection_eq. No forced adaptations of another group's module occur.
The library-wide #print axioms checks are performed by deliver3.py.

Repair of the return for delivery head 90b838f72: the two quarantined consumers
above were missing from this table. Both are recorded in coord/rework.tsv and
their preserved sources were checked in quarantine/Sheaf/Paper/. Neither has a
current claim. AmbientDiagonalPurityBaseChange uses the projection in the
definition of DiagonalNormalized; FiniteSmoothAdjunctionGeneralBase applies the
retraction identity to the diagonal and first projection. The moved declarations
have identical signatures, and purityNormalProjection has the identical defining
term. PurityNormalCone publicly reexports their new module, so neither consumer
requires an adaptation. Their quarantined files and Lean attachments are retained.

The existing def-pur-normal-bundle attachment moves to the publicly reexporting
projection foundation, keeping all six regular-immersion steps. The existing
pur9-def-normal-cone attachment moves to PurityNormalCone, which reexports its
original construction and proves the two presentation comparisons. This prevents a
DAG dependency cycle as well as the Lean import cycle, without adding a node,
changing a node statement, or bypassing either blueprint unit.

## coneAlgebraIso and the relative-spectrum lemmas (reviewer fix, 2026-10-21)

The published build used by lcompile.py is stale for this chain: its
VectorBundleZeroSection.olean still defines `antiEquivalence` as the equivalence chosen
from `affine_morphism_relative_spec`, while live source defines it as
`(structureAlgebraFunctor S).asEquivalence`. Against that stale build the live
ReesConeNormalization (even with only the import swap) fails with a type mismatch in
coneAlgebraIso, and the two `rfl` proofs of ConormalConeZeroSectionPullback fail. The
delivered workaround (`eqToIso ((affine_morphism_relative_spec S).2.choose_spec.choose _)`
and `simpa … using choose_spec`) compiles only against the stale build: against the live
VectorBundleZeroSection source it fails (Application type mismatch,
ReesConeNormalization.lean:46).

The corrected files compile against both: coneAlgebraIso ends with
`eqToIso (by first | rfl | exact (affine_morphism_relative_spec S).2.choose_spec.choose _)`,
which on the live library is `eqToIso rfl`, definitionally the identity, so the definition
is definitionally unchanged; relativeSpec_obj / relativeSpec_map try their original live
proofs first. coneZeroSection_app keeps its live text. Once the published build is rebuilt
from live sources the fallback branches are dead and may be removed.

Users of coneAlgebraIso: ConormalConeZeroSectionPullback, ReesConeNormalizedExistence,
FiniteSmoothCanonicalInterfaces (all unclaimed); all compile, against both the published
build and a sandbox built from live VectorBundleZeroSection / PurityVectorBundleZeroSection /
PurityNormalBundle sources.

## Status

landed 20261020T230748-L-610064 2026-10-20 (merge of deliver/H3/Sheaf.Paper.PurityNormalCone)
