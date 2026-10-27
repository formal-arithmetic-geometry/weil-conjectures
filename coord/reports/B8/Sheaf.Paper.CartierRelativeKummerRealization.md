## What changed

Filled relativeCartierRootZero, relativeCartierRoots_realization,
and relativeCartierTwist_realization from existing library
interfaces. The root zero relation is ZMod.natCast_self under ULift; finite_etale_torsion_twist_line
gives flatness. The proved residueLineData helper, imported privately from
P1KummerScalarEndpointExistence, supplies the normalized scalar unit on the empty Cartier
divisor. The universal property yields the compatible isomorphism to any other derived
representative. Positive-level induction identifies the positive coefficient branch. The existing
unique root-comparison theorem gives the specified twist comparison.

The Cartier Ext definition and root-normalization predicate now use direct successor matches
with the identical chosen classes and predicates. See coord/changes/B8-relative-cartier-presentation.md.
All retained declaration signatures and public imports are unchanged. No source-library module
is changed. Local irreducibility attributes avoid eager expansion of derived-category
and supported-Hom aliases. PurityFiniteSetting is unchanged. No new public declaration, module, or node is added.

## Proved and sorry left

Three original holes proved:
- WeilConjectures.PurityFiniteSetting.relativeCartierRootZero
- WeilConjectures.PurityFiniteSetting.relativeCartierRoots_realization
- WeilConjectures.PurityFiniteSetting.relativeCartierTwist_realization

One original hole remains:
- WeilConjectures.PurityFiniteSetting.relativeCartierKummer_realization

The unused relativeCartierProExt_type presentation theorem and its original hole
are pruned. The direct Ext definition no longer uses a whole-type equality transport.
Zero holes added; zero split off. This is a partial delivery. The remaining theorem's
source, full proof in words and DAG attachment are retained. Candidate full proofs exposed
costly kernel conversions; they are preserved only in the sandbox scratchpad, not delivered.

## No longer needed

relativeCartierProExt_type is no longer needed by any declaration and is removed,
with its Lean attachment updated. The chosen Cartier Ext class is retained.

Removed direct proof imports BoundedAboveFlatSheafKFlat, DerivedChangeOfRingsCochainModel,
FiniteRootSiteComparison, AmbTateRootProjectionReduction, SupportedCartierBoundaryExistence,
CartierKummerDescent and PurTwistSheafLocallyFree. Existing residue scalar-unit and unique
root-comparison results provide the needed conclusions. They may retain these nodes
transitively, so no module or upstream declaration is withdrawn.

For the completed geometric clauses, the direct lower-level construction nodes
lem-pc-bounded-above-flat-kflat-site, lem-pur-derived-change-of-rings,
lem-amb-finite-root-site-comparison, lem-amb-tate-root-projection-reduction,
lem-asd-cartier-boundary-existence and lem-pur-twist-sheaf-locally-free are unnecessary.
The final theorem still retains its planned boundary, Cartier, supported-source and
class-agreement dependencies.

## Where the brief, the DAG or earlier work was wrong

The existing scalar-unit and root-comparison interfaces already contain the data needed
for the root and twist clauses. Reconstructing their lower-level complexes is unnecessary.
The final derived-arrow assembly remains unfinished in this delivery. No mathematical
statement is disputed, and the blueprint unit route is preserved.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
