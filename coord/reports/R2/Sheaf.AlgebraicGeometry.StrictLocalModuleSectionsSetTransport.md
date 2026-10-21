## What changed

Retire Sheaf.AlgebraicGeometry.StrictLocalModuleSectionsSetTransport, the listed
zero-hole duplicate of the adopted source module. Both DAG attachments now point
at WeilConjectures.AlgebraicGeometry.StrictLocalModuleSectionsSetTransport.

Preserve the sole direct consumer QcqsStrictLocalRestrictionBijective's complete
public signature. Its proof uses the new proved exists_moduleSectionsIsoTransport
for arbitrary schemes and an isomorphism over their base. Specializing to pullback
symmetry yields precisely the small-model representative formula it already needs.
The consumer imports the generic compatibility module. The adopted fixed-presentation
result is not a needed proof dependency on this route; its declarations are retained
verbatim and both original DAG attachments point to them.
No source-library declaration, target, surviving public definition, or consumer
statement changes. The generic lemma constructs its equivalence from concrete
comparison isomorphisms; an existential witness is used only inside a theorem proof.

Validation: the generic module compiles in 22.2 seconds and the final consumer
compiles in 8.4 seconds through lcompile.py. The public consumer signature was
compared with the original and is identical. Supplying the etale object explicitly
at the general formula application avoids expensive implicit elaboration; no
heartbeat or single-file time limit was raised. The required deliver3 command
performs the final compilation, axiom probes, and preflight checks.

Change record: coord/changes/R2-strict-local-module-section-transport-retirement.md.

## Proved and sorry left

Assigned retirement: zero original holes, zero holes closed, zero holes added,
zero split-off holes. No delivered Lean declaration contains sorry.
The new AlgebraicGeometry.Etale.exists_moduleSectionsIsoTransport and its two
private naturality helpers are fully proved. The existing consumer remains proved.
This is a retirement and compatibility repair, not a claim to have closed a hole.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/StrictLocalModuleSectionsSetTransport.lean
and remove its sole direct import from QcqsStrictLocalRestrictionBijective.
The duplicate public strictLocalModuleSectionsSetEquiv and
strictLocalModuleSections_set_transport are replaced by the existing adopted
source declarations. Their nodes stay attached to those declarations.
The small-model bijectivity proof no longer uses either fixed strict-local
transport node; its node now cites the general module-sections isomorphism
transport and the already existing small-model maps. All coefficient, composition,
restriction, fibre-product, continuity, and stalk dependencies remain necessary.
No unit statement or unit proof step is bypassed. No upstream module is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes holes, but the queue assigns retirement of an
already proved module. Identical names in the two copies mask genuinely different
strict-local scheme presentations. Their APIs cannot be swapped definitionally.
The new theorem separates the formal coefficient/isomorphism argument from any
choice of strict-localization presentation and preserves the consumer statement.
The original DAG naturality plan is valid and supplies the proof of the generic
compatibility theorem. No mathematical statement is disputed.

## New nodes

lem-weil-pbc-module-sections-iso-transport records the fully proved general
isomorphism transport theorem in Sheaf.AlgebraicGeometry.ModuleSectionsIsoTransport.
It needs no geometric point, localization, qcqs or nonzero-coefficient assumption.
Its concrete equivalence and unit identities use the existing coefficient,
composition and restriction APIs. Source: Stacks 03D3/03D7 and the degree-zero
calculation in 03Q9, generalized by the explicit formal argument. Searches found
the adjunction unit identity but no existing general transport theorem. Empty
schemes, identity isomorphisms and zero coefficients require no exceptional cases.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
