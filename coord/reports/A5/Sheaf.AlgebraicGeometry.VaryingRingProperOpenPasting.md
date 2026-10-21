## What changed

Replaced the last hole, `AlgebraicGeometry.ProEtale.VaryingRing.gamma_evaluation`,
with a complete combining proof. Its public statement is unchanged. No target,
existing data definition, or source-library declaration changes.

The proof constructs `AdjunctionEvaluation` directly from each specified pullback
comparison and its actual direct-image mate. The unit and counit equations follow
from the mate identities. Apply the existing `evaluation_mate` theorem to the
varying alpha and the strict-tower alpha, obtaining their common coefficient mate.
Naturality against `constantEval` and cancellation of `constantSource` identify
this mate with the already defined `constantGamma`.

The new factor module constructs the actual cartesian open factor and clopen
section factor of alpha, and proves both varying and strict factorizations.
`clopenArrowEvaluation` composes their two comparison equations; its proof is
complete. The cartesian-open comparison is now fully proved, including its
arbitrary-ring invertibility and its specified open-mate normalization. The clopen-section
comparison is the one retained source result. It contains no cartesian beta,
proper-adjunction mate, or gamma evaluation; it is the other genuine geometric
factor of the construction.

The item adds one private proof import. New modules use public imports only for
their statement and definition interfaces; the assembly's two geometric imports
are private. All original public imports remain verbatim. The unit route and
all earlier proved identity and pasting clauses remain intact.

## Proved and sorry left

Original holes closed: one, `AlgebraicGeometry.ProEtale.VaryingRing.gamma_evaluation`.
There are zero literal holes in the item, the open base-change comparison,
and the factorization and assembly modules. The added private adjunction helpers
and both factorization theorems have complete proofs.

New holes added: one, a public theorem in its own new module, with its source,
full proof in words, blueprint tag, and matching DAG node:

- `AlgebraicGeometry.ProEtale.VaryingRing.clopenSectionEvaluation`, in
  `Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation`, node
  `lem-sp-varying-ring-clopen-section-evaluation`.

The new `AlgebraicGeometry.ProEtale.VaryingRing.openBaseChangeEvaluation` is fully
proved, with no holes in its private helpers. Its proof localizes the proved
ordinary pullback-composition equation before taking components, applies open
mate interchange, and obtains invertibility from strict beta and the constant
derived embedding. It uses neither finite coefficients nor detection of derived
morphisms by evaluation.

This is a decomposition of one original hole into one strictly smaller geometric
source result, together with a completed proof of the other factor. It is not a
net closure of the full mathematical proof. The resulting `gamma_evaluation`
continues to depend on the clopen-section hole and existing imported holes; no
axiom-free claim is made for it. No holes occur in data definitions.

Edge cases were checked on the definitions: empty open and zero coefficient
ring give zero comparison equations; a cartesian proper/open square makes the
section lift an isomorphism; identity opens remove the cartesian beta factor.
The two factors have exactly the same typed intermediate functor, as checked by
the proved Lean factorization and assembly.

Validation: all five packet Lean files compiled cleanly through
`lcompile.py --all` (open comparison 12.1 s; item 26.1 s). The
unchanged direct consumer `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`
compiled against the sandbox library in 39 seconds and was then removed from the
packet. No nonzero, finite-ring, boundedness, or preservation-of-injectives
hypothesis is added.

## No longer needed

None. No existing imports, declarations, nodes, or modules are withdrawn. Every
previous direct proof dependency remains used by earlier clauses or by the
retained geometric route. The unit's own statement and coherence route stay.
Only scratch experiments are excluded; they are not library withdrawals.

## Where the brief, the DAG or earlier work was wrong

The final DAG step previously said evaluation preserved the constructed alpha
and immediately invoked mate evaluation. The generic `evaluation_mate` theorem
requires the actual alpha comparison equation as input; it does not establish
that geometric equation. The new nodes isolate its cartesian-lift and
clopen-section calculations, and the item now supplies the complete categorical
mate argument.

The existing ordinary-clopen theorem asserts the existence of coherent pullback
and open comparison witnesses for degree-zero realization. Its statement does
not identify those witnesses with the specific unit-normalized `evalG` and
`evalJ` appearing here. Its faithfulness applies to ordinary systems, not to
arbitrary derived morphisms. Consequently it cannot simply be applied as the
missing canonical derived comparison. No such inference is used.

The existing strict beta-evaluation theorem imposes finite coefficients. The
new open-comparison proof avoids that restriction: it first proves inverse-mate
compatibility, then uses the already proved arbitrary-ring strict beta
invertibility. Constant derived towers establish invertibility of the
single-coefficient mate on every object. It needs no newly landed single-level
API that is absent from the server's last green compiled library.

## New nodes

`def-sp-varying-ring-clopen-arrow-factors`: actual exact-localization and section
factor constructions, together with two proved alpha factorizations. No data are
chosen from an unproved existence theorem.

`lem-sp-varying-ring-open-base-change-evaluation`: coefficient realization of the
cartesian open base-change factor alone, with its arbitrary-ring unit transpose.
This node now has a complete Lean proof.

`lem-sp-varying-ring-clopen-section-evaluation`: coefficient realization of the
clopen image/zero projector and its outgoing composition identifications alone.

`lem-sp-varying-ring-clopen-arrow-evaluation`: proved composition of the preceding
two geometric equations, using the actual alpha factorizations.

The existing `lem-sp-varying-ring-proper-open-pasting` node keeps all earlier
steps and replaces only its final evaluation argument and corresponding proof
dependencies/origin. All new nodes retain its chapter, unit, and blueprint
ancestor. Change record: `coord/changes/A5-varying-ring-pasting-evaluation.md`.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
