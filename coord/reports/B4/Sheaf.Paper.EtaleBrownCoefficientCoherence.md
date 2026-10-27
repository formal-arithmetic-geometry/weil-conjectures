## What changed

The statement and public imports of `Sheaf.Paper.EtaleBrownCoefficientCoherence`
are unchanged. Its proof now transports inverse-image scalar coherence through the
proper and open adjunctions and pastes the resulting compact-support projections.
The private lemmas `mate_unit_iff` and `mate_comp_iff` prove the required transport
in both directions using Mathlib mates, whiskering and cancellation. The private
`inverse_square_iff` handles inversion of the coherence squares, and
`projection_hom` unfolds only the recorded factorization of the Brown projection.
The proof uses `properMate`, `openMate` and `projection_def` of the existing Brown
construction; it does not change their definitions or assume their conclusions.

Added proof imports are `Sheaf.Paper.StrictEtaleInverseTensorCoherence` and
`Mathlib.CategoryTheory.Adjunction.Mates`. The short generic whiskering
calculation from the private helper of `ExactScalarMatePasting` is proved locally;
importing that whole derived-localization file solely for this calculation was
unnecessary. The new inverse-image theorem
is applied separately to the proper inverse image and the open inverse image.
Both unit and composition equations for each factor are then derived in Lean,
and naturality of the proper projection supplies the final interchange.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.etaleBrownCoefficientCoherence`
(`lem-pur-etale-brown-coefficient-coherence`). Its signature is unchanged.
The item contains zero remaining `sorry`s. The five private helpers are proved.

Added one hole:
`AlgebraicGeometry.strictEtaleInverseTensorCoherence`
(`lem-pur-strict-etale-inverse-tensor-coherence`), in its own new module.
Thus this delivery is a decomposition: one hole closed, one added, net zero.
The new obligation concerns inverse-image tensor comparison alone. It has no
compactification, compact-support functor, open extension, proper direct image,
Brown construction, or Brown projection. The substantial mate transport and
pasting needed to pass from it to the original conclusion are proved here.
The same new statement is needed twice, for the two different geometric factors.

## No longer needed

No original import was removed: the original public import
`Sheaf.Paper.EtaleSystemBrownConstruction` remains necessary for the statement.
No module is withdrawn and no declaration of the source library is changed.

The original direct proof-dependency route through
`def-pur-etale-brown-projection-realization`
(`Sheaf.Paper.EtaleBrownProjectionRealization`),
`lem-pur-sheaf-ring-derived-coefficient-adjunction`
(`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`), and
`lem-pur-etale-system-coefficient-projection`
(`Sheaf.Paper.EtaleSystemCoefficientProjection`) is not used by this item's
proof. The recorded mate equations give a shorter formal route without cancelling
realization equivalences. These nodes are removed only from this item's direct
proof dependencies; they may remain needed by the Brown construction or other
parents, and this delivery does not claim to prune their modules globally.
The new inverse-image obligation still uses the scalar adjunction in its own
ordinary insertion proof, so that dependency is retained there.

The generic mate-pasting dependency remains, as does the Brown-construction
node. The temporary import `Sheaf.CategoryTheory.ExactScalarMatePasting` was
removed after profiling: only its short generic whiskering proof was needed, and
that proof is now local. Its derived-localization statement is not used, so
`lem-weil-pbc-exact-scalar-mate-pasting` is not a proof dependency of this item.

## Where the brief, the DAG or earlier work was wrong

The original plan's fixed-ring realization cancellation is unnecessary for the
formal coefficient-coherence calculation: the Brown construction already records
the exact mate equations for the proper and open factors. The missing geometric
calculation can be isolated at inverse image before either adjunction is mated.
This is a change of proof route, not a statement repair.

`RingedCoefficientPullbackCoherence` already proves the analogous left-functor
calculation for a normalization over all ring sheaves. Its data are not directly
the selected quotient-level packages used here: the constants identifications,
chosen derived models and their computation comparisons still require transport.
The new theorem makes precisely that remaining selected-model coherence explicit;
it does not silently identify independently chosen units or associators.
Identity maps, repeated indices, zero coefficient rings and nonflat quotient maps
are retained. The ordinary insertion proof and K-flat resolution argument in its
docstring handle these cases without finiteness or boundedness assumptions.
The unit record `sk-def-sf-operations` is unchanged.

## New nodes

`lem-pur-strict-etale-inverse-tensor-coherence`, implemented by
`Sheaf.Paper.StrictEtaleInverseTensorCoherence`, states the normalized
inverse-image comparison's unit and composition equations. Its source is Zheng,
Construction 4.1 and Lemma 5.16, with the K-flat representative argument of Stacks
Tag 0D6D. Its docstring and node describe ordinary insertion, derived representative
transport and naturality on arbitrary unbounded inputs. It is a strictly earlier
part of the original argument, not the Brown projection conclusion with renamed
data. No change record is needed because no existing signature or definition was
changed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
