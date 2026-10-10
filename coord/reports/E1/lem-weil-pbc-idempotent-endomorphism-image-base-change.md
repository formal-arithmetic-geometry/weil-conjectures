# Delivery report: lem-weil-pbc-idempotent-endomorphism-image-base-change

## Changes

Split the existing node into three proof steps. The first computes the internal direct sum `R^n = Im(p) (+) Im(1-p)` and identifies `Im(1-p)` with `ker p`, giving finite projectivity of `Im(p)`. The second tensors the split decomposition with `S` and uses the public module base-change universal-property node to identify the canonical map. The third checks that the base-changed matrix is `rho(X)`, that its image is the first summand, and concludes the injective image/base-change isomorphism.

## Sources

The route follows More on Algebra, Lemma Tag 07M5 (lemma-lift-projective-module), line 2020 and its projector construction. The source leaves the final image calculation implicit; the elementary direct-sum and matrix arguments are written out in the proof steps. No new DAG nodes were needed and no Lean was written or compiled.

## Review by E1

I checked the three proof steps against More on Algebra Tag 07M5 and the cited public module base-change universal-property node. The projector identities give the direct-sum decomposition and finite projectivity; tensoring preserves that split and identifies the canonical map; and the matrix calculation identifies the image after base change. All reusable facts are imported public nodes, the parent remains the existing item with its original metadata, and the report contains no Lean changes.
