## What changed

Filled the eight proof holes in WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic.
The complete proofs were already present in the shared repository when this worker started;
the shared source refreshed to an eight-hole version during the first dry run. The delivery
reuses those existing library proofs, as required by the shortest-route rule, while preserving
the refreshed coefficient morphism definitions and signatures. No coefficient API repair or
change to its data is included.

The finite-limit proof constructs the adjunction from connected components of affine spectra
using the existing locally constant ring Hom correspondence. Cover preservation uses joint
surjectivity and the explicit product description of the prime spectrum. The monoidal
comparison uses the conjugate of the monoidal pushforward comparison. The other instances
specialize existing library instances. Five proof-only imports support these arguments.

## Proved and sorry left

Holes closed: 8 of 8. Holes added: 0. Split off: 0.

- `AddCommGrpCat.hasFunctorialFlatResolution`: proved.
- `AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`: proved.
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt`: proved.
- `AlgebraicGeometry.ProEtale.coverPreserving_profiniteToProEt`: proved.
- `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_profiniteToProEt`: proved.
- `AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar`: proved.
- `AlgebraicGeometry.ProEtale.isIso_δ_pointUpperStar`: proved.
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp`: proved.

No remaining `sorry` in the item or added elsewhere.

## No longer needed

No original import or library module is withdrawn. All five new proof imports are needed.
Removing Sites.PushforwardMonoidal was tested and causes instance synthesis for the
monoidal direct-image comparison to fail, so the import was retained. The existing public
imports preserve the statement and definition API.

The following dependencies are no longer used by the indicated node proofs; this is local
DAG pruning, not a claim that the modules are globally unreachable:

- `lem-sfb-lc-weakly-etale`: `def-weil-etale-morphism`, `def-weil-pbc-category-colimit`, `def-weil-weakly-etale-morphism`, `lem-weil-pbc-etale-algebra-finite-product`, `lem-weil-pbc-etale-ring-map-iff-etale-affine`, `lem-weil-pbc-ind-etale-stability`.
- `lem-sfb-point-upper-star-tensor`: `def-sfb-point-adjunction`, `def-sfb-point-lower-star`, `def-sfb-profinite-to-proetale`, `def-weil-pbc-sheafification`, `def-weil-pbc-sites-and-cohomology`, `def-weil-size-convention`, `lem-sfb-profinite-to-proetale-cover-preserving`, `lem-sfb-site-inverse-image-bilinear-adjunction`, `lem-weil-pbc-left-exact-site-inverse-image-tensor`, `sk-def-sfb-condensed-ring`, `sk-def-sfb-sheaf-tensor`.
- `lem-sfb-point-upper-star-unit`: `sk-def-sfb-sheaf-tensor`, `def-weil-pbc-sheafification`, `def-sfb-point-lower-star`, `def-sfb-point-adjunction`, `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`, `lem-weil-pbc-presheaf-pullback-left-exact`, `lem-weil-pbc-colimit-constant-connected-diagram`.
- `lem-sfb-profinite-to-proetale-cover-preserving`: `def-sfb-profinite-to-proetale`, `def-weil-affine-spectrum`, `lem-weil-pbc-morphism-affine-schemes-affine`, `sk-def-sfb-condensed-ring`, `sk-lem-pe-weakly-etale-stability`.
- `lem-sfb-profinite-to-proetale-finite-limits`: `def-weil-pbc-category-colimit`, `def-weil-pbc-small-proetale-site`, `lem-sfb-finite-quotient-fiber-product`, `lem-weil-pbc-algebra-tensor-pushout-universal-property`, `lem-weil-pbc-directed-limit-compact-hausdorff-nonempty`, `lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-finite-limits-from-terminal-pullbacks`, `lem-weil-pbc-profinite-limit-function-factorization`.
- `lem-sfb-pullback-from-point-comp-monoidal`: `def-sfb-finite-upper-lower-star-adjunction`, `sk-def-sfb-sheaf-tensor`.

The obsolete tool-use approvals for `lem-weil-pbc-ind-etale-stability` on
`lem-sfb-lc-weakly-etale` and `lem-weil-pbc-left-exact-site-inverse-image-tensor` on
`lem-sfb-point-upper-star-tensor` are withdrawn. The finite-limit proof uses the existing
Hom equivalence, and the unit/tensor proofs specialize the closed generic source instances.

## Where the brief, the DAG or earlier work was wrong

The shared source changed during initial inspection: the first snapshot had all eight holes
filled (the earlier F2 proof), and the refreshed delivery baseline had all eight open again.
The initial zero-hole diagnosis applies only to that first snapshot. This delivery restores
just the mathematical proofs against the refreshed baseline. It does not restore the unrelated
choice-backed coefficient API from the first snapshot.

## New nodes

`lem-sfb-locally-constant-ring-weakly-etale` records the already proved
`LocallyConstant.weaklyEtale` from
`WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`. The statement explicitly includes
both flatness conditions and allows the empty space and zero ring. It introduces no Lean
statement, module or hole.

`lem-sfb-general-sheaf-pullback-monoidal-comparisons` records the already proved generic
`isIso_η_sheafPullback` and `isIso_δ_sheafPullback` instances from
`WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`. It states the precise connected/sifted
comma-category and tensor-colimit hypotheses, with the comparisons taken from the canonical
adjunction. It introduces no Lean statement, module or hole. These generic tools preserve
all steps of the pulling-back-from-the-point unit, now discharged by existing library proofs.

Change record: `coord/changes/D3-basic-coefficient-site-proofs.md` lists all 304 consumers
including the item and the unchanged proposition-valued instance signatures. No consumer
adaptation is needed. The six existing node copies have proof routes matching the Lean.

## Second reading by D3

1. Compared the delivered module with the shared repository version. Existing declaration
   signatures are unchanged byte for byte; only proof bodies, proof-only imports, and private
   helpers were added. Verdict: pass.

2. Compiled `Basic.lean` with `lcompile.py`; it succeeds with no errors or warnings. Searched
   for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, and
   `debug.skipKernelTC`; none occur. The eight listed holes are closed and no holes were added.
   Verdict: pass.

3. Checked the split-off node records and searched the library for duplicate declarations.
   The two generic-tool records and the locally constant weak-etale record refer to existing
   declarations and introduce no new Lean holes. Their statements are true and are used only as
   proof dependencies. Verdict: pass.

4. Checked the proofs from the top down. The finite-limit, cover, adjunction, unit/tensor, and
   monoidality arguments use existing library results and preserve the unit route. The five
   added imports are proof-only and needed; no public import was removed. Verdict: pass.

5. Compared each edited node's `proof`, `proof_deps`, and `proof_origin` with the Lean proof and
   checked the unit-route dependencies. The records agree with the implemented route; obsolete
   dependencies are listed above. Verdict: pass.

Changed after this reading: added this review record only; no Lean declarations or DAG routes
required repair.
