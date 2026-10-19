## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteAfterBlowup` states
`AlgebraicGeometry.finiteLocallyFree_after_admissibleBlowup`. It uses the scheme
universe `u`, a scheme `S`, a scheme `X`, a morphism `f : X ⟶ S`, and an open
`U : S.Opens`. The instances `[CompactSpace S]`, `[QuasiSeparatedSpace S]`, and
`[CompactSpace U.toScheme]` render the quasi-compact and quasi-separated base and
quasi-compact open hypotheses. `[IsProper f]` renders properness. The hypothesis
`[Scheme.Hom.IsFiniteLocallyFree (Limits.pullback.snd f U.ι)]` is exactly finite
locally freeness of the restriction over `U`. The conclusion
`∃ B : IsAdmissible S U, Scheme.Hom.IsFiniteLocallyFree
(strictTransformMap f B.I.blowupMap B.I.support.compl)` supplies a U-admissible
blow-up and says its canonical strict-transform morphism is finite locally free.
The source proof route is recorded in the declaration docstring: boundary blow-up,
flattening, proper-flat finiteness over a dense open, and composition of blow-ups.
The theorem proof is intentionally `sorry` for stage 2.

Dependencies used are `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
(`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`),
`WeilConjectures.Blowup.AdmissibleBlowup`
(`AlgebraicGeometry.IsAdmissible`), and
`WeilConjectures.Compactification.StrictTransform`
(`AlgebraicGeometry.strictTransformMap`). The recorded dependency declarations
for quasi-compactness, properness, open immersions, quasi-separatedness, admissible
blow-ups, strict transforms, and finite locally free morphisms were read; the latter
four project notions are represented by the recorded upstream declarations and the
former notions by their Mathlib declarations.

Edge cases checked: `U = ⊤` permits the identity admissible blow-up; empty `U` is
not excluded by the statement; disconnected bases and varying finite locally free
ranks are allowed; nilpotents are retained because the upstream strict transform is
scheme-theoretic; no noetherian, integral, characteristic, or nonempty assumptions
were added. The pullback restriction uses `U.ι`, so its source and target are exactly
the base-change schemes in the node.

Searches made with `msearch.py Q49 lem-trf-finite-after-blowup`: LeanFinder query
“ A proper morphism finite locally free over a quasi-compact open admits an admissible
blow-up whose strict transform is finite locally free ” returned only generic
`IsFinite`, `IsProper`, and locally-finite-type declarations (no match). Loogle
query `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree,
AlgebraicGeometry.IsAdmissible, AlgebraicGeometry.strictTransformMap` returned zero
hits (the qualified project class is not in Loogle's index). Grep query
`strictTransform.*IsFiniteLocallyFree` over `AlgebraicGeometry` returned no hits.
I also searched the project and source checkouts by the item id and theorem name;
there was no existing declaration. The exact upstream definitions were read in
`WeilConjectures/AlgebraicGeometry/Morphisms/FiberDegree.lean`,
`WeilConjectures/Blowup/AdmissibleBlowup.lean`, and
`WeilConjectures/Compactification/StrictTransform.lean`.

No new nodes or dependency modules are needed. No statement correction or
`STATEMENT-DISPUTED` flag is present.

## Second reading by Q49

I reread the node and module independently. Every node hypothesis is represented by
one corresponding explicit binder or instance, and the conclusion has exactly the
admissible blow-up witness and finite-locally-free strict transform. The open is
represented by `U : S.Opens`, its quasi-compactness by `CompactSpace U.toScheme`,
and the restricted morphism by `Limits.pullback.snd f U.ι`; no extra hypotheses or
special cases occur. The declaration name is new in both the side project and the
upstream source. The file compiled cleanly with `scompile.py`; the only postponed
proof is the expected `sorry`.
