## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleChartFiniteFibreTransfer` states
`AlgebraicGeometry.AlgebraicSpace.finite_preimage_singleton_of_etaleCover`, with
`by sorry` as its entire proof. No definition or further theorem is introduced.
The source was read in `literature/stacks-project/decent-spaces.tex`,
lemma-U-finite-above-x (Tag 03JS), specifically implication (1) to (2).
The node's statement and accepted proof split are unchanged. There is no
STATEMENT-DISPUTED flag, missing notion, or unusable dependency interface.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Scheme S | `{S : Scheme.{u}}` |
| Algebraic space X over S | `(X : AlgebraicSpace S)`; its underlying set-valued presheaf is `X.obj.obj` |
| Field-valued point class x | `(x : Point X.obj.obj)` |
| A set-indexed family of schemes over S | `{I : Type w}` and `(U : I → Over S)`; the schemes are `(U i).left` |
| Morphisms a_i from those schemes to X | `(a : ∀ i : I, yoneda.obj (U i) ⟶ X.obj.obj)` |
| Every a_i is representable étale | `(ha : ∀ i : I, IsEtale (a i))`; this existing predicate includes scheme-test representability |
| The union of their point images is all of X | `hcover : ∀ y : Point X.obj.obj, ∃ (i : I) (t : (U i).left), schemePointMap (a i) t = y` |
| Each inverse image of x is finite | `hfinite : ∀ i : I, (schemePointMap (a i) ⁻¹' {x}).Finite` |
| Every affine scheme V over S | `(V : Over S) [IsAffine V.left]` |
| Every representable étale map v from V to X | `(v : yoneda.obj V ⟶ X.obj.obj) (hv : IsEtale v)` |
| The inverse image of x under v is finite | `(schemePointMap v ⁻¹' {x}).Finite` |
| No affineness or quasi-compactness requirement on U_i | Neither property appears among the binders for U |
| Fibres over x may be empty | Set finiteness imposes no inhabitance or individual-surjectivity condition |
| No hypothesis on U_i ×_X U_i | No self-intersection objects or hypotheses occur in the signature |

The universal quantification over `V`, its affineness instance and `v` is the
node's “for every affine scheme and every representable étale morphism”. `Over S`
retains the structural maps to the given base; no atlas is selected and no
arbitrary function replaces the canonical residue-field point map. Universes
`u` and `w` and all variables are explicitly bound. `w` is independent: this is
a covering family, not a limit or filtered-colimit index.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `AlgebraicGeometry.Spec`, and `Spec.map`. These are the existing
  records for def-pc-scheme and def-weil-affine-spectrum. The theorem quantifies
  over arbitrary affine schemes using `AlgebraicGeometry.IsAffine`, whose
  canonical `Scheme.isoSpec` was read in `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicGeometry.AlgebraicSpace.IsEtale`, for def-trf-algebraic-space.
  `IsEtale` is `IsRepresentableWith` for the scheme predicate `Etale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, the recorded module of
  def-a1-space-point-topology, reexports the existing
  `AlgebraicGeometry.AlgebraicSpace.Point` and `schemePointMap` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`. Their complete definitions
  and docstrings were read: the point set is the quotient of field-valued
  representatives and the scheme point map uses the canonical residue-field map.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  the recorded scheme-étale predicate of def-weil-etale-morphism. The local
  ring-map signature was read. Representable étaleness uses precisely this predicate.

The remaining imports are the modules of stated proof dependencies, with ordinary
(non-public) imports as required for stage 3:

- def-pc-scheme-fibre: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber` and its projections.
- lem-trf-space-fibre-products-etale-covers:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`, including
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback` and
  `etale_fibreProduct_isScheme` in `AlgebraicGeometry.AlgebraicSpace`.
- lem-weil-pbc-affine-opens-basis: `Mathlib.AlgebraicGeometry.AffineScheme`,
  `AlgebraicGeometry.Scheme.isBasis_affineOpens` (already a public statement import).
- lem-weil-pbc-etale-morphism-open-map:
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`, `Scheme.Hom.isOpenMap`.
- lem-weil-pbc-finite-closed-map-finite-fibres:
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.UniversallyClosed`, and
  `.QuasiFinite`, supplying the finite-to-proper instance, `Scheme.Hom.isClosedMap`
  and `Scheme.Hom.finite_preimage_singleton`.
- lem-weil-pbc-lqf-qc-source-bounded-fibres:
  `WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite`,
  `Scheme.Hom.hasUniversallyBoundedFibers_of_isLocallyQuasiFinite`.
- lem-weil-pbc-lqf-restriction-to-opens:
  `WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`,
  `Scheme.Hom.isLocallyQuasiFinite_resLE`.
- lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact:
  `Mathlib.RingTheory.Spectrum.Prime.Topology`, including `PrimeSpectrum.compactSpace`.
- lem-weil-pbc-unramified-quasi-finite-at-points:
  `WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite`,
  `Scheme.Hom.isLocallyQuasiFinite_of_unramified`.

The theorem docstring carries all four proof steps, including the finite affine
open refinement, finite scheme fibres from quasi-compact source, and equality
of the desired fibre with the finite union of finite images. It does not assume
that the covering schemes or the projections are quasi-compact.

Edge cases checked before writing:

- Empty covering index: the given point x means the point-surjectivity
  hypothesis is impossible, as it should be; no `Nonempty I` hypothesis is added.
- Empty members or empty fibres contribute empty sets; no `Nonempty` assumption
  is present for a member or its fibre.
- The test affine chart may be empty, and v need not be surjective.
- Infinite index sets are allowed in any universe w. Compactness in the proof
  is applied only to the affine test chart, never to the covering members.
- Non-quasi-separated algebraic spaces and non-quasi-compact covering schemes
  are allowed; neither separation nor a self-intersection bound is assumed.
- No characteristic, base Noetherianity, algebraic closedness, or residue-field
  extension assumption occurs in the statement or was added.

Searches made with the prescribed `msearch.py` wrapper:

- LeanFinder: “For an algebraic space, finite point fibres in a jointly
  surjective etale covering imply finite point fibres in every affine etale
  chart”. Eight hits, including `IsFinite.finite_app`, the finite-fibre instance
  for scheme finite morphisms, and `isFinite_iff`; none is this transfer theorem.
- LeanSearch: “Finite point fibres in a jointly surjective etale scheme covering
  of an algebraic space imply finite fibres in every affine etale chart”. Eight
  hits, including `IsFinite.finite_preimage_singleton` and scheme jointly
  surjective precoverage results; no algebraic-space chart transfer.
- Loogle: `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton,
  AlgebraicGeometry.IsEtale` returned zero hits and unknown identifier
  `AlgebraicGeometry.IsEtale`. The actual pinned Mathlib source has `Etale`
  and a deprecated alias; the alias is not used in the delivery.
- Loogle: `"finite_preimage_singleton"` returned nine hits. The relevant
  `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton` requires a
  quasi-compact locally quasi-finite scheme morphism and is a proof input,
  not the algebraic-space statement being delivered.
- Mathlib grep: `finite_preimage|finite_fibre|finite_fiber` in AlgebraicGeometry,
  ten hits in scheme finite/quasi-finite/fibre modules and Zariski's main theorem;
  no matching algebraic-space transfer theorem.
- Direct `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for finite-fibre
  expressions found the scheme quasi-finite APIs and geometric-fibre statements
  for algebraic-space morphisms, but no finite-fibre chart-transfer statement.
  Searches for the exact item id in `lean/WeilConjectures` returned no hits.
  Name searches for `finite_preimage_singleton_of_etaleCover` and
  `EtaleChartFiniteFibreTransfer` across Mathlib and both project roots returned
  no hits. The upstream name inventory also had no corresponding declaration.

Validation: `scompile.py Q104 lem-sfb-etale-chart-finite-fibre-transfer` compiled
the delivered file in both sandbox and library module modes, with no errors or
non-sorry warnings. The signature was extracted verbatim from the theorem keyword
up to `:=` for the node's `lean.statement`. The node copy changes only `lean`;
JSON uses indent 1, Unicode text, and a final newline. No upstream files were
edited and no Git command or global build was run by the worker.

## Second reading by Q104

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
