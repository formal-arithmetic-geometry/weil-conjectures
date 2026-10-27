## Worker report

The module `Sheaf.AlgebraicGeometry.NormalGenericChartClopens` states
`AlgebraicGeometry.ProEtale.normal_generic_chart_clopens`, with a single `sorry` proof.
There are no definitions, helper theorems, new nodes, dependency repairs or statement
corrections. The original node is changed only in `lean`.

Hypotheses and objects, matched to the node:

- `X : Scheme.{u}` and `[IsIntegral X]` express the nonempty integral scheme.
  Mathlib's class includes nonemptiness and the domain property for nonempty opens;
  a second nonemptiness hypothesis would be redundant.
- `[IsLocallyNoetherian X]` expresses local Noetherianity.
- `hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)` is exactly the normal-domain condition
  on every local ring, using the recorded inline normal-domain form.
- The generic point is the canonical `genericPoint X`. The function field is
  `X.functionField`, definitionally its structure-sheaf stalk. Its field instance
  comes from integrality. The generic inclusion is `X.fromSpecStalk (genericPoint X)`.
- `U : X.ProEt` is the recorded small pro-etale object; `U.left` is its scheme and
  `U.hom` its structural morphism. No affine or nonempty hypothesis is imposed on U.
- `V : X.Opens`, `_hV : IsAffineOpen V` and `[Nonempty V]` specify exactly the
  nonempty affine base open. `W : U.left.Opens`, `hW : IsAffineOpen W` and
  `hWV : W ≤ U.hom ⁻¹ᵁ V` specify the affine chart and actual containment of its
  image in V. No nonemptiness or domain assumption is imposed on W or its ring.
- `R` and `B` are the canonical rings `Γ(X, V)` and `Γ(U.left, W)`. The applied
  lambda installs exactly `(U.hom.appLE V W hWV).hom.toAlgebra` as the chart algebra
  structure; it introduces no arbitrary algebra or additional hypothesis.

Conclusions, matched to every clause:

- The first conjunct is `Opens.IsBasis` of the affine opens admitting such a V.
  Its existential nonemptiness is `Nonempty V`, not nonemptiness of the chart.
- For every chart pair, `IsDomain Γ(X, V) ∧ IsIntegrallyClosed Γ(X, V)` is precisely
  that R is an integrally closed domain.
- `IsFractionRing Γ(X, V) X.functionField` is the fraction-field identification
  via the canonical germ algebra supplied by `Scheme.germToFunctionField`. This
  universal-property formulation determines the unique R-algebra isomorphism
  from `FractionRing R` to k, with the prescribed germ map; it is not an arbitrary
  field isomorphism.
- `Algebra.WeaklyEtale R B`, with the chart-induced algebra just specified, has
  exactly the flatness and flat tensor-multiplication fields stated in the node.
- The generic fibre is the actual `pullback (W.ι ≫ U.hom)
  (X.fromSpecStalk (genericPoint X))`, and its first projection is i_W.
- The existential isomorphism `e` identifies that fibre with
  `Spec (CommRingCat.of (B ⊗[R] X.functionField))`. Its first projection equation
  is `e.inv ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap B D)) ≫
  hW.isoSpec.inv`. Thus the projection really is induced by b mapped to b tensor 1.
  The second projection equation identifies the map to Spec k with tensor
  `includeRight`. These equations characterize the canonical isomorphism uniquely
  by the pullback universal property; existence does not choose an arbitrary map.
- `IsLocalization ((nonZeroDivisors R).map (algebraMap R B)) D` says D, with its
  actual B-algebra map, is the localization at the image of R minus zero.
  Since R is a domain, `nonZeroDivisors R` is exactly its nonzero elements. The
  localization universal property gives the unique B-algebra isomorphism to the
  chosen localization, so this expresses the node's second canonical ring
  identification, including its map on B.
- `Function.Injective (algebraMap B D)` is the asserted injection.
- `Set.BijOn (algebraMap B D) {e | IsIdempotentElem e}
  {e | IsIdempotentElem e}` is the bijection on idempotents; it includes that the
  map takes idempotents to idempotents, injectivity there and surjectivity there.
  `IsIdempotentElem` means e * e = e, equivalent to e squared = e.
- The last `Function.Bijective` applies to the literal inverse-image function
  on `Clopens W.toScheme` under `pullback.fst`. The clopen proof is obtained by
  continuity of that projection. Its codomain explicitly uses the pullback in
  `Scheme.{u}`, then its underlying topological space.

Dependencies used (all recorded interfaces read in source, with docstrings):

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  with `IsDomain` for the recorded normal-domain conjunction.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  the category of weakly etale objects over X; its `left` and `hom` are used directly.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  and `Scheme.Hom.appLE` (the genuine chart map).
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: publicly exposes the recorded
  `Algebra.WeaklyEtale` through `Sheaf.RingTheory.IndPrincipalZariski`; this is
  Mathlib's class with flat and flat_lmul' fields, not a private replacement.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`,
  `Scheme.germToFunctionField`, its algebra instance and
  `functionField_isFractionRing_of_isAffineOpen`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.isBasis_affineOpens`,
  `IsAffineOpen.isoSpec`, and `Scheme.Opens.toSpecΓ`.
- Proof imports follow the remaining recorded proof dependencies:
  `Mathlib.AlgebraicGeometry.StructureSheaf`
  (`StructureSheaf.IsLocalization.to_stalk`),
  `Mathlib.RingTheory.LocalProperties.IntegrallyClosed`
  (`IsIntegrallyClosed.of_localization_maximal`),
  `Sheaf.AlgebraicGeometry.EtaleComparison`
  (`etale_indEtale_weaklyEtale_comparison`, especially clause 4),
  `Mathlib.AlgebraicGeometry.Pullbacks` (`pullbackSpecIso`),
  `Mathlib.RingTheory.Flat.Basic` (`Module.Flat.lTensor_preserves_injective_linearMap`),
  `WeilConjectures.RingTheory.ProEtale.WeakDimension`
  (`Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct`), and
  `Mathlib.RingTheory.Spectrum.Prime.Topology`
  (`PrimeSpectrum.isIdempotentElemEquivClopens`). Some are public because their
  notions also occur in the statement. No proof-dependency import creates a cycle.

Edge cases checked: U empty (basis vacuous); W empty with any permissible nonempty
V (B and D zero, injectivity still holds, idempotents and clopens singleton); X a
field spectrum; reducible or non-Noetherian B (neither condition is excluded);
non-quasi-separated X (no affine intersection is required). The nonempty integral
base excludes exactly the empty base excluded in the node. All scheme/ring objects
use the site's existing universe u, with no extra universe equation or smallness
restriction. No statement fault or disputed mathematical clause was found.

Searches on 2026-10-24:

- `msearch.py leanfinder`, query "Normal integral scheme weakly etale affine charts
  generic fibre injective localization bijective idempotents clopens": eight hits,
  including `IsIntegral`, germ injectivity and etale-locus results; none states this
  chart/localization/idempotent/clopen theorem.
- `msearch.py loogle`, query `"WeaklyEtale", "Idempotent"`: zero hits.
- `msearch.py leansearch`, query "Normal integral scheme generic fibre weakly etale
  affine chart same idempotents clopen subsets": eight hits, all ring-spectrum
  clopen/idempotent correspondence results. Those existing notions are reused.
- `msearch.py grep`, query
  `(WeaklyEtale|weaklyEtale).*(idempotent|IsClopen)|idempotent.*(tensorProduct|fraction|localiz)`:
  two unrelated localization hits in `FractionRing.lean` and `Away/Basic.lean`.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, `normalGenericChart`, `normal_generic_chart`, and generic/clopen
  patterns: related generic-component and parent continuous-section theorems only.
  In particular `Sheaf.AlgebraicGeometry.NormalGenericContinuousSections` states the
  parent continuous-function assertion, not this chart/idempotent result. No existing
  declaration has the whole statement and no notion has been duplicated.

Sources read locally: Stacks `more-algebra.tex`, lemma-normality-goes-up (092W),
`algebra.tex`, lemma-disjoint-decomposition (00EE), plus the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.md` and its proof. The node supplies the agent
chart/idempotent deduction; its seven-step proof is reproduced in the theorem docstring.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
An initial elaboration error in the clopen codomain was repaired by explicitly
specifying `Scheme.{u}` and taking the underlying type of its pullback.

## Second reading by NF

This is a second pass by the assigned worker; no independent worker was started,
as required by the dispatcher brief. The maintainer supplies the independent review.
With the node and signature open together, this pass matched nonempty integrality,
local Noetherianity, normal stalks, arbitrary pro-etale U, exactly the permitted
chart pairs, the chart-basis assertion, normality of R, canonical germ fraction
field, chart-induced weak etaleness, tensor and localization identifications,
projection compatibility, injection, idempotent bijection and clopen inverse-image
bijection. The only elaboration correction was the explicit scheme pullback coercion.
The tensor-spectrum's second projection equation was retained to make canonicality
checkable, and the universal-property encodings of both ring identifications were
checked against their actual algebra instances. No mathematical mismatch, added
hypothesis, omitted clause or excluded empty chart was found. The item statement,
its dependencies and proof were not changed.
