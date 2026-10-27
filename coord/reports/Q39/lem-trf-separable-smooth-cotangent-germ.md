## Worker report

The module `Sheaf.AlgebraicGeometry.SeparableSmoothCotangentGerm` states
`AlgebraicGeometry.Scheme.Hom.exists_separableSmoothCotangentGermChart` with proof
`sorry`. Its public transparent helper `SeparableSmoothCotangentGermChart` is the
expanded conclusion of this same lemma, with real definitions of all scalar actions;
it is not a second definition of any geometric object. Its `let` expressions are
inside the definition body, not in the theorem signature. Unfolding the helper exposes
all witnesses, equations, and the final germ. No other theorem is postponed, no new
DAG node is needed, and no statement correction or dependency repair is made.

Hypothesis matching:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Smoothness: `[Smooth f]`, the recorded Stacks 02H6-compatible definition.
- The point: `(x : X)`; `s` is `f x`, `k` is `S.residueField (f x)`, and `L` is
  `X.residueField x`. The original extension is exactly `f.residueFieldMap x`.
- The unique fibre point: `f.asFiber x` in `f.fiber (f x)`, the recorded canonical fibre.
- Closedness in that fibre: `hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))`.
- Finite-dimensional residue extension: `hfinite : (f.residueFieldMap x).hom.Finite`.
  A finite ring homomorphism means finite generation of the target as a source
  module; for fields this is exactly finite-dimensionality, not finite type as an
  algebra and not a finite underlying field.
- Separable algebraic extension: `hsep : @Algebra.IsSeparable ...
  (f.residueFieldMap x).hom.toAlgebra`. Algebraicity is included in this class.
- Positive finite local fibre dimension: `d : ℕ`, `hd : 1 ≤ d`, and
  `hdim : topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞)`.

Conclusion matching, after unfolding the helper:

- The theorem supplies opens `V`, `W`, `hWV : W ≤ f ⁻¹ᵁ V`, `hx : x ∈ W`,
  `hs : f x ∈ V`, `hW : IsAffineOpen W`, and `IsAffineOpen V`.
  Thus these are the specified affine neighbourhoods with f(W) contained in V.
  Take B = Γ(S,V), A = Γ(X,W). Their affine identifications are the existing
  `IsAffineOpen.fromSpec`; the ring map is exactly `f.appLE V W hWV`.
- The definition installs this map's `toAlgebra` and requires `Algebra.Smooth B A`.
  `b : Module.Basis (Fin d) A (KaehlerDifferential B A)` is freeness of rank d.
- C is literally `k ⊗[B] A`, with B acting on k by `S.evaluation V (f x) hs`.
  Mathlib's tensor-product commutative algebra supplies exactly
  `(l ⊗ a) * (m ⊗ b) = (l*m) ⊗ (a*b)`; no alternative tensor multiplication is used.
- `Algebra.Smooth k C` and `Algebra.FiniteType k C` state both claimed properties.
- `j : Spec (.of C) ⟶ f.fiber (f x)` is an open immersion whose range is the
  inverse image of W. The two displayed projection equations specify the canonical
  affine fibre chart, with right tensor inclusion to A and left tensor inclusion
  from k. `q : PrimeSpectrum C` and `hq : j q = f.asFiber x` identify the specified
  prime with the original fibre point, rather than an unrelated prime.
- R is literally `Localization.AtPrime q.asIdeal`. `eR` identifies it with the
  actual fibre stalk. Its equation on every c : C says that the equivalence
  commutes with the canonical localization map, the affine global-section germ,
  and the chart stalk map (with the point equality transported by `stalkCongr`).
  This is the canonical stalk-localization identification, not an arbitrary iso.
- `IsRegularLocalRing R` includes localness and Noetherianity. `IsDomain R` gives
  the explicit domain assertion. There is no Noetherian hypothesis on S.
- `eL : IsLocalRing.ResidueField R ≃+* L` is the residue identification. Its
  equation for every t in O_X,x commutes with `f.fiberStalkMap x` and
  `X.residue x`; this pins down the structural residue map. R acts on L through
  `eL ∘ IsLocalRing.residue R`, not an arbitrarily selected algebra structure.
- E is `L ⊗[R] KaehlerDifferential k R`, EA is
  `L ⊗[A] KaehlerDifferential B A`, and F is
  `L ⊗[X.presheaf.stalk x]` the existing relative-differential sheaf stalk.
  These are the node's tensors with their factors commuted, via the canonical
  `TensorProduct.comm`. With this convention L acts on the first factor.
- `eA : E ≃ₗ[L] EA`, `eCoord : EA ≃ₗ[L] (Fin d → L)`, and
  `eSheaf : EA ≃ₗ[L] F` give the full displayed identification chain (compose the
  inverse of eCoord with eSheaf for the last displayed arrow). The eCoord formula
  is extension of the chosen b.repr to L; differentials generate the Kahler module,
  so the formula on all `D a` specifies this basis comparison on the whole module.
- The eA formula sends d(l ⊗ a) to the residue of l times da. The eSheaf formula
  sends da to the germ of the existing universal sheaf derivation. The additional
  formula for every U, hxU and a relates the fibre differential of the germ of a
  to its sheaf differential. Thus compatibility holds for every germ, including
  fractions, not only for the sections of the selected affine chart.
- The conormal arrow is `δ : (IsLocalRing.maximalIdeal R).Cotangent →ₗ[R] E`.
  It is surjective and satisfies the specified formula on every representative z:
  `δ (m.toCotangent z) = 1 ⊗ D z`. `Ideal.Cotangent` is exactly m/m².
  The formula uniquely characterizes this map on the quotient.
- The final witness `h : X.presheaf.stalk x` belongs to the original maximal ideal.
  Its fibre image is literally `eR.symm ((f.fiberStalkMap x).hom h)`, required to
  lie in the maximal ideal of R. Its differential tensor is nonzero in E.
  The all-germs compatibility equation identifies that nonzero tensor with dh
  in the relative differential sheaf fibre (every stalk element is a section germ).
- `Function.Injective (fun r : R ↦ eR.symm ((f.fiberStalkMap x).hom h) * r)` is
  the specified injectivity of multiplication by the fibre image.

Dependency declarations used/read:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; affine smooth restriction
  and the `HasRingHomProperty` ring criterion are proof imports.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`, `Scheme.evaluation`, `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `asFiber`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `RingHom.toAlgebra`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.RingTheory.Smooth.Basic`: `Algebra.Smooth` and its base-change instance.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`, and the conormal
  quotient-map interface in `kerCotangentToTensor`; the statement specifies the
  same map on the maximal-ideal cotangent quotient without identifying that ideal
  with an equal-but-differently-written kernel by a hidden cast.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` (extends
  `IsLocalRing` and `IsNoetherianRing`). The regular-scheme dependency's mathlib_match
  supplies the ring clause; `IsRegularScheme` itself is not needed for this node.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `Mathlib.RingTheory.TensorProduct.Basic`:
  `TensorProduct`, `Algebra.TensorProduct.includeRight`, tensor algebra multiplication.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`, including
  the documented affine/restriction comparisons used by the proof plan.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  the recorded general presheaf-module stalk interface. On these scheme module
  sheaves the existing `RingedSpace.moduleStalkFunctor` from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` supplies the same carrier
  with the existing stalk-ring module structure, as the dependency record directs.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, included in regularity.
- `Sheaf.AlgebraicGeometry.FibreStalkQuotient`: `Scheme.Hom.fiberStalkMap` and its
  surjectivity/kernel/quotient-equivalence theorem. This actual canonical map is used.
- Proof imports cover recorded modules for smooth differential rank,
  affine-open stalk localization, smooth-over-field regularity, the regular-local
  domain theorem, base change and localization of differentials, tilde stalks and
  separable-field differential vanishing. `lem-trf-affine-fibre-point-dimension`
  has no Lean/module or mathlib_match yet and therefore has no import; it is only
  a proof dependency and its chart conclusion is included in this item's statement.

Sources read: Stacks more-morphisms.tex, `lemma-slice-smooth-once` (057D), its
separability discussion and `lemma-slice-smooth` (057G), including the positive-
dimensional induction and finite residue extension argument. Also inspected the
current blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/
sk-i-curve-zero/lem-trf-local-term-locality.md` and its historical-branch context;
this auxiliary node is not that unit's own statement.

Edge cases checked before writing: X empty gives no x, as required; d = 0 is
excluded explicitly by hd; d = 1 is allowed with Fin 1 coordinates; no perfectness,
characteristic-zero, algebraically-closed-base, finite underlying field, or
Noetherian-base hypothesis is imposed. Finite extensions of arbitrary degree
(including degree one) are allowed. Inseparable closed points are excluded by
hsep, as required by the counterexample discussed immediately after Stacks 057D.
No global bound on the fibre's dimension or any other fibre is assumed. The fixed
scheme universe u is shared by all the canonically constructed charts and residue
fields and puts no new size condition on the scheme morphism.

Searches (2026-10-24, `msearch.py Q39 lem-trf-separable-smooth-cotangent-germ`):

- LeanFinder: “A smooth morphism at a closed point with finite separable residue
  extension has a maximal ideal germ with nonzero relative differential and
  nonzerodivisor fibre image”. Eight hits, principally smooth/etale/unramified loci
  and local unramified criteria; none states this scheme-germ package.
- Loogle: `KaehlerDifferential, Algebra.IsSeparable`. Zero hits.
- grep in Mathlib/RingTheory: `(cotangent|conormal|separab).*(surject|nonzero)|
  (surject|nonzero).*(cotangent|conormal)`. Twenty-five hits, including cotangent
  quotient-surjectivity and presentation lemmas; none states the whole result.
- LeanSearch: “A smooth scheme morphism at a closed point with finite separable
  residue extension admits a maximal ideal germ with nonzero relative differential
  and regular fibre image”. Eight hits, mainly smooth definitions and local
  formal smoothness/unramifiedness criteria; no exact statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for `separable.*cotangent`, `smooth.*cotangent.*germ`, `SeparableSmooth`,
  `cotangentGerm`, relative differential stalks and derivations: found the shared
  differential-sheaf construction, rank theorem, separable-residue cotangent
  injectivity and the fibre-stalk quotient. No existing full theorem.
- `grep -rn` for this node ID in `lean/WeilConjectures`: no match.
  Existing helper declarations in ConormalSequenceSmoothImmersion use the same
  sheaf-stalk carrier; its general stalk derivation is private, so this delivery
  specifies compatibility directly on all representatives instead of copying it.

Validation: `scompile.py Q39 lem-trf-separable-smooth-cotangent-germ` compiled the
sandbox probe and final library module cleanly (12.1 s and 14.2 s respectively),
with `set_option autoImplicit false`. No diagnostic commands remain. Every line
is at most 100 characters. The only postponed proof is the named main theorem.

## Second reading by Q39

Single-worker second pass, with the node and final file reopened; the maintainer
will supply the independent review. Rechecked every hypothesis and each chart,
ring, differential, conormal and germ clause against the node as listed above.
The first compiler pass found shorthand `.ofHom` elaboration and an insufficiently
specified stalk module carrier. The final version spells out `CommRingCat.ofHom`
and uses the recorded ringed-space stalk functor with explicit F annotations.
These are elaboration repairs, not mathematical changes. Confirmed that the
localization and residue comparisons commute with the structural maps and that
the differential compatibility quantifies over every section germ, covering
fractions and the final h. No mismatch or statement dispute remains.
