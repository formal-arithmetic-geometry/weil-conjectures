## Worker report

Delivered item: `lem-fd-inversion`, group Q05, stage 2. The item module is
`Sheaf.Paper.WeilFourierInversion`. It states both inversion formulas as existence
of natural isomorphisms, with `sorry` as the entire proof of each theorem:

* `AlgebraicGeometry.WeilComplex.nonempty_iso_affineFourierTransform_comp_inv`;
* `AlgebraicGeometry.WeilComplex.nonempty_iso_affineFourierTransform_comp_self`.

The source is the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-thm-inversion/lem-fd-inversion.md`,
its proof file and unit `_section.md`, read together with the chapter's standing
nontrivial-character hypothesis. The fuller reviewed DAG proof supplies the finite-Tor
justification and anti-diagonal argument included in the declaration docstrings.
The source formulas are followed without a statement correction.

Hypotheses and objects, one by one:

* The finite field of definition is `(k₀ : Type u) [Field k₀] [Finite k₀]`.
  The geometric base `k` is `AlgebraicClosure k₀`, already part of the upstream
  `WeilComplex` construction on geometric fibers. Thus the input scheme in the
  Lean type is the finite-field model, not an assertion that the geometric base
  field is finite. Upstream `WeilSheaf.Category` lines 139–179 define the category
  as bounded complexes of pro-etale adic sheaves on that geometric fiber, with
  Frobenius isomorphism and constructible cohomology.
* The prime coefficient characteristic is `(l : ℕ) [Fact l.Prime]`, and distinctness
  from the base characteristic is `[Fact (ringChar k₀ ≠ l)]`. These are the standing
  Fourier conventions, also required by the recorded Weil Tate-twist declaration.
  Coefficients are the existing `PadicAlgCl l`, the project's fixed ℓ-adic algebraic closure.
* The affine vector space and its dual, after choosing the coordinates in the
  source's `V ≅ A^r`, are represented by
  `AffineSpace n (Spec (CommRingCat.of k₀))`, with `(n : Type u) [Fintype n]`.
  Their rank is exactly `Fintype.card n`, not a fixed rank-one specialization.
  Its geometric fiber is `A^r_k`. A finite coordinate type includes every
  nonnegative rank and introduces no ordering or nonemptiness requirement.
* The character is `(ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)`.
  Nontriviality is assumed throughout the source chapter. This is the existing
  finite-field Artin–Schreier model of the character ψ; the inverse is literally
  `ψ⁻¹`. No trace from the algebraic closure to a finite field is introduced.
* For every constructible Weil complex `K`: both sides are functors on the existing
  category `WeilComplex k₀ l (AffineSpace n (Spec (CommRingCat.of k₀)))`.
  Its objects are already bounded and constructible, so there is no additional
  constructibility hypothesis and no restriction to lisse or perverse inputs.

Conclusions, one by one:

* The first left side is
  `affineFourierTransform k₀ l n ψ ⋙ affineFourierTransform k₀ l n ψ⁻¹`.
  Lean's `⋙` first applies the left factor, so its component at `K` is exactly
  `FT_{ψ⁻¹}(FT_ψ(K))`.
* The first right side is
  `tateTwist k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) (-(Fintype.card n : ℤ))`.
  This is the recorded `AlgebraicGeometry.WeilComplex.tateTwist`, with exponent
  minus the actual rank. No extra cohomological shift remains in the conclusion.
* The second left side repeats the same character in both factors.
* The inverse of addition `ι'` is the existing `AffineSpace.neg n (Spec (.of k₀))`,
  whose source definition is the coordinate map `xᵢ ↦ -xᵢ` and whose square is the
  identity. Its pullback is the existing `WeilComplex.upperStar`. The second right
  side is that pullback followed by the same rank Tate twist, so its component
  is `(ι'^* K)(-r)`. The twist comes from the point, as in the source.
* Each `Nonempty (F ≅ G)` quantifies an isomorphism in the functor category,
  hence includes naturality in all `K` and compatibility with the Weil structure.
  It is not merely a family of unrelated object isomorphisms. The node asserts
  existence of functorial isomorphisms, not a particular arrow or triangle identity.

Dependency declarations used:

* `def-wf-tate-twist`: `WeilConjectures.WeilSheaf.TateTwist`,
  `AlgebraicGeometry.WeilComplex.tateTwist`. Its definition, the source docstring,
  `cyclotomicUnit`, and both nonnegative and negative sheaf-twist constructions
  were read. The twist uses the geometric-Frobenius cyclotomic scalar and the
  existing tensor with a lisse Tate sheaf.
* `def-fd-transform`: repaired interface `Sheaf.Paper.WeilFourierTransform`,
  `AlgebraicGeometry.WeilComplex.fourierTransformOfPairing` and
  `AlgebraicGeometry.WeilComplex.affineFourierTransform`; see below. The original
  `WeilConjectures.FourierTransform.Defs` / `AlgebraicGeometry.Etale.fourierTransform`
  remains publicly available and explicitly recorded in `lean.declarations`.
* Existing construction ingredients are
  `AlgebraicGeometry.artinSchreier`, `isLisse_artinSchreier`,
  `WeilSheaf.upperStar`, `WeilComplex.upperStar`, `WeilComplex.tensorLisse`,
  `WeilComplex.derivedLowerShriek`, `AffineSpace.stdPairing`, and `shiftFunctor`.
  In particular the kernel is constructed by actual pullback along the actual
  pairing function; it is not an arbitrary lisse sheaf or a chosen isomorphism.
* Recorded proof dependencies with modules are imported without `public`:
  `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition`,
  `WeilConjectures.WeilSheaf.LowerShriekFunctoriality`, and
  `Sheaf.Paper.FieldTorAmplitude`. The middle module is absent in the older local
  checkout; its current full source was read with `scompile.py --source`.
  `lem-fd-convolution-kernel` has no recorded module, so there is no module to import.
  No unrecorded convolution theorem is silently assumed in the signatures.

Edge cases checked before writing and again against the Lean:

* Rank zero: take an empty finite coordinate type. The pairing is the empty sum,
  the transform shift is zero, and the conclusion twist is zero. No `[Nonempty n]`
  or positive-rank hypothesis excludes it.
* Rank one: `Fintype.card n = 1` gives the single twist `-1` and the shift `1`
  in the defining transform. The formula is the same as the existing line transform,
  while the new definition covers arbitrary rank.
* Characteristic two: no assumption `p ≠ 2` is imposed; negation may equal identity,
  in agreement with both formulas.
* Zero complex: the natural-isomorphism statements include it automatically.
* Trivial character: for positive rank the constant-kernel transform is not
  invertible (it factors through compact-support cohomology). Thus the standing
  nontriviality hypothesis is essential and was made explicit.
* There is no `[Finite Λ]` condition on the ℓ-adic algebraic closure, no requirement
  that it be a torsion ring, and no finite-coefficient theorem is substituted for
  the Weil-complex statement.
* Every universe and variable is explicitly bound, with `set_option autoImplicit false`.

Searches for an existing statement and missing interface:

* `msearch.py ... leanfinder`, query
  `Fourier Deligne transform inverse character composite natural isomorphism Tate twist and same character negation pullback`:
  eight hits on analytic inverse transforms and discrete Fourier transforms;
  no sheaf-theoretic Fourier–Deligne inversion.
* `msearch.py ... loogle`, query `fourierTransform, tateTwist`:
  zero hits, unknown identifier `fourierTransform`.
* `msearch.py ... leansearch`, query
  `Fourier Deligne inversion on constructible Weil complexes inverse character Tate twist`:
  eight hits on analytic Fourier pairs and inverse transforms; no Weil-complex result.
* `msearch.py ... grep`, query
  `fourierTransformInversionIso|fourierTransformSquareIso|affineFourierTransform_comp`:
  zero Mathlib hits. A second Mathlib grep for
  `fourierPairingKernel|fourierTransformOfPairing|WeilComplex.affineFourierTransform`
  also returned zero hits.
* `rg` in `WeilConjectures/` and `lean/Sheaf/` found the ordinary-etale inversion
  theorems in `WeilConjectures/FourierTransform/Inversion.lean`; their full signatures
  and docstrings were read. They require finite coefficient rings and give natural
  isomorphisms on ordinary-etale derived categories, not on Weil complexes.
* `WeilConjectures/WeilSheaf/Fourier.lean` defines the actual Weil transform only
  on the affine line and states that it is an equivalence. It does not state either
  rank-r natural isomorphism. Its definitions of the kernel, tensor with a lisse
  sheaf, transform, and lisse proof were read and reused as the construction pattern.
* `WeilConjectures/WeilSheaf/FourierTateTwist.lean` concerns commutation of the
  line transform with twists, not inversion or a rank-r transform.
* `dag/lean_names_upstream.json` records only the ordinary-etale transform for
  `def-fd-transform` and no usable rank-r Weil inversion interface.
* `rg` for every proposed new name in both upstream `WeilConjectures/` and
  side-project `lean/Sheaf/` returned no duplicate declaration.

Validation: `scompile.py Q05 lem-fd-inversion <WeilFourierTransform.lean>
<WeilFourierInversion.lean>` successfully compiled each delivered file separately,
with its own logical module path as well as the sandbox checks. No warnings or
errors were emitted. The only new postponed statements are the two inversion
theorems, both associated with this DAG node and each with its full proof docstring.
All new definitions have real data; the model instances are explicit structures
filled using `rfl`, the existing pullback equation, and the existing negation-over
lemma. No new mathematical lemma is proved.

## Dependency modules

`def-fd-transform`: the recorded declaration
`AlgebraicGeometry.Etale.fourierTransform` has domain and codomain ordinary-etale
module-sheaf derived categories. Its source explicitly says that the Qbar-ell
version is not formalized there. The upstream Weil transform in
`WeilConjectures.WeilSheaf.Fourier` only treats the affine line. Consequently neither
interface can express the item's arbitrary-rank Weil statement.

The lean-only repair adds `Sheaf.Paper.WeilFourierTransform`. It retains the exact
ordinary-etale transform requested by the dependency's current blueprint snapshot
by publicly importing its module and including its declaration in the mixed
`lean.declarations` record. The added declarations give the same formula with the
existing Weil operations. For a product `Z = V ×_S V'`, a function `b` gives the
canonical map `Z → A¹`; `fourierPairingKernel` is the pullback of the existing
Artin–Schreier Weil sheaf. `fourierTransformOfPairing` is pullback by the first
projection, derived tensor with this lisse kernel, compact-support direct image
by the second projection, and shift by `r`. The finite-field structure and
projection-over binders identify the common model. Its separation and finiteness
binders are the existing shriek interface requirements and are satisfied for the
vector bundles over separated finite-type bases of the node. The ordinary-etale
ambient exact triangulated functor remains the existing recorded construction;
the new Weil construction acts on the constructible category needed by this item.

`affineFourierTransform` specializes the formula to `AffineSpace.stdPairing` and
shift `Fintype.card n`. It supplies projection properties from the actual affine
structure morphism by the existing pullback-stability instances, not hypotheses
on the inversion theorems. The canonical product-over and negation-over instances
have explicit data. These are helpers for the same transform, listed in the node's
record; no independent notion or new node is introduced. No field of the dependency
node except `lean` changes, and its `lean.note` explains this repair.

## Second reading by Q05

This is the author's second pass, not an independent reviewer: the dispatcher brief
forbids starting other agents and assigns the independent reading to the maintainer.
I reopened the complete item, current blueprint unit and node text, both dependency
records and full declarations, and both new modules.

I checked the finite-field model versus its geometric fiber explicitly in
`WeilSheaf.Category`: the Lean input is indeed a constructible Weil complex on
`A^r_k`. I checked composition order, both characters, the negative rank in each
Tate twist, the negation pullback in the second formula, and that `Nonempty (F ≅ G)`
expresses naturality. I checked empty coordinate type, rank one, and characteristic
two. There is no added mixedness, lissity, perversity, finite-coefficient, or positive-rank
condition on the input, and no shift remains in the conclusions.

For the dependency module I compared the ordinary-etale snapshot with its retained
public upstream declaration, and compared the added Weil formula with the existing
rank-one construction. The generic formula uses the actual product projections and
function, and its affine specialization uses the standard pairing with precisely
the rank shift. Both source interpretations are retained instead of silently replacing
the coefficient category. Compilation initially exposed a missing finite-type
instance for the product's structure morphism; this was supplied in the affine
specialization from the first projection and the actual affine structure morphism,
without adding a hypothesis to either inversion statement. Both files then compiled
cleanly. No statement mismatch requiring a correction was found.

## Reviewer fix (maintainer second reader, 2026-10-18)

H4 (one definition per notion): the delivered helper `AlgebraicGeometry.WeilSheaf.fourierPairingKernel`
was, word for word, the existing upstream `AlgebraicGeometry.artinSchreierOf` of
`WeilConjectures.WeilSheaf.FourierInversion.Defs` (the pullback of `artinSchreier ψ 1` along
`AffineSpace.homOfVector (X ↘ Spec k₀) (fun _ ↦ b)`), with `isLisse_artinSchreierOf` as its
lisse proof. The fixed `Sheaf.Paper.WeilFourierTransform` drops the copy and builds
`fourierTransformOfPairing` with `artinSchreierOf ψ b` / `isLisse_artinSchreierOf ψ b`; it imports
`WeilConjectures.WeilSheaf.FourierInversion.Defs` (which publicly imports
`WeilConjectures.WeilSheaf.Fourier`). No signature changes: the recorded statement of
`fourierTransformOfPairing` and both inversion statements are unchanged.

The searches above missed the upstream `WeilConjectures/WeilSheaf/FourierInversion.lean`: it proves
`AlgebraicGeometry.nonempty_iso_fourierTransform_comp_inv`, the first formula for the rank-one
line transform only, with the shifts `[-2][1][1]` left uncancelled, and has no same-character
formula. It therefore does not make this rank-`r` item existing, but it is the upstream
counterpart of the first formula for `n = PUnit`.

Because the fixed module is re-read by the merge tool, `lean.declarations` of `def-fd-transform`
keeps only the names the module declares. `AlgebraicGeometry.Etale.fourierTransform` stays
publicly imported through `WeilConjectures.FourierTransform.Defs` and remains the node's
`blueprint_lean`.
