## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothOpenDeformationLift` states
`AlgebraicGeometry.exists_smooth_open_deformation_lift`, with its entire proof
postponed by `sorry`. No definitions, helper theorems, or additional nodes are
introduced. The node changes only in `lean`.

Source read: `literature/stacks-project/examples-defos.tex`, Example
`example-schemes`, Situation `situation-glueing`, Lemmas `lemma-glueing`
(Tag 0DYZ) and `lemma-glueing-smooth` (Tag 0DZN). The second assertion applies
with U_1 smooth, hence a local complete intersection. The module docstring
retains the node's seven-step constructive proof with all its dependencies.

Clause-by-clause correspondence:

| Node data or condition | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| Finite-dimensional commutative k-algebras A and A' | `[CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [FiniteDimensional k A] [FiniteDimensional k A']` |
| Each augmentation kernel is its unique maximal ideal | `[IsLocalRing A] [IsLocalRing A']`, algebra homomorphisms `ε`, `ε'` into k, and kernel equations `hε`, `hε'` |
| Augmentation-preserving surjection A' → A | `q : A' →ₐ[k] A`, `hq : Function.Surjective q`, and `haug : ε.comp q = ε'` |
| X is a k-scheme | `X : Over (Spec (CommRingCat.of k))` |
| Affine opens U,V cover X | `U V : X.left.Opens`, `hcover : U ⊔ V = ⊤`, `hU : IsAffineOpen U`, `hV : IsAffineOpen V` |
| Affine intersection | `hUV : IsAffineOpen (U ⊓ V)` |
| U and U∩V smooth over k | `hsU : Smooth (U.ι ≫ X.hom)` and `hsUV : Smooth ((U ⊓ V).ι ≫ X.hom)` |
| Flat Y over Spec A | `Y : Over (Spec (CommRingCat.of A))`, `[Flat Y.hom]` |
| Specified k-isomorphism of its special fibre with X | `φ : (Over.pullback (Spec.map (CommRingCat.ofHom ε.toRingHom))).obj Y ≅ X` |
| Y_V is the open corresponding to V | `YV : Y.left.Opens`, with `hYV` equating its inverse image under the special-fibre projection to the inverse image of V under `φ.hom.left` |
| Given flat A'-scheme Z | `Z : Over (Spec (CommRingCat.of A'))`, `[Flat Z.hom]` |
| Given A-isomorphism e from Z_A to Y_V | `e : (Over.pullback (Spec.map (CommRingCat.ofHom q.toRingHom))).obj Z ≅ Over.mk (YV.ι ≫ Y.hom)` |
| Existence of flat A'-scheme Y' | `∃ Y' : Over (Spec (CommRingCat.of A')), Flat Y'.hom ∧ ...` |
| A-isomorphism α from Y'_A to Y | existential `α : (Over.pullback (Spec.map (CommRingCat.ofHom q.toRingHom))).obj Y' ≅ Y` |
| Y'_V is the open for V under the marking induced by α | existential `Y'V` with inverse image under Y'_A → Y' equal to `α.hom.left ⁻¹ᵁ YV` |
| A'-isomorphism γ : Y'_V ≅ Z | existential `γ : Over.mk (Y'V.ι ≫ Y'.hom) ≅ Z` |
| e ∘ γ_A = α restricted to Y_V | final equality in `Over (Spec A)`, using `(Over.pullback ...).mapIso γ` and the pullback of the actual inclusion `Over.homMk Y'V.ι` |

Augmentations are algebra maps, so are automatically surjective (they split
the structure homomorphism k → A or k → A'). Locality and the kernel equations
say exactly that the augmentation ideal is the unique maximal ideal, without
assuming a nilpotence bound or adding an Artinian hypothesis.

The binder `YV` and its equation are a presentation of the node's labelled open,
not a hypothesis about an arbitrary open unrelated to V: reduction is a
homeomorphism under the stated ring hypotheses, so there exists exactly one
such open for every V. The conclusion labels `Y'V` by reduction modulo ker q;
this is equivalent to labelling by the special fibre because the two
nilpotent reductions compose. Thus no extra topological assumption or chosen
inverse homeomorphism is needed. The final equation is written after the open
inclusion Y_V → Y. Since this inclusion is a monomorphism, it is equivalent to
the equation into Y_V in the node. The right-hand side is the canonical
base-change of the open inclusion followed by α, so the equation also supplies
the factorization through Y_V. All four isomorphisms are in slice categories,
so their compatibility with the structural maps is part of their types.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, Mathlib.AlgebraicGeometry.Scheme.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`, Mathlib.AlgebraicGeometry.Morphisms.Flat; its docstring identifies the stalkwise criterion.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, supplied for schemes by Mathlib.AlgebraicGeometry.Pullbacks.

The slice-category packaging uses Mathlib.CategoryTheory.Comma.Over.Pullback
(`Over.pullback`) and Mathlib.CategoryTheory.Comma.Over.Basic (`Over.mk`,
`Over.homMk`). These are the actual fibre-product functor and actual open
inclusions, not new versions of schemes, isomorphisms or base change.

Plain proof imports retain the plan: `WeilConjectures.AlgebraicGeometry.Thickening`
(`IsThickening`, `IsFirstOrderThickening`, `IsNthOrderThickening`,
`IsFiniteOrderThickening`), Mathlib.AlgebraicGeometry.Morphisms.Proper
(`IsProper.isStableUnderBaseChange`, with the smooth clause in the public Smooth
module), `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`
(`Smooth.flat_and_locallyOfFinitePresentation`),
`Sheaf.AlgebraicGeometry.AffineSmoothTrivializationLift`
(`exists_affine_smooth_trivialization_lift`), Mathlib.RingTheory.HopkinsLevitzki
(`instIsNoetherianRingOfIsArtinianRing`, `isArtinianRing_iff_isNilpotent_maximalIdeal`),
and Mathlib.AlgebraicGeometry.Gluing (`Scheme.GlueData.glued`,
`ι_isOpenImmersion`, `ι_jointly_surjective`, `glue_condition`,
`vPullbackConeIsLimit`, `Scheme.OpenCover.glueMorphisms`, `hom_ext`,
`ι_glueMorphisms`). The open-immersion base-change instance is supplied by
Mathlib.AlgebraicGeometry.OpenImmersion through the scheme pullback imports.

Edge cases checked before writing:

- Empty U is allowed by `IsAffineOpen` and smoothness; the construction is Z.
- Empty V gives the empty labelled opens and the unique empty isomorphism.
- Empty intersection gives disjoint gluing; neither overlap nor open is assumed nonempty.
- Empty X (both opens empty) is allowed.
- Identity q, and A = k or A' = A = k, are allowed; no strictly positive ideal power or nonzero kernel is required.
- Arbitrary characteristic is allowed. The rings cannot be the zero ring because they are augmented to a field; this is already forced by the node, not an extra restriction.
- Y and Z have no affineness, finite-presentation, properness, or smoothness assumption.
- All schemes and rings have a single explicit ambient universe u, as required for the Mathlib category of schemes and its Spec functor; the theorem is universe-polymorphic. Every variable is bound explicitly.

Searches for an existing statement:

- Prescribed `msearch.py ... leanfinder`, query “A flat deformation of one affine open extends across a smooth affine open with smooth affine overlap”: 8 hits, consisting of flat affine-chart criteria, smooth charts, and smooth-fibre criteria. None extends a prescribed open deformation compatibly with its marked reduction.
- Prescribed `msearch.py ... loogle`, query `AlgebraicGeometry.Smooth, AlgebraicGeometry.Flat`: 3 hits (`instFlatOfSmooth`, flat descent of smoothness, smoothness from smooth fibres). No matching statement.
- Prescribed `msearch.py ... grep`, query `deformation|trivialization` in AlgebraicGeometry: 0 hits.
- `rg` in both live roots for `smooth.open.deformation|smooth_open_deformation|trivialization|lem-sfb-smooth-open-deformation-lift`: many unrelated bundle/sheaf trivializations; the relevant landed affine lifting theorem is used as a proof dependency. No existing theorem of this node's strength.
- Narrowed `rg` in both AlgebraicGeometry directories for `smooth.open.deformation|extends.*smooth affine|deformation.*affine open`: no matching declaration.
- Direct search for the node id in WeilConjectures: no hit; in Sheaf the only previous hit is a proof-plan citation in IsolatedCurveFormalLifting.

No statement dispute, source correction, dependency-record repair, or new node was needed.

Validation: prescribed `scompile.py` compiled both the sandbox and the module
under its library name, cleanly (2.0 s and 1.6 s); no errors or warnings.

## Second reading by Q98

I reopened the node and final Lean statement for a separate clause-by-clause
pass. This is the worker's rereading; the dispatcher forbids starting another
agent, and the maintainer supplies the independent review. In particular I
checked both augmentation-kernel equations, both affine opens and their affine
overlap, both smoothness hypotheses, the k-linearity of the marking, the
A-linearity of e and α, and the A'-linearity of γ. I checked that the last equation
uses the specified e and actual functorial reduction of γ, so existence of an
unrelated global lift does not satisfy it. The `hYV` and concluding inverse-image
equations identify precisely the labelled opens, including empty ones. The
final equality after the open inclusion is equivalent by monicity to the node's
restriction equation. No missing or extra mathematical hypotheses or clauses
were found; no correction was made in this pass.
