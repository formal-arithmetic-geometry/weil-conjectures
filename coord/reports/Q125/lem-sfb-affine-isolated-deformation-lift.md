## Worker report

The module `Sheaf.AlgebraicGeometry.AffineIsolatedDeformationLift` states
`AlgebraicGeometry.exists_affine_isolated_deformation_lift`, with `sorry` as
its entire proof. It introduces no new definition. Only the item's `lean`
record changes. No statement correction or disputed statement is needed.

Source read: `literature/stacks-project/examples-defos.tex`,
`example-rings` (lines 814–831), `lemma-affine` (Tag 0DYX, lines 1383–1399),
and `lemma-isolated` (Tag 0DZF, lines 2657–2720). The first smooth arrow is
used with its compatible reduction marking. No completion, henselization,
tangent-space assertion, or extra finiteness conclusion is stated.

The correspondence with every hypothesis is as follows.

| Node hypothesis | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Commutative k-algebras A', A | `[CommRing A'] [CommRing A] [Algebra k A'] [Algebra k A]` |
| Finite-dimensional coefficient algebras | `[FiniteDimensional k A'] [FiniteDimensional k A]` |
| The coefficient homomorphism is k-linear | `[Algebra A' A] [IsScalarTower k A' A]`; its ring map is `algebraMap A' A` |
| Surjectivity | `hsurj` |
| Each ring has a unique maximal ideal | `[IsLocalRing A'] [IsLocalRing A]` |
| Augmentations to k | `ε' : A' →ₐ[k] k`, `ε : A →ₐ[k] k` |
| Augmentation kernels are the maximal ideals | `hε'`, `hε`, using `RingHom.ker` and `IsLocalRing.maximalIdeal` |
| Respect for augmentations | `haug` |
| V affine, of finite type over k | `[IsAffine V]`, `f`, `[LocallyOfFiniteType f] [QuasiCompact f]` |
| A finite list of distinct closed points | `r : ℕ`, `p : Fin r → V`, `hp`, `hclosed` |
| Smooth away from the listed points | `hsmooth`, giving a smooth open neighbourhood of every point outside `Set.range p` |
| Affine flat A-scheme Y | `[IsAffine Y]`, `g : Y ⟶ Spec (.of A)`, `[Flat g]` |
| Specified special-fibre marking | `j : V ⟶ Y` and `hspecial : IsPullback j f g (Spec.map … ε)` |
| Identify the points using the special fibre | The labelled point in Y is `j (p i)` |
| Local A'-algebras D_i | `D : Fin r → Type v`, with the dependent `CommRing`, `IsLocalRing`, `Algebra A'` instances |
| Flat and essentially finite type D_i | Dependent instances `Module.Flat A' (D i)` and `Algebra.EssFiniteType A' (D i)` |
| Specified reduction isomorphism δ_i | `δ i : (D i ⊗[A'] A) ≃+* Y.presheaf.stalk (j (p i))` together with `hδ` |
| Usual tensor algebra structure | Mathlib's commutative ring structure on `TensorProduct A' (D i) A` |

The correspondence with every conclusion is as follows.

| Node conclusion | Lean rendering |
| --- | --- |
| An affine scheme Y' flat over A' | Existential `Y'`, `g'`, and conjuncts `IsAffine Y' ∧ Flat g'` |
| Specified reduction isomorphism α over A | Existential `l : Y ⟶ Y'` and `IsPullback l g g' (Spec.map … (algebraMap A' A))` |
| Label the point p_i in Y' using reduction | `l (j (p i))` |
| Local A'-algebra isomorphisms β_i | Existential `β i : Y'.presheaf.stalk (l (j (p i))) ≃+* D i` and the first universal conjunct imposing scalar compatibility |
| Reduction of β_i followed by δ_i is α's local identification | Last universal conjunct, `δ i (β i z ⊗ₜ[A'] 1) = l.stalkMap (j (p i)) z` |
| r = 0 included | No nonemptiness or positivity hypothesis on `r`; dependent families over `Fin 0` are allowed |

A square `IsPullback j f g (Spec.map ε)` is exactly a marking of the
special fibre by V over Spec k: its universal property supplies the unique
isomorphism `pullback g (Spec.map ε) ≅ V` with these projections.
Conversely such a marking gives j and this square. Likewise the concluding
square is exactly the isomorphism α of the node; l is α inverse followed by
the first projection. These are actual universal-property conditions, not
unconstrained maps or extra geometric hypotheses.

The tensor's A-structure comes from its right factor. Consequently hδ,
which identifies the image of every `1 ⊗ a` with the scalar in the stalk,
says exactly that δ is an A-algebra isomorphism. The corresponding scalar
equation for β says that β is an A'-algebra isomorphism. Ring isomorphisms
between local rings are automatically local. The final equation is written
on `z ⊗ 1`; because the two resulting maps from the reduced stalk tensor
are A-linear, this characterizes equality on the whole tensor product.
In particular it retains the supplied δ rather than merely asserting
unmarked isomorphism of local lifts.

Dependency declarations used, with their recorded modules/interfaces:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (available through the public imports).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, Mathlib.AlgebraicGeometry.Scheme.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType; `QuasiCompact` is its recorded second clause.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth, used on open restrictions.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`, Mathlib.AlgebraicGeometry.Morphisms.Flat, equivalent to the recorded stalk condition by `Flat.iff_flat_stalkMap`.
- `def-pc-fibre-product`: the pullback universal property, `CategoryTheory.IsPullback`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs; Mathlib.AlgebraicGeometry.Pullbacks supplies scheme pullbacks. This is the universal-property form of the recorded chosen `CategoryTheory.Limits.pullback`.
- `def-weil-pbc-flat-ring-map`: `Module.Flat`, Mathlib.RingTheory.Flat.Basic, and the recorded Mathlib.RingTheory.RingHom.Flat; the dependency explicitly records both names.
- `def-weil-pbc-essentially-finite-type-algebra`: `Algebra.EssFiniteType`, Mathlib.RingTheory.EssentialFiniteness, as in its mathlib_match.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, Mathlib.LinearAlgebra.TensorProduct.Defs; its ring structure is Mathlib.RingTheory.TensorProduct.Basic.

All these signatures and docstrings were read in the source, as were the
recorded project proof modules. The proof-only imports include
`WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`,
`Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`,
`WeilConjectures.Algebra.FiniteTypeLiftNilpotent`,
`WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration`, and
`WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness`.
Artinian/Hopkins–Levitzki Mathlib inputs are imported privately. The three
proof dependencies `lem-sfb-cotangent-ext-smooth-support`,
`lem-sfb-finite-maximal-support-localization`, and
`lem-sfb-flat-algebra-small-extension-control` have no recorded Lean
statement yet; they are not needed to type this statement and are named in
the proof docstring without inventing interfaces for them.

Edge cases checked: r = 0; the empty affine scheme (which forces r = 0);
A' = A with the identity reduction; augmentation ideals equal to zero;
all field characteristics; and a listed point that is already smooth.
No nonempty scheme, singularity at every listed point, properness,
finite-type hypothesis on Y, or finite-type conclusion on Y' is imposed.
The local rings D_i have an independent universe v, and all universes and
variables are explicitly bound (`autoImplicit false`). The coefficient
rings and schemes share the usual Scheme universe u; test-algebra
quantification in a smaller independent universe is not used.

Searches performed through msearch.py (logged in searches.jsonl):

- LeanFinder: “An affine scheme smooth outside finitely many closed points admits a flat deformation lifting specified local ring deformations over Artinian algebras”. Eight hits, only smoothness definitions, smooth-chart results and algebra smoothness/flatness; no deformation lifting theorem.
- Loogle: “Algebra.TensorProduct.map, Algebra.EssFiniteType, IsLocalRing”. Zero hits.
- Mathlib grep: “isolated|deformation”, subdirectory AlgebraicGeometry. Zero wrapper hits.
- LeanSearch: “An affine scheme with isolated singularities admits compatible prescribed local flat deformations over an Artinian local algebra surjection”. Eight hits: scheme constructors, Artinian schemes and affine flatness; no lifting theorem.
- Direct rg over lean/WeilConjectures and lean/Sheaf: `isolated.deformation|IsolatedDeformation|affine.*deformation|AffineDeformation`. No theorem matching this statement. Nearby AffineSchemeDeformationComparison is first-order comparison; IsolatedCurveFormalLifting cites this item as a prerequisite.
- Direct rg for the item id in lean/WeilConjectures: no hits. Direct rg for `affine.*isolated|isolated.*affine` in dag/lean_names_upstream.json and the final declaration name in both Lean trees and Mathlib: no hits.

Validation: the prescribed scompile.py compiled this file in both sandbox
and library module forms cleanly (3.4 s and 2.2 s). No diagnostics or
non-sorry warnings. Every line is at most 100 columns.

## Second reading by Q125

A separate manual pass compared the completed signature against the node
and source. No additional agent was started, as instructed; the delivery
still receives the maintainer's independent review. This pass checked the
coefficient surjection, augmentation equations, finite-dimensionality and
locality; the distinct closed-point family and smooth-open condition;
the affine flat deformation and its actual pullback marking; and the
local flat essentially-finite-type algebras with their A-linear reductions.
It checked all three parts of the conclusion and expanded the meanings
of both pullback squares, both scalar equations, and the final tensor
compatibility equation. No mismatch was found and no statement changed.
In particular there is no unmarked-lift weakening, no assumption that the
points are k-rational, and no nonempty-index restriction. The final
conclusion's map has the correct contravariant stalk direction, from
Y' at l(j(p_i)) to Y at j(p_i).
