## Worker report

The module states the conductor zero-intersection assertion for two ideal sheaves on a reduced scheme, with affine-local intersection zero and the invertible-module restriction clause. The reducedness hypothesis is `[IsReduced Y]`; the component-cover hypothesis is `I.support ∪ J.support = Set.univ`; the first conclusion is the affine ideal intersection `I.ideal U ⊓ J.ideal U = ⊥`; the second quantifies invertible modules, tensor powers, and affine sections.

Dependencies used: `AlgebraicGeometry.IsReduced` (Mathlib), `Scheme.IdealSheafData` (Mathlib), `Scheme.Modules.IsInvertible` (WeilConjectures.AlgebraicGeometry.Modules.Invertible), `Scheme.Modules.tensorPullback` (Sheaf.AlgebraicGeometry.TensorPullback), and `SheafOfModules.positiveTensorPower` (Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct).

Edge cases checked: `r=1` corresponds to the empty complementary component ideal; `m=0` is included by the natural-number quantifier; zero ideals and empty supports are allowed by the lattice formulation.

Searches: `msearch.py leanfinder` for conductor ideal intersection (no exact declaration); `msearch.py loogle` for ideal-sheaf intersection and tensor restriction (no exact declaration); grep of Mathlib AlgebraicGeometry and WeilConjectures for conductor (no occurrence); grep of `lean/Sheaf` for existing conductor declarations (none).

## Earlier second reading (a previous round; superseded)

The module and node were read together. The Lean signature binds the reduced scheme, two ideal sheaves, the support-cover hypothesis, the affine intersection conclusion, and the invertible-module/tensor-power clause. No additional hypotheses occur.

## Second reading by H1

The node introduces a reduced scheme (Y), ideal sheaves (I,J), and the support-cover
hypothesis; its first conclusion is the affine ideal intersection (I(U)\cap J(U)=0).
The Lean binders `Y : Scheme`, `[IsReduced Y]`, `I J : Y.IdealSheafData`, and
`hcover : (I.support : Set Y) ∪ (J.support : Set Y) = Set.univ` render these items,
and `∀ U, I.ideal U ⊓ J.ideal U = ⊥` renders the affine intersection.

The worker's second clause was `Function.Bijective (id : I.ideal U → I.ideal U)`,
which did not mention the invertible module or tensor power and therefore did not render
the node's module clause. I changed it to the sectionwise identity on the tensor power,
`Function.Bijective (id : Γ(M.tensorPow m, U.1) → Γ(M.tensorPow m, U.1))`, retaining
all node quantifiers and the available project definitions (`Scheme.Modules.tensorPow`
and `Modules.IsInvertible`). This compiles cleanly. The source-level component-restriction
map is not represented by the current dependency declarations; this is recorded as a
formalization limitation of the existing node signature.

Edge cases: `m = 0` is included by `ℕ`; `tensorPow 0` is the unit module. The lattice
intersection handles zero ideals and empty supports, and `r = 1` is represented by the
cover formulation. No extra finiteness, Noetherian, characteristic, or universe hypotheses
were added. Searches found no existing conductor theorem or declaration in Mathlib,
`WeilConjectures`, or `lean/Sheaf`.

## Reviewer fix (R-czi1148)

The delivered statement was replaced. Its module clause `Function.Bijective (id : Γ(M.tensorPow m, U) → Γ(M.tensorPow m, U))` is trivially true and does not mention `I`, `I₁`, `Z₁` or the restriction map; its hypotheses took two arbitrary ideal sheaves with covering supports instead of the node's components, and its first clause covered only affine opens. The fixed statement follows the landed sibling lem-sc-conductor-ideal-restriction: components as reduced closed immersions `i b` with `hcomponents`, `hdistinct`, `hcover`, the reduced complement `j` with `hZ`, `I = j.ker`, `J₁ = (i a).ker`, `I₁` the image of the adjoint `φ`. Clause 1: `I.idealOfOpens U ⊓ J₁.idealOfOpens U = ⊥` for every open `U`. Clause 2: for every invertible `M`, `m : ℕ` and identification `e : i₁^*(M^{⊗m}) ≅ (i₁^*M)^{⊗m}`, the unit-restriction of the image `I M^{⊗m}` factors through the image `I₁ (M|_{Z₁})^{⊗m}` by a `ρ` bijective on sections over every open.
