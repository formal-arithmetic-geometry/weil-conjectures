module
public import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- The tensor-total Cech sequence is short exact in the right coefficient.
Source: Stacks Project, Varieties, Tag 0BED, the coefficient diagram following
equation-kunneth-on-cech, applied in the right variable.
(blueprint: lem-sc-picard-external-right-cech-exact-tensor).

Proof: In Cech degree q, every tuple has q+1 entries, so its intersection
is nonempty as a family of opens. Repeated use of the affine diagonal criterion
makes that intersection affine. Sections of S there are short exact: sections
preserve kernels, and quasi-coherent affine vanishing of H^1 of S.X₁ gives
surjectivity onto sections of S.X₃. Restriction of scalars to k preserves this.
The finite product over the tuples is therefore short exact, proving degreewise
short exactness of the scalar Cech sequence. Fix a total degree n. Tensor each
sequence in degree q with the fixed k-vector space of F-cochains in degree p,
for p+q=n. All k-vector spaces are flat, so this preserves short exactness.
The finite direct sum over these pairs remains short exact. These are exactly
the terms and maps of picardRightTensorCechFunctor, by the natural tensor-total
construction. Extension from natural to integer degrees keeps these terms and
puts the zero sequence in negative degrees. Degreewise short exactness implies
short exactness of complexes. Empty index types give empty products (zero
modules) in every Cech degree; zero coefficients also give zero terms. Thus
neither a cover hypothesis nor a nonemptiness assumption is needed. -/
theorem picardExternal_right_cech_tensor_exact
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (picardRightTensorCechFunctor f g U V F)).ShortExact := by sorry
end AlgebraicGeometry.Scheme.Modules
