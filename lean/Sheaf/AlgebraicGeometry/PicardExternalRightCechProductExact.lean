module
public import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- The product-cover Cech sequence is short exact in the right coefficient.
Source: Stacks Project, Varieties, Tag 0BED, the coefficient diagram following
equation-kunneth-on-cech, applied in the right variable.
(blueprint: lem-sc-picard-external-right-cech-exact-product).

Proof: A tuple of pairs in degree n specifies a nonempty finite intersection A
of the U opens and B of the V opens. Both are affine by the affine diagonal
criterion, and the product-cover intersection is A times B over Spec k.
Write A=Spec R and B=Spec T. If M is the R-module of F-sections on A and Nᵢ
is the T-module of S.Xᵢ-sections on B, the affine pullback and tensor formulas
identify the external coefficient sections on this product with M tensor_k Nᵢ.
These identifications are natural in S, so the coefficient maps become tensor
products of the section maps. The sequence of Nᵢ is short exact: sections
preserve kernels, and affine quasi-coherent vanishing of H^1 of S.X₁ gives
surjectivity. Tensoring with M preserves it because k is a field. Taking the
finite product over all degree-n tuples proves degreewise short exactness of
the product-cover Cech sequence. Extension by zero places zero sequences in
negative degrees; degreewise short exactness then gives short exactness of
complexes. Empty index families have zero Cech terms, and zero coefficients
likewise cause no exception. No cover condition or flatness over O_X is used. -/
theorem picardExternal_right_cech_product_exact
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (picardRightProductCechFunctor f g U V F)).ShortExact := by sorry
end AlgebraicGeometry.Scheme.Modules
