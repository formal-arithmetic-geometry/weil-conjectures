module

public import Sheaf.AlgebraicGeometry.AbelianVariety.Simple
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import Sheaf.AlgebraicGeometry.AbelianVariety.MultipleRetraction
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import Sheaf.AlgebraicGeometry.AbelianVariety.HomImageDimension
import Sheaf.AlgebraicGeometry.AbelianFiniteProduct
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Sheaf.AlgebraicGeometry.AbelianVariety.KernelAbelianPart
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.FiniteGroupSchemeOrderAnnihilator

/-! # Simple factors and quasi-inverse isogenies

Source: Milne, Abelian Varieties, Chapter I, Proposition 10.1 and the discussion after
Remark 10.2, printed pp.42-43; Remark 8.6, printed p.36.
(blueprint: lem-sfb-simple-isogeny-decomposition)

Multiplication by `n` is `𝟙 X ^ n`; the zero group-scheme map is `1` in the pointwise
group of scheme morphisms. Projection homomorphism conditions specify the componentwise
group law on the finite product, including the empty product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- Every abelian variety is isogenous over its ground field to a finite product of
simple abelian varieties. The family may be empty, giving the zero abelian variety.

Source: Milne, Abelian Varieties, Chapter I, Proposition 10.1, printed p.42.
(blueprint: lem-sfb-simple-isogeny-decomposition)

Proof:
1. For a nonzero proper abelian subgroup i : B → A, use
   lem-sfb-abelian-inclusion-multiple-retraction to find n > 0 and r with ri = [n].
   By lem-sc-av-commutative the homomorphism q = [n] - ir has qi = 0 and rq = 0.
   By lem-sfb-abelian-hom-image-dimension its scheme-theoretic image C is abelian.
   The ideal description of that image shows that C lies in ker r scheme-theoretically.
2. The addition map B × C → A is surjective because [n] = ir + q factors through it
   and lem-sc-mult-n-isogeny makes [n] surjective. Its kernel identifies with B ×_A C
   by changing the sign of the second coordinate. This intersection is a closed subscheme
   of B[n], hence finite by lem-sc-mult-n-isogeny. Thus addition is an isogeny.
3. By lem-sfb-abelian-hom-image-dimension and lem-sfb-abelian-finite-product,
   dim A = dim B + dim C. Both factors therefore have smaller dimension.
4. Induct strongly on dimension. A zero-dimensional abelian variety is the empty product
   by lem-sfb-abelian-finite-product. A simple positive-dimensional variety is its own
   single factor; otherwise apply the complement construction and induction to B and C.
5. The product of the resulting isogenies, followed by addition, is an isogeny:
   lem-sc-isogeny-degree makes the factor maps finite flat, and
   lem-trf-finite-radicial-basechange preserves finiteness under products and composition.
   Surjectivity is preserved under base change and composition, and the kernel is the
   base change of the finite composite along the identity section (def-sc-isogeny).
-/
theorem IsAbelianVariety.exists_simple_isogeny_decomposition
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] :
    ∃ (r : ℕ) (C : Fin r → Over (Spec (.of k)))
      (_ : ∀ i, GrpObj (C i)) (_ : ∀ i, IsAbelianVariety (C i)),
      (∀ i, IsSimpleAbelianVariety (C i)) ∧
        ∃ (_ : GrpObj (piObj C)), (∀ i, IsMonHom (Pi.π C i)) ∧
          ∃ (f : piObj C ⟶ A), IsIsogeny f := by
  sorry

/-- A nonzero homomorphism between simple abelian varieties over the ground field is an
isogeny. Nonzero means different from the constant identity-section morphism.

Source: Milne, Abelian Varieties, Chapter I, the discussion after Remark 10.2, printed p.43.
(blueprint: lem-sfb-simple-isogeny-decomposition)

Proof:
1. By lem-sfb-abelian-hom-image-dimension the image I is a closed abelian subgroup of Y.
   If it had dimension zero, lem-sfb-abelian-finite-product would make it the zero group,
   contradicting f ≠ 0. Simplicity forces dim I = dim Y. By
   lem-sc-abelian-variety-characterization, Y is integral, so a closed subvariety of full
   dimension is all of Y. Thus f is surjective.
2. By lem-sfb-abelian-kernel-abelian-part the kernel contains a closed abelian subgroup D
   with dim D = dim ker f. Simplicity of X forces this dimension to be zero or dim X.
   In the latter case integrality gives D = X, contradicting nonzeroness. The kernel is
   therefore zero-dimensional and finite by the same kernel lemma, even if nonreduced.
   Surjectivity and this finite kernel give def-sc-isogeny.
-/
theorem isIsogeny_of_nonzero_of_simple
    {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [GrpObj X] [GrpObj Y] [IsAbelianVariety X] [IsAbelianVariety Y]
    (hX : IsSimpleAbelianVariety X) (hY : IsSimpleAbelianVariety Y)
    (f : X ⟶ Y) [IsMonHom f] (hf : f ≠ 1) : IsIsogeny f := by
  sorry

/-- Every isogeny has an isogeny in the opposite direction whose two composites are
multiplication by the same positive integer.

Source: Milne, Abelian Varieties, Chapter I, Remark 8.6, printed p.36.
(blueprint: lem-sfb-simple-isogeny-decomposition)

Proof:
1. By lem-sc-isogeny-degree, f is finite flat, and hence an fpqc cover since it is
   surjective. Its finite commutative kernel K is killed by its positive order n by
   lem-sfb-finite-group-scheme-order-annihilator and lem-sc-av-commutative.
2. The group laws identify X ×_Y X with X × K via (x,t) ↦ (x,x+t), with inverse
   (x,x') ↦ (x,x'-x). Because [n] kills K scheme-theoretically, the two pullbacks of
   [n]_X agree. By lem-weil-pbc-fpqc-representable-descent this descends uniquely to
   g : Y → X with gf = [n]_X. The structure map to Spec k descends uniquely too,
   so g is over k.
3. Pull back the multiplication identity for g along f × f. It becomes the homomorphism
   identity for [n]. Cancel the two fpqc base changes of f using descent uniqueness and
   lem-galois-fpqc-covering-base-change. Identity and inverse compatibility follow by
   the same cancellation, so g is a group-scheme homomorphism.
4. The identity (fg)f = f[n]_X = [n]_Y f descends uniquely to fg = [n]_Y.
   Since gf = [n]_X and [n]_X is surjective (lem-sc-mult-n-isogeny), g is surjective.
   Its kernel is a closed subgroup scheme of the finite group Y[n], hence finite.
   Thus g is an isogeny by def-sc-isogeny and the two identities use the same n > 0.
-/
theorem IsIsogeny.exists_isogeny_quasi_inverse
    {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [GrpObj X] [GrpObj Y] [IsAbelianVariety X] [IsAbelianVariety Y]
    (f : X ⟶ Y) [IsIsogeny f] :
    ∃ (g : Y ⟶ X), IsIsogeny g ∧
      ∃ (n : ℕ), 0 < n ∧ f ≫ g = 𝟙 X ^ n ∧ g ≫ f = 𝟙 Y ^ n := by
  sorry

end AlgebraicGeometry
