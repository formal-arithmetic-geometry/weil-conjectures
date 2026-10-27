module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import Sheaf.AlgebraicGeometry.AbelianVariety.RationalHom

/-! # Rational homomorphisms of abelian varieties

Source: Milne, Abelian Varieties, I §10, pp.45–46, and §14, p.61;
componentwise Tate action in I §10 (blueprint: def-sfb-abelian-rational-tate-action).

The homomorphism group is Mathlib's group of morphisms of group objects, written
additively. Rationalization and the maps on it use the actual tensor product.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry.IsAbelianVariety

variable {k : Type u} [Field k]
variable (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
  [IsAbelianVariety A] [IsAbelianVariety B]

variable {A B} {C : Over (Spec (.of k))} [GrpObj C] [IsAbelianVariety C]

/-- Precomposition of integral group homomorphisms, with its additive structure
supplied by Yoneda. Source: Milne AV I §10 (blueprint: def-sfb-abelian-rational-tate-action). -/
def abelianHomPrecomp (f : A ⟶ B) [IsMonHom f] : abelianHom B C →+ abelianHom A C :=
  ((yonedaGrpObj (Grp.mk C)).map (Grp.ofHom f).op).hom.toAdditive

/-- Postcomposition of integral group homomorphisms.
Source: Milne AV I §10 (blueprint: def-sfb-abelian-rational-tate-action). -/
def abelianHomPostcomp (f : B ⟶ C) [IsMonHom f] : abelianHom A B →+ abelianHom A C :=
  (IsMonHom.monoidHom (Grp.ofHom f) (Grp.mk A)).toAdditive

/-- Precomposition on rational homomorphisms is scalar extension of precomposition.
Source: Milne AV I §14, p.61 (blueprint: def-sfb-abelian-rational-tate-action). -/
def rationalHomPrecomp (f : A ⟶ B) [IsMonHom f] :
    abelianRationalHom B C →ₗ[ℚ] abelianRationalHom A C :=
  (abelianHomPrecomp (C := C) f).toIntLinearMap.baseChange ℚ

/-- Postcomposition on rational homomorphisms is scalar extension of postcomposition.
Source: Milne AV I §14, p.61 (blueprint: def-sfb-abelian-rational-tate-action). -/
def rationalHomPostcomp (f : B ⟶ C) [IsMonHom f] :
    abelianRationalHom A B →ₗ[ℚ] abelianRationalHom A C :=
  (abelianHomPostcomp (A := A) f).toIntLinearMap.baseChange ℚ

/-- The additive action of integral homomorphisms on integral Tate modules, defined
coordinatewise. Source: Milne AV I §10 (blueprint: def-sfb-abelian-rational-tate-action). -/
def abelianHomTateMap (ℓ : ℕ) [Fact ℓ.Prime] :
    abelianHom A B →+ (tateModule ℓ A →ₗ[ℤ_[ℓ]] tateModule ℓ B) where
  toFun f := tateModuleMap f.toMul.hom.hom
  map_zero' := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext n
    change Additive.ofMul (_ ≫ (1 : A ⟶ B)) = 0
    simp
  map_add' f g := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext n
    change Additive.ofMul (_ ≫ (f.toMul.hom.hom * g.toMul.hom.hom)) = _
    rw [MonObj.comp_mul]
    rfl

/-- The additive action of integral homomorphisms on rational Tate modules.
Source: Milne AV I §10 (blueprint: def-sfb-abelian-rational-tate-action). -/
def abelianHomRationalTateMap (ℓ : ℕ) [Fact ℓ.Prime] :
    abelianHom A B →+ (rationalTateModule ℓ A →ₗ[ℚ_[ℓ]] rationalTateModule ℓ B) :=
  (LinearMap.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] (tateModule ℓ A) (tateModule ℓ B)).toAddMonoidHom.comp
    (abelianHomTateMap (A := A) (B := B) ℓ)

/-- Rational homomorphisms act by the unique rational-linear extension of the
componentwise Tate action: `q ⊗ f` acts by `q V_ℓ(f)`.
Source: Milne AV I §10 and §14, p.61 (blueprint: def-sfb-abelian-rational-tate-action). -/
def rationalHomTateMap (ℓ : ℕ) [Fact ℓ.Prime] :
    abelianRationalHom A B →ₗ[ℤ] (rationalTateModule ℓ A →ₗ[ℚ_[ℓ]] rationalTateModule ℓ B) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ
      (fun (q : ℚ) (f : abelianHom A B) ↦ (q : ℚ_[ℓ]) • abelianHomRationalTateMap ℓ f)
      (fun q r f ↦ by simp [add_smul])
      (fun n q f ↦ by
        simp only [zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast, mul_smul,
          Int.cast_smul_eq_zsmul])
      (fun q f g ↦ by rw [map_add, smul_add])
      (fun n q f ↦ by rw [map_zsmul]; exact smul_comm (q : ℚ_[ℓ]) n _))

end AlgebraicGeometry.IsAbelianVariety
