/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine bijectivity of normalized coefficient comparisons

Source: Stacks Project, Tags 02KE, 01I9 and 01IA.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A coefficient comparison morphism with the unit formula is bijective on affine opens.
This is a single-open statement: no tuples, face maps, or gluing are involved.
Source: Stacks Project, Tag 02KG (Lemma 30.5.1); Tags 01I9 and 01IA.
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-bijective).

Proof: Write A = Gamma(U,O), D = Gamma(Z,O), N = Gamma(Z,F), and
R = Gamma(B,O). The affine intersection base-change theorem shows that
W -> T' is affine. Hence W intersect f' inverse image B is affine, and it
is Z times_U B by the cartesian square and the stated equality for W.
The affine pullback section formula identifies the sections of M there
with (R tensor_A D) tensor_D N = R tensor_A N. The source is the pullback
to B of the associated A-module N, so the same formula identifies its
sections with R tensor_A N. Both identifications send 1 tensor s to the
restriction of the displayed generator section. Naturality of q under
B -> top and its linearity over Gamma(B,O) therefore identify q on every
r tensor s with the identity under these presentations. Such pure tensors
generate the tensor product, so q is conjugate to an additive equivalence
and is bijective. The argument includes empty Z and empty B, with zero
modules. It uses neither flatness nor any covering assumption. -/
theorem coefficientComparison_affine_bijective {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) :
    let G := (F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat
    let H := ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) ⋙
      tilde.functor Γ(U.toScheme, ⊤) ⋙
      Modules.pullback U.toScheme.toSpecΓ ⋙ Modules.pullback g
    let M := (Modules.pullback g').obj F
    ∀ q : H.obj (G.obj (op Z)) ⟶
        (pushforward (W.ι ≫ f')).obj (M.restrict W.ι),
      (∀ s : Γ(F.restrict (f ⁻¹ᵁ U).ι, Z),
        (coefficientSupportIso f' M W ⊤).hom
          (q.app ⊤ (coefficientGenerator g _ s)) =
        M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ ⊤ ≤ W)).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s)) →
      ∀ B : T'.Opens, IsAffineOpen B → Function.Bijective (q.app B) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
