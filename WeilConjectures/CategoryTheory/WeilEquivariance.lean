/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Weil equivariance of adjunction data and of duals

Let `G : C ⥤ C` be an endofunctor; in the `ℓ`-adic formalism `C = D(X, Λ)` and `G = Lg^*` is the
pullback along the geometric Frobenius `g` of `X`. A *Weil datum* on an object `M` is a morphism
`φ : G M ⟶ M`, and `u : M ⟶ N` is *equivariant* for data `φ_M`, `φ_N` if
`G u ≫ φ_N = φ_M ≫ u`. This file proves two formal equivariance statements of blueprint
`cor-coef-verdier-weil-equivariance`.

**Adjunction data.** Let `L ⊣ R` be adjunctions `C ⇄ D` and `E ⇄ F` (`L₁ ⊣ R₁`, `L₂ ⊣ R₂`), and
let `e : L₁ ⋙ H ≅ G ⋙ L₂` be an isomorphism (in the geometric case the compact-support base
change `Ex_! : Lh^* Rf_! ≅ Rf_! Lg^*`). Its *right adjoint exchange* is the mate
`R₁ ⋙ G ⟶ H ⋙ R₂` of `e⁻¹` (`CategoryTheory.Adjunction.rightAdjointExchange`). Transporting
Weil data through `L` by `e` and through `R` by the right adjoint exchange, the unit and the
counit of the adjunction are equivariant
(`CategoryTheory.Adjunction.isWeilEquivariant_counit`,
`CategoryTheory.Adjunction.isWeilEquivariant_unit`).

**Duals.** Let `C` be monoidal closed and `G` a monoidal endofunctor. A Weil datum `φ_ω` on an
object `ω` and an invertible Weil datum `φ_A` on `A` give the *dual Weil datum* on `[A, ω]`
(`CategoryTheory.MonoidalClosed.dualWeilDatum`), the tensor-hom adjoint of
```
A ⊗ G [A, ω] ──φ_A⁻¹ ⊗ 1──▶ G A ⊗ G [A, ω] ──μ──▶ G (A ⊗ [A, ω]) ──G ev──▶ G ω ──φ_ω──▶ ω;
```
for an autoequivalence `G` it is `G [A, ω] ≅ [G A, G ω] ──[G A, φ_ω]──▶ [G A, ω] ──[φ_A⁻¹, ω]──▶
[A, ω]`, the first map being the internal-hom comparison of `G`. The evaluation
`A ⊗ [A, ω] ⟶ ω` is equivariant (`CategoryTheory.MonoidalClosed.isWeilEquivariant_ev`), and the
tensor-hom adjoint
`B ⟶ [A, ω]` of an equivariant pairing `A ⊗ B ⟶ ω` is equivariant
(`CategoryTheory.MonoidalClosed.isWeilEquivariant_curry`). No integral lattice of `φ_A` is
needed: the construction only uses `φ_A` and its inverse.

**Biduality.** If moreover `C` is braided and `G` is a braided functor, the braiding is
equivariant (`CategoryTheory.MonoidalClosed.isWeilEquivariant_braiding`), and so is the
double-dual map `A ⟶ [[A, ω], ω]` for `φ_A` and the dual of the dual Weil datum, provided the
dual Weil datum is invertible (`CategoryTheory.MonoidalClosed.isWeilEquivariant_toIhomIhom`).
-/

@[expose] public section

namespace CategoryTheory

open Category MonoidalCategory CategoryTheory.Functor

/-- A morphism `u : M ⟶ N` is *equivariant* for Weil data `φ_M : G M ⟶ M` and `φ_N : G N ⟶ N`
if `G u ≫ φ_N = φ_M ≫ u`. -/
def IsWeilEquivariant {C : Type*} [Category* C] (G : C ⥤ C) {M N : C} (φM : G.obj M ⟶ M)
    (φN : G.obj N ⟶ N) (u : M ⟶ N) : Prop :=
  G.map u ≫ φN = φM ≫ u

section Transport

variable {C D : Type*} [Category* C] [Category* D] {G : C ⥤ C} {G' : D ⥤ D} (T : C ⥤ D)
  (c : G ⋙ T ≅ T ⋙ G')

end Transport

namespace Adjunction

section Mate

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  {G : C ⥤ E} {H : D ⥤ F} (e : L₁ ⋙ H ≅ G ⋙ L₂)

/-- The *right adjoint exchange* `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `e : L₁ ⋙ H ≅ G ⋙ L₂`
between adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`: the mate of `e⁻¹`. For the compact-support base
change `Ex_! : Lh^* Rf_! ≅ Rf'_! Lg^*` it is the exceptional base change
`Lg^* Rf^! ⟶ Rf'^! Lh^*`. -/
noncomputable def rightAdjointExchange : R₁ ⋙ G ⟶ H ⋙ R₂ :=
  (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv)).natTrans

/-- The right adjoint exchange is characterised by its compatibility with the counits:
```
H L₁ R₁ d ──e──▶ L₂ G R₁ d ──L₂ (exchange)──▶ L₂ R₂ H d ──ε₂──▶ H d
```
is `H ε₁`. -/
@[reassoc]
lemma hom_app_comp_map_rightAdjointExchange_app_comp_counit (d : D) :
    e.hom.app (R₁.obj d) ≫ L₂.map ((rightAdjointExchange adj₁ adj₂ e).app d) ≫
        adj₂.counit.app (H.obj d) = H.map (adj₁.counit.app d) := by
  have h := mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv) d
  calc e.hom.app (R₁.obj d) ≫ L₂.map ((rightAdjointExchange adj₁ adj₂ e).app d) ≫
        adj₂.counit.app (H.obj d)
      = e.hom.app (R₁.obj d) ≫ e.inv.app (R₁.obj d) ≫ H.map (adj₁.counit.app d) :=
        congrArg (e.hom.app (R₁.obj d) ≫ ·) h
    _ = H.map (adj₁.counit.app d) := by simp

/-- The right adjoint exchange is compatible with the units:
`G η₁ ≫ (exchange)_{L₁ c} = η₂ ≫ R₂ (e⁻¹)`. -/
@[reassoc]
lemma map_unit_app_comp_rightAdjointExchange_app (c : C) :
    G.map (adj₁.unit.app c) ≫ (rightAdjointExchange adj₁ adj₂ e).app (L₁.obj c) =
      adj₂.unit.app (G.obj c) ≫ R₂.map (e.inv.app c) :=
  unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv) c

end Mate

section Weil

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {G : C ⥤ C} {H : D ⥤ D} (e : L ⋙ H ≅ G ⋙ L)

/-- The Weil datum `H L c ──e──▶ L G c ──L φ──▶ L c` on `L c` transported from a datum
`φ : G c ⟶ c` along `e : L ⋙ H ≅ G ⋙ L` (for `L = Rf_!` and `e = Ex_!` this is the
compact-support transport). -/
noncomputable def leftWeilDatum {c : C} (φ : G.obj c ⟶ c) : H.obj (L.obj c) ⟶ L.obj c :=
  e.hom.app c ≫ L.map φ

/-- The Weil datum `G R d ──exchange──▶ R H d ──R ψ──▶ R d` on `R d` transported from a datum
`ψ : H d ⟶ d` along the right adjoint exchange of `e`. -/
noncomputable def rightWeilDatum {d : D} (ψ : H.obj d ⟶ d) : G.obj (R.obj d) ⟶ R.obj d :=
  (rightAdjointExchange adj adj e).app d ≫ R.map ψ

/-- **The counit is Weil equivariant**: for a Weil datum `ψ` on `d`, the counit
`L R d ⟶ d` is equivariant for the transported datum on `L R d` and `ψ`. -/
lemma isWeilEquivariant_counit {d : D} (ψ : H.obj d ⟶ d) :
    IsWeilEquivariant H (leftWeilDatum e (rightWeilDatum adj e ψ)) ψ (adj.counit.app d) := by
  have h := adj.counit.naturality ψ
  dsimp at h
  rw [IsWeilEquivariant, leftWeilDatum, rightWeilDatum, Functor.map_comp, Category.assoc,
    Category.assoc, h,
    hom_app_comp_map_rightAdjointExchange_app_comp_counit_assoc]

end Weil

end Adjunction

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] (G : C ⥤ C)
  [G.Monoidal]

end MonoidalClosed

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] (G : C ⥤ C)
  [G.Braided]

end MonoidalClosed

end CategoryTheory
