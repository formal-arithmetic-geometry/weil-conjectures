/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange

/-!
# Transposing coefficient comparisons along a left adjoint of restriction of scalars

Let `Ψ_B ⊣ Res_B` and `Ψ_A ⊣ Res_A` be adjunctions (think: the derived extension of scalars
along a ring morphism `ρ : Λ →+* Λ'`, left adjoint to the restriction of scalars, over two
schemes), and `F : B ⥤ A`, `F' : B' ⥤ A'` functors with a coefficient comparison
`ι : Res_B ⋙ F ≅ F' ⋙ Res_A`. The *transpose* of `ι` is the mate
`F ⋙ Ψ_A ⟶ Ψ_B ⋙ F'` (`AlgebraicGeometry.Etale.coeffMate`), the comparison of `Ψ` with `F`.

This file develops the calculus of these transposes:

* they are natural with respect to transformations compatible with the coefficient comparisons
  (`AlgebraicGeometry.Etale.CoeffCompatible.map_app_comp_coeffMate_app`), compatible with the
  pasting of squares (`AlgebraicGeometry.Etale.coeffMate_pasteTwoSquaresIso_app`) and trivial for
  the identity (`AlgebraicGeometry.Etale.coeffMate_unitors_app`);
* when the transpose `β` is invertible and `F ⊣ U`, `F' ⊣ U'`, the mate of `β⁻¹` is a comparison
  `U ⋙ Ψ_B ⟶ Ψ_A ⋙ U'` of `Ψ` with the right adjoints
  (`AlgebraicGeometry.Etale.coeffUpperMate`), and these are compatible with the conjugates of
  compatible composition isomorphisms
  (`AlgebraicGeometry.Etale.map_conjugateIsoEquiv_comp_coeffUpperMate`),
  with the right adjoints of compatible identifications with the identity
  (`AlgebraicGeometry.Etale.map_rightAdjointUniq_hom_app_eq`), and with the mates of compatible
  exchange maps (`AlgebraicGeometry.Etale.coeffMate_app_comp_map_coeffUpperMate_app_comp`);
* the transpose of the mate of a coefficient comparison of left adjoints is the mate of the
  transpose (`AlgebraicGeometry.Etale.coeffMate_mateEquiv`).

Equalities of morphisms out of `Ψ M` are checked on their transposes `M ⟶ Res N`.
-/

@[expose] public section

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Transpose

variable {B B' A A' C C' : Type*} [Category B] [Category B'] [Category A] [Category A']
  [Category C] [Category C'] {RB : B' ⥤ B} {RA : A' ⥤ A} {RC : C' ⥤ C} {ΨB : B ⥤ B'}
  {ΨA : A ⥤ A'} {ΨC : C ⥤ C'} (adjB : ΨB ⊣ RB) (adjA : ΨA ⊣ RA) (adjC : ΨC ⊣ RC)

/-- The *transpose* `F ⋙ Ψ_A ⟶ Ψ_B ⋙ F'` of a coefficient comparison
`ι : Res_B ⋙ F ≅ F' ⋙ Res_A` along the adjunctions `Ψ_B ⊣ Res_B` and `Ψ_A ⊣ Res_A`: the mate of
`ι`. -/
noncomputable def coeffMate {F : B ⥤ A} {F' : B' ⥤ A'} (ι : RB ⋙ F ≅ F' ⋙ RA) :
    F ⋙ ΨA ⟶ ΨB ⋙ F' :=
  ((mateEquiv adjB adjA).symm ι.hom).natTrans

/-- The defining property of the transpose: `F(M ⟶ Res Ψ M) ≫ ι = (F M ⟶ Res Ψ F M) ≫ Res β`. -/
@[reassoc]
lemma unit_app_comp_map_coeffMate_app {F : B ⥤ A} {F' : B' ⥤ A'} (ι : RB ⋙ F ≅ F' ⋙ RA)
    (M : B) :
    adjA.unit.app (F.obj M) ≫ RA.map ((coeffMate adjB adjA ι).app M) =
      F.map (adjB.unit.app M) ≫ ι.hom.app (ΨB.obj M) :=
  (unit_mateEquiv_symm adjB adjA ι.hom M).symm

variable {adjA} in
/-- Morphisms out of `Ψ_A M` are determined by their transposes `M ⟶ Res_A N`. -/
lemma hom_ext_of_adjunction {M : A} {N : A'} {f g : ΨA.obj M ⟶ N}
    (h : adjA.unit.app M ≫ RA.map f = adjA.unit.app M ≫ RA.map g) : f = g :=
  (adjA.homEquiv M N).injective (by rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit])

/-- **The transposes are natural** with respect to transformations `α : F ⟶ G`, `α' : F' ⟶ G'`
compatible with the coefficient comparisons. -/
@[reassoc]
lemma CoeffCompatible.map_app_comp_coeffMate_app {F G : B ⥤ A} {F' G' : B' ⥤ A'}
    {ιF : RB ⋙ F ≅ F' ⋙ RA} {ιG : RB ⋙ G ≅ G' ⋙ RA} {α : F ⟶ G} {α' : F' ⟶ G'}
    (h : CoeffCompatible ιF ιG α α') (M : B) :
    ΨA.map (α.app M) ≫ (coeffMate adjB adjA ιG).app M =
      (coeffMate adjB adjA ιF).app M ≫ α'.app (ΨB.obj M) := by
  apply hom_ext_of_adjunction (adjA := adjA)
  have hu := adjA.unit.naturality (α.app M)
  have hn := α.naturality (adjB.unit.app M)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hu hn
  rw [Functor.map_comp, ← reassoc_of% hu, unit_app_comp_map_coeffMate_app, Functor.map_comp,
    unit_app_comp_map_coeffMate_app_assoc, h (ΨB.obj M), reassoc_of% hn]

/-- **The transpose of a pasted square** is the pasting of the transposes. -/
lemma coeffMate_pasteTwoSquaresIso_app {F : B ⥤ A} {G : A ⥤ C} {F' : B' ⥤ A'} {G' : A' ⥤ C'}
    (ιF : RB ⋙ F ≅ F' ⋙ RA) (ιG : RA ⋙ G ≅ G' ⋙ RC) (M : B) :
    (coeffMate adjB adjC (pasteTwoSquaresIso ιF ιG)).app M =
      (coeffMate adjA adjC ιG).app (F.obj M) ≫ G'.map ((coeffMate adjB adjA ιF).app M) := by
  apply hom_ext_of_adjunction (adjA := adjC)
  have hn := ιG.hom.naturality ((coeffMate adjB adjA ιF).app M)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [unit_app_comp_map_coeffMate_app, Functor.map_comp]
  simp only [Functor.comp_obj, Functor.comp_map]
  rw [unit_app_comp_map_coeffMate_app_assoc, ← hn, ← G.map_comp_assoc,
    unit_app_comp_map_coeffMate_app, pasteTwoSquaresIso_hom_app, G.map_comp, Category.assoc]

/-- The transpose of the unitor square `Res ⋙ 𝟭 ≅ 𝟭 ⋙ Res` is the identity. -/
lemma coeffMate_unitors_app (M : B) :
    (coeffMate adjB adjB (Functor.rightUnitor RB ≪≫ (Functor.leftUnitor RB).symm)).app M =
      𝟙 _ := by
  apply hom_ext_of_adjunction (adjA := adjB)
  have := unit_app_comp_map_coeffMate_app adjB adjB
    (Functor.rightUnitor RB ≪≫ (Functor.leftUnitor RB).symm) M
  simpa using this

/-- The transpose of an isomorphism `δ : H ≅ 𝟭` compatible with the unitor squares:
`Ψ δ = β ≫ δ'`. -/
lemma map_hom_app_eq_coeffMate_app_comp {H : B ⥤ B} {H' : B' ⥤ B'} {ιH : RB ⋙ H ≅ H' ⋙ RB}
    {δ : H ≅ 𝟭 B} {δ' : H' ≅ 𝟭 B'}
    (h : CoeffCompatible ιH (Functor.rightUnitor RB ≪≫ (Functor.leftUnitor RB).symm)
      δ.hom δ'.hom) (M : B) :
    ΨB.map (δ.hom.app M) = (coeffMate adjB adjB ιH).app M ≫ δ'.hom.app (ΨB.obj M) := by
  have := h.map_app_comp_coeffMate_app adjB adjB M
  rw [coeffMate_unitors_app] at this
  simpa using this

/-- The transpose of a coefficient comparison of a functor isomorphic to the identity, compatibly
with the unitor squares, is an isomorphism. -/
lemma isIso_coeffMate_of_coeffCompatible_unitors {H : B ⥤ B} {H' : B' ⥤ B'}
    {ιH : RB ⋙ H ≅ H' ⋙ RB} {δ : H ≅ 𝟭 B} {δ' : H' ≅ 𝟭 B'}
    (h : CoeffCompatible ιH (Functor.rightUnitor RB ≪≫ (Functor.leftUnitor RB).symm)
      δ.hom δ'.hom) : IsIso (coeffMate adjB adjB ιH) := by
  have (M : B) : IsIso ((coeffMate adjB adjB ιH).app M) := by
    have e : (coeffMate adjB adjB ιH).app M = ΨB.map (δ.hom.app M) ≫ δ'.inv.app (ΨB.obj M) := by
      rw [map_hom_app_eq_coeffMate_app_comp adjB h M, Category.assoc, Iso.hom_inv_id_app]
      simp
    rw [e]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Transpose

section UpperMate

variable {B B' A A' : Type*} [Category B] [Category B'] [Category A] [Category A']
  {RB : B' ⥤ B} {RA : A' ⥤ A} {ΨB : B ⥤ B'} {ΨA : A ⥤ A'} (adjB : ΨB ⊣ RB) (adjA : ΨA ⊣ RA)
  {F : B ⥤ A} {F' : B' ⥤ A'} {U : A ⥤ B} {U' : A' ⥤ B'} (adj : F ⊣ U) (adj' : F' ⊣ U')
  (ι : RB ⋙ F ≅ F' ⋙ RA) [IsIso (coeffMate adjB adjA ι)]

/-- The comparison `U ⋙ Ψ_B ⟶ Ψ_A ⋙ U'` of `Ψ` with the right adjoints `U`, `U'` of `F`, `F'`:
the mate, under `F ⊣ U` and `F' ⊣ U'`, of the inverse of the transpose of the coefficient
comparison `ι` of `F`. -/
noncomputable def coeffUpperMate : U ⋙ ΨB ⟶ ΨA ⋙ U' :=
  mateEquiv adj adj' (TwoSquare.mk _ _ _ _ (inv (coeffMate adjB adjA ι)))

/-- The defining property of `AlgebraicGeometry.Etale.coeffUpperMate`: its composite with the
counit of `F' ⊣ U'` is `β⁻¹ ≫ Ψ(counit)`. -/
@[reassoc]
lemma map_coeffUpperMate_app_comp_counit (N : A) :
    F'.map ((coeffUpperMate adjB adjA adj adj' ι).app N) ≫ adj'.counit.app (ΨA.obj N) =
      (inv (coeffMate adjB adjA ι)).app (U.obj N) ≫ ΨA.map (adj.counit.app N) :=
  mateEquiv_counit adj adj' _ N

variable {adj'} in
/-- Morphisms into `U' N` are determined by their adjoints. -/
lemma hom_ext_of_counit {M : B'} {N : A'} {f g : M ⟶ U'.obj N}
    (h : F'.map f ≫ adj'.counit.app N = F'.map g ≫ adj'.counit.app N) : f = g :=
  (adj'.homEquiv M N).symm.injective (by rwa [Adjunction.homEquiv_counit,
    Adjunction.homEquiv_counit])

end UpperMate

section Composition

variable {B B' A A' C C' : Type*} [Category B] [Category B'] [Category A] [Category A']
  [Category C] [Category C'] {RB : B' ⥤ B} {RA : A' ⥤ A} {RC : C' ⥤ C} {ΨB : B ⥤ B'}
  {ΨA : A ⥤ A'} {ΨC : C ⥤ C'} (adjB : ΨB ⊣ RB) (adjA : ΨA ⊣ RA) (adjC : ΨC ⊣ RC)
  {F : B ⥤ A} {F' : B' ⥤ A'} {UF : A ⥤ B} {UF' : A' ⥤ B'} (adjF : F ⊣ UF) (adjF' : F' ⊣ UF')
  {G : A ⥤ C} {G' : A' ⥤ C'} {UG : C ⥤ A} {UG' : C' ⥤ A'} (adjG : G ⊣ UG) (adjG' : G' ⊣ UG')
  {H : B ⥤ C} {H' : B' ⥤ C'} {UH : C ⥤ B} {UH' : C' ⥤ B'} (adjH : H ⊣ UH) (adjH' : H' ⊣ UH')
  (ιF : RB ⋙ F ≅ F' ⋙ RA) (ιG : RA ⋙ G ≅ G' ⋙ RC) (ιH : RB ⋙ H ≅ H' ⋙ RC)
  [IsIso (coeffMate adjB adjA ιF)] [IsIso (coeffMate adjA adjC ιG)]
  [IsIso (coeffMate adjB adjC ιH)]

/-- **The comparisons with the right adjoints are compatible with composition.** For
isomorphisms `e : H ≅ F ⋙ G` and `e' : H' ≅ F' ⋙ G'` compatible with the coefficient
comparisons, the conjugates `U_G ⋙ U_F ≅ U_H` and `U_G' ⋙ U_F' ≅ U_H'` intertwine the comparison
of `Ψ` with `U_H` and the composite of the comparisons with `U_F` and `U_G`. -/
lemma map_conjugateIsoEquiv_comp_coeffUpperMate {e : H ≅ F ⋙ G} {e' : H' ≅ F' ⋙ G'}
    (he : CoeffCompatible ιH (pasteTwoSquaresIso ιF ιG) e.hom e'.hom) (N : C) :
    ΨB.map ((conjugateIsoEquiv (adjF.comp adjG) adjH e).hom.app N) ≫
        (coeffUpperMate adjB adjC adjH adjH' ιH).app N =
      (coeffUpperMate adjB adjA adjF adjF' ιF).app (UG.obj N) ≫
        UF'.map ((coeffUpperMate adjA adjC adjG adjG' ιG).app N) ≫
          (conjugateIsoEquiv (adjF'.comp adjG') adjH' e').hom.app (ΨC.obj N) := by
  -- the compatibility of the transposes, inverted
  have hβ (X : B) : (inv (coeffMate adjB adjC ιH)).app X ≫ ΨC.map (e.hom.app X) =
      e'.hom.app (ΨB.obj X) ≫ G'.map ((inv (coeffMate adjB adjA ιF)).app X) ≫
        (inv (coeffMate adjA adjC ιG)).app (F.obj X) := by
    have h₀ := he.map_app_comp_coeffMate_app adjB adjC X
    rw [coeffMate_pasteTwoSquaresIso_app adjB adjA adjC] at h₀
    simp only [NatIso.isIso_inv_app, Functor.map_inv]
    rw [IsIso.inv_comp_eq]
    simp only [← Category.assoc]
    rw [IsIso.eq_comp_inv, IsIso.eq_comp_inv]
    simp only [Category.assoc]
    exact h₀
  apply hom_ext_of_counit (adj' := adjH')
  simp only [conjugateIsoEquiv_apply_hom]
  have c₁ := conjugateEquiv_counit (adjF.comp adjG) adjH e.hom N
  have c₂ := conjugateEquiv_counit (adjF'.comp adjG') adjH' e'.hom (ΨC.obj N)
  have n₁ := (inv (coeffMate adjB adjC ιH)).naturality
    ((conjugateEquiv (adjF.comp adjG) adjH e.hom).app N)
  have n₂ := e'.hom.naturality ((coeffUpperMate adjB adjA adjF adjF' ιF).app (UG.obj N) ≫
    UF'.map ((coeffUpperMate adjA adjC adjG adjG' ιG).app N))
  have n₃ := adjF'.counit.naturality ((coeffUpperMate adjA adjC adjG adjG' ιG).app N)
  have n₄ := (inv (coeffMate adjA adjC ιG)).naturality (adjF.counit.app (UG.obj N))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Adjunction.comp_counit_app] at c₁ c₂ n₁ n₂ n₃ n₄
  -- both sides are computed to the same composite
  have hL : H'.map (ΨB.map ((conjugateEquiv (adjF.comp adjG) adjH e.hom).app N) ≫
      (coeffUpperMate adjB adjC adjH adjH' ιH).app N) ≫ adjH'.counit.app (ΨC.obj N) =
      e'.hom.app (ΨB.obj (UF.obj (UG.obj N))) ≫
        G'.map ((inv (coeffMate adjB adjA ιF)).app (UF.obj (UG.obj N))) ≫
        (inv (coeffMate adjA adjC ιG)).app (F.obj (UF.obj (UG.obj N))) ≫
        ΨC.map (G.map (adjF.counit.app (UG.obj N))) ≫ ΨC.map (adjG.counit.app N) := by
    rw [Functor.map_comp, Category.assoc, map_coeffUpperMate_app_comp_counit, reassoc_of% n₁,
      ← ΨC.map_comp, c₁, ΨC.map_comp, ΨC.map_comp, reassoc_of% hβ]
  have hR : H'.map ((coeffUpperMate adjB adjA adjF adjF' ιF).app (UG.obj N) ≫
      UF'.map ((coeffUpperMate adjA adjC adjG adjG' ιG).app N) ≫
        (conjugateEquiv (adjF'.comp adjG') adjH' e'.hom).app (ΨC.obj N)) ≫
          adjH'.counit.app (ΨC.obj N) =
      e'.hom.app (ΨB.obj (UF.obj (UG.obj N))) ≫
        G'.map ((inv (coeffMate adjB adjA ιF)).app (UF.obj (UG.obj N))) ≫
        (inv (coeffMate adjA adjC ιG)).app (F.obj (UF.obj (UG.obj N))) ≫
        ΨC.map (G.map (adjF.counit.app (UG.obj N))) ≫ ΨC.map (adjG.counit.app N) := by
    rw [← Category.assoc, Functor.map_comp, Category.assoc, c₂, reassoc_of% n₂,
      ← G'.map_comp_assoc, F'.map_comp, Category.assoc, n₃,
      map_coeffUpperMate_app_comp_counit_assoc]
    simp only [Functor.map_comp, Category.assoc]
    rw [map_coeffUpperMate_app_comp_counit, reassoc_of% n₄]
  exact hL.trans hR.symm

end Composition

section Identity

/-- The counit of the adjunction `H ⊣ 𝟭` induced by an isomorphism `δ : H ≅ 𝟭` is `δ`. -/
lemma _root_.CategoryTheory.Adjunction.id_ofNatIsoLeft_symm_counit_app {B : Type*} [Category B]
    {H : B ⥤ B} (δ : H ≅ 𝟭 B) (X : B) :
    (Adjunction.id.ofNatIsoLeft δ.symm).counit.app X = δ.hom.app X := by
  simp [Adjunction.ofNatIsoLeft]

variable {B B' : Type*} [Category B] [Category B'] {RB : B' ⥤ B} {ΨB : B ⥤ B'}
  (adjB : ΨB ⊣ RB) {H : B ⥤ B} {H' : B' ⥤ B'} {UH : B ⥤ B} {UH' : B' ⥤ B'} (adjH : H ⊣ UH)
  (adjH' : H' ⊣ UH') (ιH : RB ⋙ H ≅ H' ⋙ RB) [IsIso (coeffMate adjB adjB ιH)]

/-- **The comparison with the right adjoint is compatible with identifications with the
identity.** For `δ : H ≅ 𝟭` and `δ' : H' ≅ 𝟭` compatible with the coefficient comparisons, the
induced identifications `U_H ≅ 𝟭` (the right adjoints of `δ`) intertwine the comparison of `Ψ`
with `U_H` and the identity. -/
lemma map_rightAdjointUniq_hom_app_eq {δ : H ≅ 𝟭 B} {δ' : H' ≅ 𝟭 B'}
    (h : CoeffCompatible ιH (Functor.rightUnitor RB ≪≫ (Functor.leftUnitor RB).symm)
      δ.hom δ'.hom) (N : B) :
    ΨB.map ((adjH.rightAdjointUniq (Adjunction.id.ofNatIsoLeft δ.symm)).hom.app N) =
      (coeffUpperMate adjB adjB adjH adjH' ιH).app N ≫
        (adjH'.rightAdjointUniq (Adjunction.id.ofNatIsoLeft δ'.symm)).hom.app (ΨB.obj N) := by
  apply hom_ext_of_counit (adj' := Adjunction.id.ofNatIsoLeft δ'.symm)
  have u₁ := adjH.rightAdjointUniq_hom_app_counit (Adjunction.id.ofNatIsoLeft δ.symm) N
  have u₂ := adjH'.rightAdjointUniq_hom_app_counit (Adjunction.id.ofNatIsoLeft δ'.symm)
    (ΨB.obj N)
  have hδ := map_hom_app_eq_coeffMate_app_comp adjB h N
  have n₂ := (coeffMate adjB adjB ιH).naturality
    ((adjH.rightAdjointUniq (Adjunction.id.ofNatIsoLeft δ.symm)).hom.app N)
  rw [Adjunction.id_ofNatIsoLeft_symm_counit_app] at u₁ u₂ ⊢
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at n₂ ⊢
  rw [Functor.map_comp, Category.assoc, u₂, map_coeffUpperMate_app_comp_counit, ← u₁,
    ΨB.map_comp, hδ, reassoc_of% n₂, NatIso.isIso_inv_app, IsIso.inv_hom_id_assoc]

end Identity

section BaseChange

variable {B B' A A' B₂ B₂' A₂ A₂' : Type*} [Category B] [Category B'] [Category A]
  [Category A'] [Category B₂] [Category B₂'] [Category A₂] [Category A₂']
  {RB : B' ⥤ B} {RA : A' ⥤ A} {RB₂ : B₂' ⥤ B₂} {RA₂ : A₂' ⥤ A₂} {ΨB : B ⥤ B'} {ΨA : A ⥤ A'}
  {ΨB₂ : B₂ ⥤ B₂'} {ΨA₂ : A₂ ⥤ A₂'} (adjB : ΨB ⊣ RB) (adjA : ΨA ⊣ RA) (adjB₂ : ΨB₂ ⊣ RB₂)
  (adjA₂ : ΨA₂ ⊣ RA₂)
  {F : B ⥤ A} {F' : B' ⥤ A'} {UF : A ⥤ B} {UF' : A' ⥤ B'} (adjF : F ⊣ UF) (adjF' : F' ⊣ UF')
  {F₂ : B₂ ⥤ A₂} {F₂' : B₂' ⥤ A₂'} {UF₂ : A₂ ⥤ B₂} {UF₂' : A₂' ⥤ B₂'} (adjF₂ : F₂ ⊣ UF₂)
  (adjF₂' : F₂' ⊣ UF₂') {V : B ⥤ B₂} {V' : B' ⥤ B₂'} {W : A ⥤ A₂} {W' : A' ⥤ A₂'}
  (ιF : RB ⋙ F ≅ F' ⋙ RA) (ιF₂ : RB₂ ⋙ F₂ ≅ F₂' ⋙ RA₂) (κV : RB ⋙ V ≅ V' ⋙ RB₂)
  (κW : RA ⋙ W ≅ W' ⋙ RA₂) [IsIso (coeffMate adjB adjA ιF)] [IsIso (coeffMate adjB₂ adjA₂ ιF₂)]
  (Ex : F ⋙ W ⟶ V ⋙ F₂) (Ex' : F' ⋙ W' ⟶ V' ⋙ F₂') [IsIso Ex] [IsIso Ex']

/-- **The comparisons with the right adjoints are compatible with base change.** Let
`Ex : F ⋙ W ⟶ V ⋙ F₂` and `Ex' : F' ⋙ W' ⟶ V' ⋙ F₂'` be isomorphisms (for instance the
compact-support base change maps `Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!`) compatible with the coefficient
comparisons. Then their mates `U_F ⋙ V ⟶ W ⋙ U_{F₂}` (the base change maps of the right
adjoints) are compatible with the comparisons of `Ψ` with the right adjoints, through the
transposes of the coefficient comparisons of `V` and `W`. -/
lemma coeffMate_app_comp_map_coeffUpperMate_app_comp
    (h : CoeffCompatible (pasteTwoSquaresIso ιF κW) (pasteTwoSquaresIso κV ιF₂) Ex Ex')
    (N : A) :
    (coeffMate adjB adjB₂ κV).app (UF.obj N) ≫
        V'.map ((coeffUpperMate adjB adjA adjF adjF' ιF).app N) ≫
          (mateEquiv adjF' adjF₂' (TwoSquare.mk _ _ _ _ (inv Ex'))).app (ΨA.obj N) =
      ΨB₂.map ((mateEquiv adjF adjF₂ (TwoSquare.mk _ _ _ _ (inv Ex))).app N) ≫
        (coeffUpperMate adjB₂ adjA₂ adjF₂ adjF₂' ιF₂).app (W.obj N) ≫
          UF₂'.map ((coeffMate adjA adjA₂ κW).app N) := by
  -- the compatibility of the transposes, inverted
  have hβ (X : B) : F₂'.map ((coeffMate adjB adjB₂ κV).app X) ≫ (inv Ex').app (ΨB.obj X) ≫
      W'.map ((inv (coeffMate adjB adjA ιF)).app X) =
      (inv (coeffMate adjB₂ adjA₂ ιF₂)).app (V.obj X) ≫ ΨA₂.map ((inv Ex).app X) ≫
        (coeffMate adjA adjA₂ κW).app (F.obj X) := by
    have h₀ := h.map_app_comp_coeffMate_app adjB adjA₂ X
    rw [coeffMate_pasteTwoSquaresIso_app adjB adjA adjA₂,
      coeffMate_pasteTwoSquaresIso_app adjB adjB₂ adjA₂] at h₀
    simp only [NatIso.isIso_inv_app, Functor.map_inv]
    rw [IsIso.eq_inv_comp, IsIso.eq_inv_comp]
    simp only [← Category.assoc]
    rw [IsIso.comp_inv_eq, IsIso.comp_inv_eq]
    simp only [Category.assoc] at h₀ ⊢
    exact h₀
  apply hom_ext_of_counit (adj' := adjF₂')
  have b₁ := mateEquiv_counit adjF' adjF₂' (TwoSquare.mk _ _ _ _ (inv Ex')) (ΨA.obj N)
  have b₂ := mateEquiv_counit adjF adjF₂ (TwoSquare.mk _ _ _ _ (inv Ex)) N
  have n₁ := (inv Ex').naturality ((coeffUpperMate adjB adjA adjF adjF' ιF).app N)
  have n₂ := adjF₂'.counit.naturality ((coeffMate adjA adjA₂ κW).app N)
  have n₃ := (inv (coeffMate adjB₂ adjA₂ ιF₂)).naturality
    ((mateEquiv adjF adjF₂ (TwoSquare.mk _ _ _ _ (inv Ex))).app N)
  have n₄ := (coeffMate adjA adjA₂ κW).naturality (adjF.counit.app N)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Functor.id_map] at b₁ b₂ n₁ n₂ n₃ n₄
  have hL : F₂'.map ((coeffMate adjB adjB₂ κV).app (UF.obj N) ≫
      V'.map ((coeffUpperMate adjB adjA adjF adjF' ιF).app N) ≫
        (mateEquiv adjF' adjF₂' (TwoSquare.mk _ _ _ _ (inv Ex'))).app (ΨA.obj N)) ≫
          adjF₂'.counit.app (W'.obj (ΨA.obj N)) =
      F₂'.map ((coeffMate adjB adjB₂ κV).app (UF.obj N)) ≫ (inv Ex').app (ΨB.obj (UF.obj N)) ≫
        W'.map ((inv (coeffMate adjB adjA ιF)).app (UF.obj N)) ≫
          W'.map (ΨA.map (adjF.counit.app N)) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, b₁,
      reassoc_of% n₁, ← W'.map_comp, map_coeffUpperMate_app_comp_counit, W'.map_comp]
  have hR : F₂'.map (ΨB₂.map ((mateEquiv adjF adjF₂ (TwoSquare.mk _ _ _ _ (inv Ex))).app N) ≫
      (coeffUpperMate adjB₂ adjA₂ adjF₂ adjF₂' ιF₂).app (W.obj N) ≫
        UF₂'.map ((coeffMate adjA adjA₂ κW).app N)) ≫ adjF₂'.counit.app (W'.obj (ΨA.obj N)) =
      F₂'.map ((coeffMate adjB adjB₂ κV).app (UF.obj N)) ≫ (inv Ex').app (ΨB.obj (UF.obj N)) ≫
        W'.map ((inv (coeffMate adjB adjA ιF)).app (UF.obj N)) ≫
          W'.map (ΨA.map (adjF.counit.app N)) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, n₂,
      map_coeffUpperMate_app_comp_counit_assoc, reassoc_of% n₃, ← ΨA₂.map_comp_assoc, b₂,
      ΨA₂.map_comp, Category.assoc, n₄, reassoc_of% (hβ (UF.obj N))]
  exact hL.trans hR.symm

end BaseChange

section IteratedMate

variable {X X' Z Z' : Type*} [Category X] [Category X'] [Category Z] [Category Z']
  {ResX : X' ⥤ X} {ResZ : Z' ⥤ Z} {ΨX : X ⥤ X'} {ΨZ : Z ⥤ Z'} (adjX : ΨX ⊣ ResX)
  (adjZ : ΨZ ⊣ ResZ) {L : X ⥤ Z} {L' : X' ⥤ Z'} {R : Z ⥤ X} {R' : Z' ⥤ X'} (adjL : L ⊣ R)
  (adjL' : L' ⊣ R') (κ : ResX ⋙ L ≅ L' ⋙ ResZ) (σ : ResZ ⋙ R ≅ R' ⋙ ResX)
  [IsIso (coeffMate adjX adjZ κ)]

/-- **Transposes of mates.** If the coefficient comparison `σ` of the right adjoints is the mate
of the coefficient comparison `κ` of the left adjoints, then the transpose of `σ` is the mate of
the inverse of the transpose of `κ`: the comparison of `Ψ` with `R` obtained from that with `L`
by adjunction is the transpose of `σ`. -/
lemma coeffUpperMate_eq_coeffMate (hσ : mateEquiv adjL' adjL κ.hom = σ.inv) :
    coeffUpperMate adjX adjZ adjL adjL' κ = coeffMate adjZ adjX σ := by
  ext N
  apply hom_ext_of_adjunction (adjA := adjX)
  have hu (c : X') : ResX.map (adjL'.unit.app c) =
      adjL.unit.app (ResX.obj c) ≫ R.map (κ.hom.app c) ≫ σ.hom.app (L'.obj c) := by
    have := unit_mateEquiv adjL' adjL κ.hom c
    rw [hσ] at this
    simp only [Functor.comp_obj, Functor.id_obj] at this
    rw [← reassoc_of% this]
    simp
  have hP (M : X) : L.map (adjX.unit.app M) ≫ κ.hom.app (ΨX.obj M) ≫
      ResZ.map ((inv (coeffMate adjX adjZ κ)).app M) = adjZ.unit.app (L.obj M) := by
    rw [← unit_app_comp_map_coeffMate_app_assoc adjX adjZ κ M, ← ResZ.map_comp, ← NatTrans.comp_app,
      IsIso.hom_inv_id, NatTrans.id_app]
    simp
  have n₁ := adjL.unit.naturality (adjX.unit.app (R.obj N))
  have n₂ := σ.hom.naturality ((inv (coeffMate adjX adjZ κ)).app (R.obj N))
  have n₃ := σ.hom.naturality (ΨZ.map (adjL.counit.app N))
  have n₄ := adjZ.unit.naturality (adjL.counit.app N)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n₁ n₂ n₃ n₄
  rw [unit_app_comp_map_coeffMate_app, coeffUpperMate, Adjunction.mateEquiv_app]
  simp only [TwoSquare.natTrans, Functor.map_comp]
  rw [hu]
  simp only [Category.assoc]
  rw [reassoc_of% n₁, ← reassoc_of% n₂, ← n₃, ← R.map_comp_assoc, ← R.map_comp_assoc,
    ← R.map_comp_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% (hP (R.obj N)), ← n₄, R.map_comp, Category.assoc,
    Adjunction.right_triangle_components_assoc]

end IteratedMate

end AlgebraicGeometry.Etale
