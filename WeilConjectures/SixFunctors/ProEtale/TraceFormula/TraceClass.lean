/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing

/-!
# The exceptional internal hom exchange and external duality

For a morphism `c : C ⟶ Z` of geometric schemes and `M`, `N` in `Dᵇctf(Z)`, the canonical
comparison `c^! RHom(M, N) ⟶ RHom(c^* M, c^! N)`, the tensor-hom adjoint of the exceptional
adjoint of

```
  Rc_! (c^* M ⊗ᴸ c^! RHom(M, N)) ≃ Rc_! c^! RHom(M, N) ⊗ᴸ M ──ε──▶ RHom(M, N) ⊗ᴸ M ──ev──▶ N,
```

is an isomorphism: both sides represent `P ↦ Hom(Rc_! P ⊗ᴸ M, N)` on `Dᵇctf(C)`.

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricOperations.exceptionalIhomMap`: the comparison
  `c^! RHom(M, N) ⟶ RHom(c^* M, c^! N)`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.exceptionalIhomIso`: the comparison as an
  isomorphism (blueprint `lem-trf-exceptional-internal-hom-exchange`).
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {s : Scheme.{u}}

/-- A morphism `f : A ⟶ B` between objects of a full subcategory `P` such that postcomposition
with `f` is a bijection `Hom(Q, A) ≃ Hom(Q, B)` for every `Q` in `P` is an isomorphism. -/
lemma _root_.CategoryTheory.ObjectProperty.isIso_of_bijective_comp {D : Type*} [Category D]
    (P : ObjectProperty D) {X Y : D} (hX : P X) (hY : P Y) (f : X ⟶ Y)
    (h : ∀ Q, P Q → Function.Bijective fun g : Q ⟶ X ↦ g ≫ f) : IsIso f := by
  obtain ⟨g, hg⟩ := (h Y hY).2 (𝟙 Y)
  refine ⟨g, (h X hX).1 ?_, hg⟩
  simp only [Category.assoc, hg, Category.comp_id, Category.id_comp]

omit [Etale.HasBoundedBelowUpperShrieks A] in
/-- The internal hom out of isomorphic objects: `RHom(X, Y) ≃ RHom(X', Y)` for `X ≅ X'`. -/
@[simps]
noncomputable def ihomIsoOfIsoLeft {D : Type*} [Category D] [MonoidalCategory D]
    [MonoidalClosed D] {X X' : D} (e : X ≅ X') (Y : D) : (ihom X).obj Y ≅ (ihom X').obj Y where
  hom := (pre e.inv).app Y
  inv := (pre e.hom).app Y
  hom_inv_id := by rw [← NatTrans.comp_app, ← pre_map, e.hom_inv_id, pre_id]; rfl
  inv_hom_id := by rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id]; rfl

namespace GeometricOperations

variable [DerivedBraiding A] (G : GeometricOperations A s)

variable {C Z : Scheme.{u}} (c : C ⟶ Z) (hc : IsGeometricHom s c) [HasCompactification c]
  {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)} (hM : G.ctf Z M) (hN : G.ctf Z N)

/-- The map `Rc_! (c^* M ⊗ᴸ P) ⟶ N` attached to `h : Rc_! P ⟶ RHom(M, N)`: the composite

```
  Rc_! (c^* M ⊗ᴸ P) ≃ Rc_! (P ⊗ᴸ c^* M) ≃ Rc_! P ⊗ᴸ M ──h──▶ RHom(M, N) ⊗ᴸ M ≃ M ⊗ᴸ RHom(M, N)
      ──ev──▶ N
```

of the braiding, the projection formula and the evaluation. -/
noncomputable def exceptionalIhomAux {P : DerivedCategory (Sheaf (Scheme.ProEt.topology C) A)}
    (hP : G.ctf C P) (h : (rightDerivedLowerShriek A c).obj P ⟶ (ihom M).obj N) :
    (rightDerivedLowerShriek A c).obj (((upperStar A c).leftDerivedFunctor).obj M ⊗ P) ⟶ N :=
  (rightDerivedLowerShriek A c).map (β_ _ _).hom ≫
    ((G.projectionFormula c hc).app (⟨P, hP⟩, ⟨M, hM⟩)).inv ≫ (h ▷ M) ≫ (β_ _ _).hom ≫
    (ihom.ev M).app N

/-- The canonical comparison `c^! RHom(M, N) ⟶ RHom(c^* M, c^! N)` for `M`, `N` in `Dᵇctf(Z)`:
the tensor-hom adjoint of the exceptional adjoint of
`Rc_! (c^* M ⊗ᴸ c^! RHom(M, N)) ⟶ N`, built from the counit
`Rc_! c^! RHom(M, N) ⟶ RHom(M, N)` by `exceptionalIhomAux`. -/
noncomputable def exceptionalIhomMap :
    (rightDerivedUpperShriek A c).obj ((ihom M).obj N) ⟶
      (ihom (((upperStar A c).leftDerivedFunctor).obj M)).obj
        ((rightDerivedUpperShriek A c).obj N) :=
  have hR : G.ctf Z ((ihom M).obj N) := G.ctf_ihom hc.id_target hM hN
  curry (G.exceptionalHomEquiv c hc
    (G.ctf_tensor hc.id_source (G.ctf_upperStar c hc hM) (G.ctf_upperShriek c hc hR)) hN
    (G.exceptionalIhomAux c hc hM (G.ctf_upperShriek c hc hR)
      (G.exceptionalCounit c hc _ hR)))


omit [DerivedBraiding A] in
/-- The inverse of the exceptional adjunction bijection is `g ↦ Rc_! g ≫ ε`. -/
lemma _root_.AlgebraicGeometry.ProEtale.GeometricCoefficients.exceptionalHomEquiv_symm_apply
    (G : GeometricCoefficients A s) {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : G.ctf X K) {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hL : G.ctf Y L)
    (g : K ⟶ (rightDerivedUpperShriek A f).obj L) :
    (G.exceptionalHomEquiv f hf hK hL).symm g =
      (rightDerivedLowerShriek A f).map g ≫ G.exceptionalCounit f hf L hL := by
  rw [Equiv.symm_apply_eq, GeometricCoefficients.exceptionalHomEquiv_naturality_left _ f hf hK
    (G.ctf_upperShriek f hf hL) hL, GeometricCoefficients.exceptionalHomEquiv_exceptionalCounit,
    Category.comp_id]

lemma exceptionalIhomAux_eq {P : DerivedCategory (Sheaf (Scheme.ProEt.topology C) A)}
    (hP : G.ctf C P) (h : (rightDerivedLowerShriek A c).obj P ⟶ (ihom M).obj N) :
    G.exceptionalIhomAux c hc hM hP h =
      (rightDerivedLowerShriek A c).map (β_ _ _).hom ≫
        ((G.projectionFormula c hc).app (⟨P, hP⟩, ⟨M, hM⟩)).inv ≫ (β_ _ _).hom ≫ uncurry h := by
  rw [exceptionalIhomAux, BraidedCategory.braiding_naturality_left_assoc, uncurry_eq]
  rfl

lemma bijective_exceptionalIhomAux {P : DerivedCategory (Sheaf (Scheme.ProEt.topology C) A)}
    (hP : G.ctf C P) : Function.Bijective (G.exceptionalIhomAux c hc hM (N := N) hP) := by
  set e := (rightDerivedLowerShriek A c).mapIso (β_ _ _) ≪≫
    ((G.projectionFormula c hc).app (⟨P, hP⟩, ⟨M, hM⟩)).symm ≪≫ β_ _ _
  have he (h) : G.exceptionalIhomAux c hc hM (N := N) hP h = e.hom ≫ uncurry h := by
    simp [e, exceptionalIhomAux_eq]
  refine ⟨fun h₁ h₂ h ↦ ?_, fun k ↦ ⟨curry (e.inv ≫ k), ?_⟩⟩
  · rw [he, he, cancel_epi] at h
    exact (uncurry_injective h)
  · rw [he, uncurry_curry, Iso.hom_inv_id_assoc]

variable {c hc hM hN} in
lemma comp_exceptionalIhomMap {P : DerivedCategory (Sheaf (Scheme.ProEt.topology C) A)}
    (hP : G.ctf C P) (g : P ⟶ (rightDerivedUpperShriek A c).obj ((ihom M).obj N)) :
    have hR : G.ctf Z ((ihom M).obj N) := G.ctf_ihom hc.id_target hM hN
    g ≫ G.exceptionalIhomMap c hc hM hN =
      curry (G.exceptionalHomEquiv c hc (G.ctf_tensor hc.id_source (G.ctf_upperStar c hc hM) hP)
        hN (G.exceptionalIhomAux c hc hM hP ((G.exceptionalHomEquiv c hc hP hR).symm g))) := by
  intro hR
  rw [exceptionalIhomMap, ← curry_natural_left,
    ← GeometricCoefficients.exceptionalHomEquiv_naturality_left _ c hc
      (G.ctf_tensor hc.id_source (G.ctf_upperStar c hc hM) hP)
      (G.ctf_tensor hc.id_source (G.ctf_upperStar c hc hM) (G.ctf_upperShriek c hc hR)) hN]
  congr 1
  rw [GeometricCoefficients.exceptionalHomEquiv_symm_apply, exceptionalIhomAux,
    exceptionalIhomAux, ← Functor.map_comp_assoc, BraidedCategory.braiding_naturality_right]
  congr 1
  have nat := (G.projectionFormula c hc).inv.naturality (X := (⟨P, hP⟩, ⟨M, hM⟩))
    (Y := (⟨_, G.ctf_upperShriek c hc hR⟩, ⟨M, hM⟩)) (ObjectProperty.homMk g, 𝟙 _)
  dsimp at nat
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at nat
  rw [Functor.map_comp, Category.assoc, MonoidalCategory.comp_whiskerRight, Category.assoc]
  erw [reassoc_of% nat]
  rfl

/-- Blueprint `lem-trf-exceptional-internal-hom-exchange`: for a morphism `c : C ⟶ Z` of
geometric schemes and `M`, `N` in `Dᵇctf(Z)`, the canonical comparison
`c^! RHom(M, N) ⟶ RHom(c^* M, c^! N)` is an isomorphism, natural in `M` and `N`. -/
instance isIso_exceptionalIhomMap : IsIso (G.exceptionalIhomMap c hc hM hN) := by
  have hR : G.ctf Z ((ihom M).obj N) := G.ctf_ihom hc.id_target hM hN
  refine (G.ctf C).isIso_of_bijective_comp (G.ctf_upperShriek c hc hR)
    (G.ctf_ihom hc.id_source (G.ctf_upperStar c hc hM) (G.ctf_upperShriek c hc hN)) _
    fun P hP ↦ ?_
  have key : (fun g ↦ g ≫ G.exceptionalIhomMap c hc hM hN) =
      curry ∘ (G.exceptionalHomEquiv c hc
        (G.ctf_tensor hc.id_source (G.ctf_upperStar c hc hM) hP) hN) ∘
        G.exceptionalIhomAux c hc hM hP ∘ (G.exceptionalHomEquiv c hc hP hR).symm :=
    funext fun g ↦ G.comp_exceptionalIhomMap hP g
  rw [key]
  exact (Function.bijective_iff_has_inverse.2 ⟨uncurry, uncurry_curry, curry_uncurry⟩).comp
    ((Equiv.bijective _).comp ((G.bijective_exceptionalIhomAux c hc hM hP).comp
      (Equiv.bijective _)))


/-- Blueprint `lem-trf-exceptional-internal-hom-exchange`: the canonical comparison
`c^! RHom(M, N) ≃ RHom(c^* M, c^! N)` for `M`, `N` in `Dᵇctf(Z)`, as an isomorphism. -/
noncomputable def exceptionalIhomIso :
    (rightDerivedUpperShriek A c).obj ((ihom M).obj N) ≅
      (ihom (((upperStar A c).leftDerivedFunctor).obj M)).obj
        ((rightDerivedUpperShriek A c).obj N) :=
  asIso (G.exceptionalIhomMap c hc hM hN)

section SourceIso

variable {X : Scheme.{u}} {aX : X ⟶ s} [IsGeometric aX] [HasCompactification aX] [QuasiCompact aX]
  [s.IsSpecOfField] {p₁ p₂ : Z ⟶ X} (sq : IsPullback p₁ p₂ aX aX) [IsGeometric (p₁ ≫ aX)]
  [HasCompactification p₁] {c₁ c₂ : C ⟶ X} [HasCompactification c₁] (h₁ : c ≫ p₁ = c₁)
  (h₂ : c ≫ p₂ = c₂) [HasCompactification (c ≫ p₁)]
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)

/-- External duality on a support `c : C ⟶ Z` over a Cartesian square `Z = X ×_s X` with
projections `p₁`, `p₂`, for `c₁ = c ≫ p₁` and `c₂ = c ≫ p₂`:
`RHom(Lc₂^* K, Rc₁^! K) ≃ RHom(Lc^* Lp₂^* K, Rc^! Rp₁^! K) ≃ Rc^! RHom(Lp₂^* K, Rp₁^! K)
≃ Rc^! (Lp₁^* K ⊗ᴸ Lp₂^* D_X K)`. It is stated for an arbitrary Cartesian square, as the kernel
check on the literal fibre product is very slow. -/
noncomputable def externalDualityIso :
    (ihom (((upperStar A c₂).leftDerivedFunctor).obj K)).obj
        ((rightDerivedUpperShriek A c₁).obj K) ≅
      (rightDerivedUpperShriek A c).obj (((upperStar A p₁).leftDerivedFunctor).obj K ⊗
        ((upperStar A p₂).leftDerivedFunctor).obj (G.verdierDual aX K)) :=
  have hp₁ : IsGeometricHom s p₁ := .mk (aY := aX) rfl
  have hp₂ : IsGeometricHom s p₂ := .mk (aX := p₁ ≫ aX) (aY := aX) sq.w.symm
  ihomIsoOfIsoLeft (leftDerivedUpperStarCompIso c h₂ K).symm _ ≪≫
    (ihom _).mapIso ((G.upperShriekCompIso c p₁ hc hp₁ (hc.comp hp₁) K hK ≪≫
      (rightDerivedUpperShriekCongr A h₁).app K).symm) ≪≫
    (G.exceptionalIhomIso c hc (G.ctf_upperStar _ hp₂ hK) (G.ctf_upperShriek _ hp₁ hK)).symm ≪≫
    (rightDerivedUpperShriek A c).mapIso (G.kunnethVerdier sq K hK K hK).symm

end SourceIso

end GeometricOperations


namespace Correspondence

variable [DerivedBraiding A] (G : GeometricOperations A s) {X : Scheme.{u}} {aX : X ⟶ s}
  [IsGeometric aX] [HasCompactification aX] [QuasiCompact aX] [s.IsSpecOfField]
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)
  (c : Correspondence aX aX K K) [IsGeometric c.str] [HasCompactification c.toProd]
  [HasCompactification (pullback.fst aX aX)]

/-- Blueprint `thm-trf-verdier-duality`: external duality for the fixed-point trace,
`H_c(K) = RHom(Lc₂^* K, Rc₁^! K) ≃ Rc^! RHom(Lp₂^* K, Rp₁^! K) ≃ Rc^! (K ⊠ D_X K)` on the
support `C` of an endocorrespondence, from the composition isomorphisms of `L(-)^*` and
`R(-)^!`, the exceptional internal hom exchange `GeometricOperations.exceptionalIhomIso` and
the Künneth-Verdier isomorphism `K ⊠ D_X K ≃ RHom(Lp₂^* K, Rp₁^! K)` of
`GeometricOperations.kunnethVerdier` (the first assertion of the blueprint statement). -/
noncomputable def traceClassSourceIso :
    c.traceClassSource ≅ (rightDerivedUpperShriek A c.toProd).obj
      (((upperStar A (pullback.fst aX aX)).leftDerivedFunctor).obj K ⊗
        ((upperStar A (pullback.snd aX aX)).leftDerivedFunctor).obj (G.verdierDual aX K)) :=
  G.externalDualityIso c.toProd c.isGeometricHom_toProd (IsPullback.of_hasPullback aX aX)
    c.toProd_fst c.toProd_snd hK

end Correspondence

namespace GeometricOperations

end GeometricOperations

end AlgebraicGeometry.ProEtale
