/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange

/-!
# Strict models of normalized towers

Let `(C, J)` be an essentially small site, `R` a commutative ring and `I` an ideal, and put
`A_n = R ⧸ Iⁿ`. A *normalized tower* is a family of objects `L_n ∈ D(J, A_n)` with transition
maps `t_n : L_{n+1} ⟶ Res L_n` exhibiting `L_n` as the derived base change
`L_{n+1} ⊗ᴸ_{A_{n+1}} A_n` (`CategoryTheory.Sheaf.IsDerivedBaseChange`).

This file shows that a normalized tower is represented by a tower of K-flat complexes and chain
maps: there are K-flat complexes `P_n` of flat sheaves of `A_n`-modules with
`Q P_n ≅ L_n` and chain maps `P_{n+1} ⟶ Res P_n` representing the transition maps
(`DerivedCategory.exists_kFlatModelTower`).

## Main definitions

- `CochainComplex.IsKFlat`: K-flat complexes.
- `DerivedCategory.KFlatModel`: a K-flat model of an object of the derived category.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian.{v} 𝒜]
  [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜] [BraidedCategory 𝒜]
  [Abelian.HasFunctorialFlatResolution 𝒜]

/-- A complex `P` is *K-flat* if tensoring with it preserves quasi-isomorphisms. This is
`(HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P`, packaged as a definition so that it can be
stated for concrete categories without searching for the monoidal structure on complexes. -/
def CochainComplex.IsKFlat (P : CochainComplex 𝒜 ℤ) : Prop :=
  (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P

/-- Every complex has a resolution by a K-flat complex of flat objects. -/
lemma CochainComplex.exists_quasiIso_isKFlat (L : CochainComplex 𝒜 ℤ) :
    ∃ (P : CochainComplex 𝒜 ℤ) (π : P ⟶ L), QuasiIso π ∧ (∀ n, ObjectProperty.flat (P.X n)) ∧
      P.IsKFlat :=
  CochainComplex.exists_quasiIso_flat_kFlat L

end

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

/-- A *K-flat model* of an object `L` of `D(J, A)`: a K-flat complex of flat sheaves of
`A`-modules together with an isomorphism `Q P ≅ L`. -/
structure KFlatModel {A : Type (u + 1)} [CommRing A]
    (L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) where
  /-- The complex. -/
  P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ
  flat (i : ℤ) : ObjectProperty.flat (P.X i)
  isKFlat : P.IsKFlat
  /-- The isomorphism `Q P ≅ L`. -/
  iso : Q.obj P ≅ L

namespace KFlatModel

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']

/-- Every object has a K-flat model. -/
lemma nonempty (L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    Nonempty (KFlatModel L) := by
  obtain ⟨P, π, hπ, hflat, hP⟩ := CochainComplex.exists_quasiIso_isKFlat (Q.objPreimage L)
  have : IsIso (Q.map π) := (isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  exact ⟨⟨P, hflat, hP, asIso (Q.map π) ≪≫ Q.objObjPreimageIso L⟩⟩

/-- A morphism `L' ⟶ Res L` to the restriction of scalars of an object with a K-flat model `M`
is represented by a chain map `P' ⟶ Res P` out of some K-flat model `M'` of `L'`. -/
lemma exists_hom (f : A' →+* A) {L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
    (M : KFlatModel L) {L' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A'))}
    (t : L' ⟶ (Sheaf.derivedRestrictScalars J f).obj L) :
    ∃ (M' : KFlatModel L')
      (g : M'.P ⟶ ((Sheaf.restrictScalars J f).mapHomologicalComplex (.up ℤ)).obj M.P),
      Q.map g ≫ (Sheaf.restrictScalars J f).mapDerivedCategoryFactors.inv.app M.P ≫
          (Sheaf.derivedRestrictScalars J f).map M.iso.hom = M'.iso.hom ≫ t := by
  let F := Sheaf.restrictScalars J f
  let Y := Q.objPreimage L'
  let eY : Q.obj Y ≅ L' := Q.objObjPreimageIso L'
  let φ : Q.obj Y ⟶ Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj M.P) :=
    eY.hom ≫ t ≫ (Sheaf.derivedRestrictScalars J f).map M.iso.inv ≫
      F.mapDerivedCategoryFactors.hom.app M.P
  obtain ⟨X, s, _, g, hφ⟩ := right_fac φ
  obtain ⟨P, π, hπ, hflat, hP⟩ := CochainComplex.exists_quasiIso_isKFlat X
  have : IsIso (Q.map π) := (isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  refine ⟨⟨P, hflat, hP, asIso (Q.map π) ≪≫ asIso (Q.map s) ≪≫ eY⟩, π ≫ g, ?_⟩
  have hg : Q.map g = Q.map s ≫ φ := by rw [hφ, IsIso.hom_inv_id_assoc]
  simp only [Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc, hg, φ, F]
  simp

end KFlatModel

section Restrict

variable {A A' A'' : Type (u + 1)} [CommRing A] [CommRing A'] [CommRing A'']
  {f : A →+* A'} {g : A' →+* A''} {gf : A →+* A''} (hgf : gf = g.comp f)

/-- On the image of a complex, `Sheaf.derivedRestrictScalarsCompIso` is the image of the
composition isomorphism of restrictions of scalars of complexes. -/
lemma derivedRestrictScalarsCompIso_hom_app_Q_obj
    (K : CochainComplex (Sheaf J (ModuleCat.{u + 1} A'')) ℤ) :
    (Sheaf.restrictScalars J f).mapDerivedCategoryFactors.inv.app
        (((Sheaf.restrictScalars J g).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Sheaf.derivedRestrictScalars J f).map
        ((Sheaf.restrictScalars J g).mapDerivedCategoryFactors.inv.app K) ≫
      (Sheaf.derivedRestrictScalarsCompIso J hgf).hom.app (Q.obj K) =
    Q.map ((Functor.mapHomologicalComplexCompIso
        (Sheaf.restrictScalarsCompIso J f g gf hgf) (.up ℤ)).hom.app K) ≫
      (Sheaf.restrictScalars J gf).mapDerivedCategoryFactors.inv.app K := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fac (Sheaf.restrictScalars J g)
    (Sheaf.restrictScalars J f) K
  have h₂ := Functor.mapDerivedCategoryNatIso_fac (Sheaf.restrictScalarsCompIso J f g gf hgf) K
  have h₃ : Q.map ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (Sheaf.restrictScalars J g ⋙ Sheaf.restrictScalars J f)) (.up ℤ)).hom.app K) =
      𝟙 _ := by
    rw [← Q.map_id]
    congr 1
  rw [h₃] at h₁
  erw [Category.comp_id] at h₁
  have e₁ : ((Sheaf.restrictScalars J g).mapDerivedCategoryCompIso
      (Sheaf.restrictScalars J f)).inv.app (Q.obj K) =
      (Sheaf.derivedRestrictScalars J f).map
        ((Sheaf.restrictScalars J g).mapDerivedCategoryFactors.hom.app K) ≫
      (Sheaf.restrictScalars J f).mapDerivedCategoryFactors.hom.app
        (((Sheaf.restrictScalars J g).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Sheaf.restrictScalars J g ⋙ Sheaf.restrictScalars J f).mapDerivedCategoryFactors.inv.app
        K := by
    rw [← cancel_epi (((Sheaf.restrictScalars J g).mapDerivedCategoryCompIso
      (Sheaf.restrictScalars J f)).hom.app (Q.obj K)), Iso.hom_inv_id_app, reassoc_of% h₁,
      Iso.hom_inv_id_app]
    rfl
  have e₂ : (Functor.mapDerivedCategoryNatIso
      (Sheaf.restrictScalarsCompIso J f g gf hgf)).hom.app (Q.obj K) =
      (Sheaf.restrictScalars J g ⋙ Sheaf.restrictScalars J f).mapDerivedCategoryFactors.hom.app
        K ≫ Q.map ((NatTrans.mapHomologicalComplex
          (Sheaf.restrictScalarsCompIso J f g gf hgf).hom (.up ℤ)).app K) ≫
      (Sheaf.restrictScalars J gf).mapDerivedCategoryFactors.inv.app K := by
    rw [← reassoc_of% h₂]
    simp
  simp only [Sheaf.derivedRestrictScalarsCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, e₁, e₂, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rfl

end Restrict

section Tower

variable {A : ℕ → Type (u + 1)} [∀ n, CommRing (A n)] {φ : ∀ n, A (n + 1) →+* A n}
  (L : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (A n))))
  (t : ∀ n : ℕ, L (n + 1) ⟶ (Sheaf.derivedRestrictScalars J (φ n)).obj (L n))

/-- K-flat models of the levels of a tower, chosen inductively so that the transition maps are
represented by chain maps (`DerivedCategory.towerModelMap`). -/
noncomputable def towerModel (n : ℕ) : KFlatModel (L n) :=
  Nat.rec (motive := fun n ↦ KFlatModel (L n)) (KFlatModel.nonempty (L 0)).some
    (fun n M ↦ (KFlatModel.exists_hom _ M (t n)).choose) n

lemma towerModel_succ (n : ℕ) :
    towerModel L t (n + 1) = (KFlatModel.exists_hom _ (towerModel L t n) (t n)).choose :=
  rfl

/-- The chain maps `P_{n+1} ⟶ Res P_n` representing the transition maps of a tower. -/
noncomputable def towerModelMap (n : ℕ) :
    (towerModel L t (n + 1)).P ⟶ ((Sheaf.restrictScalars J (φ n)).mapHomologicalComplex (.up ℤ)).obj
      (towerModel L t n).P :=
  (KFlatModel.exists_hom _ (towerModel L t n) (t n)).choose_spec.choose

lemma towerModelMap_spec (n : ℕ) :
    Q.map (towerModelMap L t n) ≫ (Sheaf.restrictScalars J (φ n)).mapDerivedCategoryFactors.inv.app
        (towerModel L t n).P ≫
      (Sheaf.derivedRestrictScalars J (φ n)).map (towerModel L t n).iso.hom =
    (towerModel L t (n + 1)).iso.hom ≫ t n :=
  (KFlatModel.exists_hom _ (towerModel L t n) (t n)).choose_spec.choose_spec

end Tower

end DerivedCategory
