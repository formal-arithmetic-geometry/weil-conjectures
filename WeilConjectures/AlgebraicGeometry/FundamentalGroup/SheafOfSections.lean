/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant

/-!
# Finite étale schemes and finite locally constant sheaves of sets

Let `Y` be a scheme. Sending a finite étale `Y`-scheme `P` to its sheaf of sections
`U ↦ Hom_Y(U, P)` on the small étale site is an equivalence between the category `FÉt(Y)` of
finite étale `Y`-schemes and the category `FLC(Y)` of finite locally constant sheaves of sets
(`AlgebraicGeometry.Scheme.FiniteEtale.equivalenceFiniteLocallyConstant`). It is fully faithful
by the Yoneda lemma, and essentially surjective by the representability of finite locally
constant sheaves (`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`).
The stalk of the sheaf of sections of `P` at a geometric point `s` is the geometric fibre `P_s`
(`AlgebraicGeometry.Scheme.FiniteEtale.sheafFiberToSheafEquiv`).

For a connected scheme `Y` and a fundamental group `G` of the fibre functor at `s`, composing
with `AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction` makes `G` act on the stalks of
finite locally constant sheaves of sets, naturally, continuously, and such that the stalk functor
is fully faithful onto `G`-equivariant maps (`AlgebraicGeometry.Scheme.FiniteLocallyConstant.smul`
and the lemmas following it).

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale.toFiniteLocallyConstant`: the sheaf of sections functor
  `FÉt(Y) ⥤ FLC(Y)`.
- `AlgebraicGeometry.Scheme.FiniteEtale.equivalenceFiniteLocallyConstant`: the equivalence
  `FÉt(Y) ≌ FLC(Y)`.
- `AlgebraicGeometry.Scheme.FiniteLocallyConstant.smul`: the action of `π₁(Y, s)` on the stalks
  of finite locally constant sheaves of sets.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

namespace FiniteEtale

/-- The sheaf of sections `U ↦ Hom_Y(U, P)` of a finite étale `Y`-scheme `P`, i.e. the Yoneda
presheaf of `P` viewed as an object of the small étale site, is a sheaf. -/
lemma isSheaf_uliftYoneda (P : Y.FiniteEtale) :
    Presheaf.IsSheaf Y.smallEtaleTopology (uliftYoneda.{u + 1}.obj P.obj) :=
  have : IsFinite P.obj.hom := P.property
  ((isFiniteLocallyConstant_yoneda_and_exists_iso Y).1 P.obj.left P.obj.hom).fst

/-- The sheaf of sections `U ↦ Hom_Y(U, P)` of a finite étale `Y`-scheme `P`. -/
noncomputable abbrev toSheaf (P : Y.FiniteEtale) : Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
  ⟨uliftYoneda.{u + 1}.obj P.obj, isSheaf_uliftYoneda P⟩

/-- Blueprint `thm-galois-lc-etale`: the sheaf of sections of a finite étale `Y`-scheme is
finite locally constant. -/
lemma isFiniteLocallyConstantSheafOfTypes_toSheaf (P : Y.FiniteEtale) :
    IsFiniteLocallyConstantSheafOfTypes (toSheaf P) :=
  have : IsFinite P.obj.hom := P.property
  ((isFiniteLocallyConstant_yoneda_and_exists_iso Y).1 P.obj.left P.obj.hom).snd

variable (Y) in
/-- Blueprint `thm-galois-lc-etale`: the functor `FÉt(Y) ⥤ FLC(Y)` sending a finite étale
`Y`-scheme `P` to its sheaf of sections `U ↦ Hom_Y(U, P)`. -/
noncomputable def toFiniteLocallyConstant : Y.FiniteEtale ⥤ Y.FiniteLocallyConstant :=
  ObjectProperty.lift _
    (ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ uliftYoneda.{u + 1}) isSheaf_uliftYoneda)
    isFiniteLocallyConstantSheafOfTypes_toSheaf

@[simp]
lemma toFiniteLocallyConstant_obj_obj_obj (P : Y.FiniteEtale) :
    ((toFiniteLocallyConstant Y).obj P).obj.obj = uliftYoneda.{u + 1}.obj P.obj := rfl

@[simp]
lemma toFiniteLocallyConstant_map_hom_hom {P Q : Y.FiniteEtale} (f : P ⟶ Q) :
    ((toFiniteLocallyConstant Y).map f).hom.hom = uliftYoneda.{u + 1}.map f.hom := rfl

variable (Y) in
/-- The sheaf of sections functor is fully faithful, by the Yoneda lemma. -/
noncomputable def fullyFaithfulToFiniteLocallyConstant :
    (toFiniteLocallyConstant Y).FullyFaithful :=
  have h : (toFiniteLocallyConstant Y ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ULiftYoneda.fullyFaithful _)
  (h.ofCompFaithful (G := ObjectProperty.ι _ ⋙ ObjectProperty.ι _))

instance : (toFiniteLocallyConstant Y).Full := (fullyFaithfulToFiniteLocallyConstant Y).full

instance : (toFiniteLocallyConstant Y).Faithful := (fullyFaithfulToFiniteLocallyConstant Y).faithful

instance : (toFiniteLocallyConstant Y).EssSurj where
  mem_essImage F := by
    obtain ⟨P, π, _, _, ⟨e⟩⟩ :=
      (isFiniteLocallyConstant_yoneda_and_exists_iso Y).2 F.obj F.property
    let Q : Y.FiniteEtale := ⟨Etale.mk π, inferInstanceAs (IsFinite π)⟩
    exact ⟨Q, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
      ((fullyFaithfulSheafToPresheaf _ _).preimageIso e.symm)⟩⟩

variable (Y) in
/-- Blueprint `thm-galois-lc-etale`: Finite locally constant sheaves and finite etale schemes.

The sheaf of sections functor `P ↦ Hom_Y(-, P)` is an equivalence between finite étale
`Y`-schemes and finite locally constant sheaves of sets on the small étale site of `Y`. -/
noncomputable def equivalenceFiniteLocallyConstant : Y.FiniteEtale ≌ Y.FiniteLocallyConstant :=
  have : (toFiniteLocallyConstant Y).IsEquivalence := { }
  (toFiniteLocallyConstant Y).asEquivalence

section Fiber

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The Yoneda presheaf `U ↦ Hom_Y(U, X)` of an étale `Y`-scheme `X`, with values in
`Type (u + 1)`. -/
abbrev yonedaPresheaf (X : Y.Etale) : Y.Etaleᵒᵖ ⥤ Type (u + 1) := uliftYoneda.{u + 1}.obj X

/-- A morphism `f : Z ⟶ X` of étale `Y`-schemes, as a section over `Z` of the Yoneda presheaf
of `X`. -/
abbrev yonedaSection {X Z : Y.Etale} (f : Z ⟶ X) : (yonedaPresheaf X).obj (op Z) :=
  ULift.up f

/-- The map from the stalk of the Yoneda presheaf of `X` to the geometric fibre `X_s`, sending
the germ of `f : U ⟶ X` at `u ∈ U_s` to `f(u)`. -/
noncomputable def presheafFiberUliftYonedaDesc (X : Y.Etale) :
    (pointSmallEtale s).presheafFiber.obj (yonedaPresheaf X) ⟶
      ULift.{u + 1} ((pointSmallEtale s).fiber.obj X) :=
  (pointSmallEtale s).presheafFiberDesc (P := yonedaPresheaf X)
    (fun Z z ↦ TypeCat.ofHom fun f : ULift.{u + 1} (Z ⟶ X) ↦
      ULift.up ((pointSmallEtale s).fiber.map f.down z)) (fun Z Z' g z ↦ by
      ext f
      simp)

lemma presheafFiberUliftYonedaDesc_toPresheafFiber (X : Y.Etale) {Z : Y.Etale}
    (z : (pointSmallEtale s).fiber.obj Z) (f : Z ⟶ X) :
    (presheafFiberUliftYonedaDesc s X)
      ((pointSmallEtale s).toPresheafFiber Z z (yonedaPresheaf X) (yonedaSection f)) =
      ULift.up ((pointSmallEtale s).fiber.map f z) :=
  ConcreteCategory.congr_hom
    ((pointSmallEtale s).toPresheafFiber_presheafFiberDesc (P := yonedaPresheaf X) _ _ Z z)
    (yonedaSection f)

/-- The stalk at a geometric point `s` of the Yoneda presheaf `U ↦ Hom_Y(U, X)` of an étale
`Y`-scheme `X` is the geometric fibre `X_s`: the germ of `f : U ⟶ X` at a point `u` of `U_s`
is the point `f(u)` of `X_s`. -/
noncomputable def presheafFiberUliftYonedaEquiv (X : Y.Etale) :
    (pointSmallEtale s).presheafFiber.obj (yonedaPresheaf X) ≃
      ULift.{u + 1} ((pointSmallEtale s).fiber.obj X) where
  toFun := presheafFiberUliftYonedaDesc s X
  invFun x := (pointSmallEtale s).toPresheafFiber X x.down (yonedaPresheaf X)
    (yonedaSection (𝟙 X))
  left_inv p := by
    obtain ⟨Z, z, f, rfl⟩ := (pointSmallEtale s).toPresheafFiber_jointly_surjective
      (P := yonedaPresheaf X) p
    change (pointSmallEtale s).toPresheafFiber X _ (yonedaPresheaf X)
      (yonedaSection (𝟙 X)) =
        (pointSmallEtale s).toPresheafFiber Z z (yonedaPresheaf X) (yonedaSection f.down)
    rw [presheafFiberUliftYonedaDesc_toPresheafFiber,
      ← GrothendieckTopology.Point.toPresheafFiber_w_apply]
    congr 1
    ext
    simp
  right_inv x := by
    change presheafFiberUliftYonedaDesc s X _ = x
    rw [presheafFiberUliftYonedaDesc_toPresheafFiber]
    simp

@[simp]
lemma presheafFiberUliftYonedaEquiv_toPresheafFiber (X : Y.Etale) {Z : Y.Etale}
    (z : (pointSmallEtale s).fiber.obj Z) (f : Z ⟶ X) :
    presheafFiberUliftYonedaEquiv s X
      ((pointSmallEtale s).toPresheafFiber Z z (yonedaPresheaf X) (yonedaSection f)) =
      ULift.up ((pointSmallEtale s).fiber.map f z) :=
  by exact presheafFiberUliftYonedaDesc_toPresheafFiber s X z f

lemma presheafFiberUliftYonedaEquiv_naturality {X X' : Y.Etale} (g : X ⟶ X')
    (p : (pointSmallEtale s).presheafFiber.obj (yonedaPresheaf X)) :
    presheafFiberUliftYonedaEquiv s X'
      ((pointSmallEtale s).presheafFiber.map (uliftYoneda.{u + 1}.map g) p) =
      ULift.up ((pointSmallEtale s).fiber.map g (presheafFiberUliftYonedaEquiv s X p).down) := by
  obtain ⟨Z, z, f, rfl⟩ := (pointSmallEtale s).toPresheafFiber_jointly_surjective
    (P := yonedaPresheaf X) p
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  change presheafFiberUliftYonedaEquiv s X' ((pointSmallEtale s).toPresheafFiber Z z
    (yonedaPresheaf X')
    (yonedaSection (f.down ≫ g))) = ULift.up ((pointSmallEtale s).fiber.map g
      (presheafFiberUliftYonedaEquiv s X ((pointSmallEtale s).toPresheafFiber Z z
        (yonedaPresheaf X)
        (yonedaSection f.down))).down)
  simp

/-- The stalk of the sheaf of sections of a finite étale `Y`-scheme `P` at a geometric point `s`
is the geometric fibre `P_s`. -/
noncomputable def sheafFiberToSheafEquiv (P : Y.FiniteEtale) :
    (pointSmallEtale s).sheafFiber.obj ((toFiniteLocallyConstant Y).obj P).obj ≃
      ULift.{u + 1} ((fiber s).obj P) :=
  presheafFiberUliftYonedaEquiv s P.obj

lemma sheafFiberToSheafEquiv_naturality {P Q : Y.FiniteEtale} (f : P ⟶ Q)
    (p : (pointSmallEtale s).sheafFiber.obj ((toFiniteLocallyConstant Y).obj P).obj) :
    sheafFiberToSheafEquiv s Q
      ((pointSmallEtale s).sheafFiber.map ((toFiniteLocallyConstant Y).map f).hom p) =
      ULift.up ((fiber s).map f (sheafFiberToSheafEquiv s P p).down) :=
  presheafFiberUliftYonedaEquiv_naturality s f.hom p

end Fiber

end FiniteEtale

end AlgebraicGeometry.Scheme
