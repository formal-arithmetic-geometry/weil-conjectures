/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!
# An invertible sheaf of modules is locally isomorphic to the structure sheaf

A sheaf of modules `M` on a scheme `X` is invertible, in the sense of
`WeilConjectures.AlgebraicGeometry.Modules.Picard`, when there is a sheaf of modules `N` and an
isomorphism `M ⊗ N ≅ 𝒪ₓ`. This file proves that such an `M` is a line bundle in the geometric
sense: every point of `X` has an open neighbourhood `W` on which `M` is isomorphic to the
structure sheaf.

The proof has two halves.

The first is a comparison between the tensor product of two sheaves of modules and the
*sectionwise* tensor product of the underlying presheaves of modules. The former is by
construction the sheafification of the latter, so there is a canonical morphism
`SheafOfModules.tensorPresheafHom` from the sectionwise tensor product to `M ⊗ N`, and it becomes
an isomorphism after sheafification; over a topological space this makes it locally surjective.
Composing it with an isomorphism `M ⊗ N ≅ 𝒪ₓ` gives a pairing
`AlgebraicGeometry.Scheme.Modules.tensorPairing` of a section of `M` and a section of `N` over an
open `U` with values in `Γ(X, U)`, and local surjectivity says that `1` is locally a finite sum of
such products. Since the local rings of `X` are local rings, one of the summands has a germ which
is a unit at any prescribed point, and shrinking to a basic open set makes that product itself a
unit: this is `AlgebraicGeometry.Scheme.Modules.exists_tensorPairing_eq_one`.

The second half is formal. Two sections `m` of `M` and `n` of `N` over `W` whose product is `1`
give a morphism `𝒪_W ⟶ M|_W`, multiplication by `m`, and a morphism `M|_W ⟶ 𝒪_W`, pairing with
`n`, whose composite is the identity of `𝒪_W`. A split monomorphism from the tensor unit to an
invertible object of a monoidal category is an isomorphism
(`CategoryTheory.MonoidalCategory.isIso_of_comp_eq_id`), and `M|_W` is invertible because the
pullback of an invertible sheaf of modules is invertible.

## Main declarations

- `SheafOfModules.tensorPresheafHom`: the comparison morphism from the sectionwise tensor product
  of the underlying presheaves of modules of `F` and `G` to the underlying presheaf of modules of
  `F ⊗ G`, together with `SheafOfModules.w_toPresheaf_map_tensorPresheafHom`, the statement that
  it becomes an isomorphism after sheafification.
- `AlgebraicGeometry.Scheme.Modules.tensorPairing`: the pairing on sections determined by an
  isomorphism `M ⊗ N ≅ 𝒪ₓ`.
- `SheafOfModules.Invertible.exists_restrict_iso_unit`: **an invertible sheaf of modules on a
  scheme is locally isomorphic to the structure sheaf.**
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite TensorProduct

universe v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

variable (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))

/-- The underlying presheaf of modules of a sheaf of modules, spelled as a presheaf of modules
over the underlying presheaf of rings of `R`, so that the monoidal structure of
`PresheafOfModules` is found by instance resolution. -/
abbrev presheafOfModules : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (SheafOfModules.forget _).obj F

/-- The sheafification of the underlying presheaf of modules of a sheaf of modules is that
sheaf of modules; this is the counit of the sheafification adjunction. -/
noncomputable def sheafificationObjIso : (sheafification R).obj (presheafOfModules F) ≅ F :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).counit).app F

/-- **The tensor product of two sheaves of modules is the sheafification of the sectionwise
tensor product** of the underlying presheaves of modules. -/
noncomputable def tensorSheafificationIso :
    (sheafification R).obj (presheafOfModules F ⊗ presheafOfModules G) ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (sheafification R) _ _).symm ≪≫
    tensorIso (sheafificationObjIso F) (sheafificationObjIso G)

/-- The canonical morphism from the sectionwise tensor product of the underlying presheaves of
modules of `F` and `G` to the underlying presheaf of modules of `F ⊗ G`. -/
noncomputable def tensorPresheafHom :
    presheafOfModules F ⊗ presheafOfModules G ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).obj
          (presheafOfModules (F ⊗ G)) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).homEquiv _ _
      (tensorSheafificationIso F G).hom

lemma toPresheaf_map_tensorPresheafHom :
    (PresheafOfModules.toPresheaf _).map (tensorPresheafHom F G) =
      CategoryTheory.toSheafify J (presheafOfModules F ⊗ presheafOfModules G).presheaf ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          (tensorSheafificationIso F G).hom := rfl

/-- The comparison morphism from the sectionwise tensor product to the tensor product becomes an
isomorphism after sheafification; in particular it is locally bijective. -/
lemma w_toPresheaf_map_tensorPresheafHom :
    J.W ((PresheafOfModules.toPresheaf _).map (tensorPresheafHom F G)) := by
  have h : J.W ((SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      PresheafOfModules.toPresheaf _).map (tensorSheafificationIso F G).hom) :=
    J.W.of_isIso _
  rw [toPresheaf_map_tensorPresheafHom]
  exact J.W.comp_mem _ _ (J.W_toSheafify _) h

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

instance (U : X.Opens) (M : X.Modules) :
    Module Γ(X, U) ((SheafOfModules.presheafOfModules M).obj (op U)) :=
  inferInstanceAs (Module Γ(X, U) Γ(M, U))

variable (e : M ⊗ N ≅ SheafOfModules.unit X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
/-- The pairing of sections of `M` and of `N` over an open `U` determined by an isomorphism
`M ⊗ N ≅ 𝒪_X`: a section of `M` and a section of `N` over `U` have a product in `Γ(X, U)`,
obtained by pushing their tensor product through the comparison morphism
`SheafOfModules.tensorPresheafHom` and then through `e`. -/
noncomputable def tensorPairing (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  LinearMap.compr₂ (TensorProduct.mk Γ(X, U) Γ(M, U) Γ(N, U))
    { toFun := fun t ↦ Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom t)
      map_add' := fun t t' ↦ by rw [map_add, map_add]
      map_smul' := fun r t ↦ by rw [RingHom.id_apply, _root_.map_smul, Hom.app_smul] }

variable {e}

lemma tensorPairing_apply (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    tensorPairing e U m n =
      Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom
        (m ⊗ₜ[Γ(X, U)] n)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma tensorPairing_tmul (U : X.Opens) (t : Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) :
    Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom t) =
      TensorProduct.lift (tensorPairing e U) t := by
  induction t with
  | zero => simp
  | tmul m n => rfl
  | add t t' h h' => rw [map_add, map_add, map_add, h, h']

set_option backward.isDefEq.respectTransparency false in
/-- The pairing of sections is compatible with restriction to a smaller open subset. -/
lemma map_tensorPairing {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    X.presheaf.map i.op (tensorPairing e U m n) =
      tensorPairing e V (M.presheaf.map i.op m) (N.presheaf.map i.op n) := by
  rw [tensorPairing_apply, tensorPairing_apply]
  have h₁ := CategoryTheory.congr_fun ((Hom.mapPresheaf e.hom).naturality i.op)
    (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom (m ⊗ₜ[Γ(X, U)] n))
  have h₂ := PresheafOfModules.naturality_apply (SheafOfModules.tensorPresheafHom M N) i.op
    (m ⊗ₜ[Γ(X, U)] n)
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at h₁
  refine h₁.symm.trans ?_
  exact congrArg (ConcreteCategory.hom (Hom.app e.hom V)) h₂.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Any point has a neighbourhood on which `M` and `N` have sections pairing to `1`.** -/
lemma exists_tensorPairing_eq_one (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V) (m : Γ(M, V)) (n : Γ(N, V)), tensorPairing e V m n = 1 := by
  have h1 : TopCat.Presheaf.IsLocallySurjective
      ((PresheafOfModules.toPresheaf _).map (SheafOfModules.tensorPresheafHom M N)) :=
    (SheafOfModules.w_toPresheaf_map_tensorPresheafHom M N).isLocallySurjective
  obtain ⟨V, hVle, ⟨s, hs⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).1 h1 ⊤ (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) x trivial
  have key : TensorProduct.lift (tensorPairing e V) s = 1 := by
    rw [← tensorPairing_tmul]
    have hs' : ((SheafOfModules.tensorPresheafHom M N).app (op V)).hom s =
        (M ⊗ N).presheaf.map (homOfLE hVle).op (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) := hs
    have hnat := CategoryTheory.congr_fun ((Hom.mapPresheaf e.hom).naturality (homOfLE hVle).op)
      (Hom.app e.inv ⊤ (1 : Γ(X, ⊤)))
    simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hnat
    have hone : Hom.app e.hom ⊤ (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app,
        ConcreteCategory.id_apply]
    rw [hs', hnat, hone]
    exact (X.presheaf.map (homOfLE hVle).op).hom.map_one
  obtain ⟨t, key⟩ : ∃ t : Γ(M, V) ⊗[Γ(X, V)] Γ(N, V),
      TensorProduct.lift (tensorPairing e V) t = 1 := ⟨s, key⟩
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  rw [hS, map_sum] at key
  simp only [TensorProduct.lift.tmul] at key
  have hgerm : IsUnit (∑ p ∈ S, X.presheaf.germ V x hxV (tensorPairing e V p.1 p.2)) := by
    rw [← map_sum, key, map_one]
    exact isUnit_one
  obtain ⟨p, -, hp⟩ := IsLocalRing.exists_of_isUnit_sum hgerm
  have hunit : IsUnit (X.presheaf.map
      (homOfLE (X.basicOpen_le (tensorPairing e V p.1 p.2))).op (tensorPairing e V p.1 p.2)) :=
    X.toRingedSpace.isUnit_res_basicOpen _
  obtain ⟨u, hu⟩ := hunit
  refine ⟨X.basicOpen (tensorPairing e V p.1 p.2),
    (Scheme.mem_basicOpen X _ x hxV).2 hp,
    M.presheaf.map (homOfLE (X.basicOpen_le _)).op p.1,
    ((u⁻¹ : (Γ(X, X.basicOpen (tensorPairing e V p.1 p.2)))ˣ) :
      Γ(X, X.basicOpen (tensorPairing e V p.1 p.2))) •
      N.presheaf.map (homOfLE (X.basicOpen_le _)).op p.2, ?_⟩
  rw [_root_.map_smul, ← map_tensorPairing, ← hu, smul_eq_mul]
  exact u.inv_mul

section Restrict

variable (e) {W : X.Opens}

/-- Multiplication by the restriction of a section `m` of `M` over `W` to a smaller open `V`. -/
noncomputable def smulSection (m : Γ(M, W)) (V : X.Opens) (hV : V ≤ W) : Γ(X, V) →+ Γ(M, V) :=
  AddMonoidHom.mk' (fun r ↦ r • M.presheaf.map (homOfLE hV).op m) (fun r r' ↦ add_smul r r' _)

lemma smulSection_smul (m : Γ(M, W)) (V : X.Opens) (hV : V ≤ W) (r z : Γ(X, V)) :
    smulSection m V hV (r • z) = r • smulSection m V hV z :=
  mul_smul r z _

lemma map_smulSection (m : Γ(M, W)) {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ W) (i : V' ⟶ V)
    (r : Γ(X, V)) :
    M.presheaf.map i.op (smulSection m V hV r) = smulSection m V' hV' (X.presheaf.map i.op r) := by
  rw [smulSection, smulSection]
  simp only [AddMonoidHom.mk'_apply]
  rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

/-- Pairing with the restriction of a section `n` of `N` over `W` to a smaller open `V`. -/
noncomputable def pairSection (n : Γ(N, W)) (V : X.Opens) (hV : V ≤ W) : Γ(M, V) →+ Γ(X, V) :=
  AddMonoidHom.mk' (fun z ↦ tensorPairing e V z (N.presheaf.map (homOfLE hV).op n))
    (fun z z' ↦ by rw [map_add]; rfl)

lemma pairSection_smul (n : Γ(N, W)) (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V)) (z : Γ(M, V)) :
    pairSection e n V hV (r • z) = r • pairSection e n V hV z := by
  rw [pairSection]
  simp only [AddMonoidHom.mk'_apply]
  rw [_root_.map_smul]
  rfl

lemma map_pairSection (n : Γ(N, W)) {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ W) (i : V' ⟶ V)
    (z : Γ(M, V)) :
    X.presheaf.map i.op (pairSection e n V hV z) =
      pairSection e n V' hV' (M.presheaf.map i.op z) := by
  rw [pairSection, pairSection]
  simp only [AddMonoidHom.mk'_apply]
  rw [map_tensorPairing, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 3

lemma pairSection_smulSection (m : Γ(M, W)) (n : Γ(N, W)) (h : tensorPairing e W m n = 1)
    (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V)) :
    pairSection e n V hV (smulSection m V hV r) = r := by
  rw [smulSection]
  simp only [AddMonoidHom.mk'_apply]
  rw [pairSection_smul, pairSection]
  simp only [AddMonoidHom.mk'_apply, smul_eq_mul]
  rw [← map_tensorPairing, h, map_one, mul_one]

/-- Multiplication by a section `m` of `M` over `W`, as a morphism `𝒪_X|_W ⟶ M|_W` of sheaves
of modules on the open subscheme `W`. -/
noncomputable def smulRestrictHom (m : Γ(M, W)) :
    restrict (SheafOfModules.unit X.ringCatSheaf) W.ι ⟶ restrict M W.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimage <|
    PresheafOfModules.homMk
      { app := fun U' ↦ AddCommGrpCat.ofHom (smulSection m (W.ι ''ᵁ U'.unop) (W.ι_image_le _))
        naturality := fun {U' V'} f ↦ by
          ext r
          exact (map_smulSection m _ _ _ r).symm }
      (fun U' r z ↦ smulSection_smul m _ _ ((W.ι.appIso U'.unop).inv r) z)

set_option maxHeartbeats 2000000 in
-- The naturality of the pairing is checked up to the definitional unfolding of
-- `AlgebraicGeometry.Scheme.Modules.tensorPairing`, which goes through the sheafification of the
-- sectionwise tensor product and is therefore expensive.
set_option backward.isDefEq.respectTransparency false in
/-- Pairing with a section `n` of `N` over `W`, as a morphism `M|_W ⟶ 𝒪_X|_W`. -/
noncomputable def pairRestrictHom (n : Γ(N, W)) :
    restrict M W.ι ⟶ restrict (SheafOfModules.unit X.ringCatSheaf) W.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimage <|
    PresheafOfModules.homMk
      { app := fun U' ↦ AddCommGrpCat.ofHom (pairSection e n (W.ι ''ᵁ U'.unop) (W.ι_image_le _))
        naturality := fun {_U' _V'} _f ↦ AddCommGrpCat.hom_ext
          (AddMonoidHom.ext fun z ↦ (map_pairSection e n _ _ _ z).symm) }
      (fun U' r z ↦ pairSection_smul e n _ _ ((W.ι.appIso U'.unop).inv r) z)

/-- If the sections `m` of `M` and `n` of `N` over `W` pair to `1`, then multiplication by `m`
is a split monomorphism `𝒪_X|_W ⟶ M|_W`. -/
lemma smulRestrictHom_comp_pairRestrictHom (m : Γ(M, W)) (n : Γ(N, W))
    (h : tensorPairing e W m n = 1) :
    smulRestrictHom m ≫ pairRestrictHom e n = 𝟙 _ := by
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  ext U' r
  exact pairSection_smulSection e m n h _ _ r

end Restrict

/-- The tensor unit of the category of `𝒪_W`-modules on an open subscheme `W` of `X` is the
restriction of the structure sheaf of `X`. -/
noncomputable def tensorUnitRestrictIso (W : X.Opens) :
    𝟙_ W.toScheme.Modules ≅ restrict (SheafOfModules.unit X.ringCatSheaf) W.ι :=
  SheafOfModules.tensorUnitIso W.toScheme.sheaf ≪≫ (restrictUnitIso W.ι).symm

/-- **An invertible sheaf of modules on a scheme is locally trivial**: every point has an open
neighbourhood on which the sheaf is isomorphic to the structure sheaf. -/
theorem _root_.SheafOfModules.Invertible.exists_restrict_iso_unit {M : X.Modules}
    (hM : M.Invertible) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧
      Nonempty (M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  obtain ⟨N, ⟨e₀⟩⟩ := SheafOfModules.invertible_iff_exists.{u, u, u}.1 hM
  obtain ⟨W, hxW, m, n, h⟩ :=
    exists_tensorPairing_eq_one (e := e₀ ≪≫ SheafOfModules.tensorUnitIso X.sheaf) x
  refine ⟨W, hxW, ?_⟩
  have hMW : (M.restrict W.ι).Invertible :=
    (hM.pullback W.ι).of_iso ((restrictFunctorIsoPullback W.ι).app M).symm
  obtain ⟨N', ⟨eW⟩⟩ : ∃ N' : W.toScheme.Modules,
      Nonempty (M.restrict W.ι ⊗ N' ≅ 𝟙_ W.toScheme.Modules) :=
    SheafOfModules.invertible_iff_exists.{u, u, u}.1 hMW
  have key : ((tensorUnitRestrictIso W).hom ≫ smulRestrictHom m) ≫
      (pairRestrictHom (e₀ ≪≫ SheafOfModules.tensorUnitIso X.sheaf) n ≫
        (tensorUnitRestrictIso W).inv) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (smulRestrictHom m),
      smulRestrictHom_comp_pairRestrictHom _ m n h, Category.id_comp,
      (tensorUnitRestrictIso W).hom_inv_id]
  have : IsIso ((tensorUnitRestrictIso W).hom ≫ smulRestrictHom m) :=
    MonoidalCategory.isIso_of_comp_eq_id eW (β_ N' (M.restrict W.ι) ≪≫ eW) key
  exact ⟨(asIso ((tensorUnitRestrictIso W).hom ≫ smulRestrictHom m)).symm ≪≫
    SheafOfModules.tensorUnitIso W.toScheme.sheaf⟩

/-- An invertible sheaf of modules on a scheme is locally isomorphic to the tensor unit. -/
theorem _root_.SheafOfModules.Invertible.exists_restrict_iso_tensorUnit {M : X.Modules}
    (hM : M.Invertible) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ Nonempty (M.restrict W.ι ≅ 𝟙_ W.toScheme.Modules) := by
  obtain ⟨W, hxW, ⟨i⟩⟩ := hM.exists_restrict_iso_unit x
  exact ⟨W, hxW, ⟨i ≪≫ (SheafOfModules.tensorUnitIso W.toScheme.sheaf).symm⟩⟩

end AlgebraicGeometry.Scheme.Modules
