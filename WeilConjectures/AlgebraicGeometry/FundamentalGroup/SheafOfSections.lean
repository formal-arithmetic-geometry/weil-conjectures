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
(`AlgebraicGeometry.Scheme.FiniteEtale.sectionsEquivalence`). It is fully faithful
by the Yoneda lemma, and essentially surjective by the representability of finite locally
constant sheaves (`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`).
The stalk of the sheaf of sections of `P` at a geometric point `s` is the geometric fibre `P_s`
(`AlgebraicGeometry.Scheme.FiniteEtale.sheafFiberSectionsSheafEquiv`).

For a connected scheme `Y` and a fundamental group `G` of the fibre functor at `s`, composing
with `AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction` makes `G` act on the stalks of
finite locally constant sheaves of sets, naturally, continuously, and such that the stalk functor
is fully faithful onto `G`-equivariant maps (`AlgebraicGeometry.Scheme.FiniteLocallyConstant.smul`
and the lemmas following it).

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale.sectionsFunctor`: the sheaf of sections functor
  `FÉt(Y) ⥤ FLC(Y)`.
- `AlgebraicGeometry.Scheme.FiniteEtale.sectionsEquivalence`: the equivalence
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
noncomputable abbrev sectionsSheaf (P : Y.FiniteEtale) : Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
  ⟨uliftYoneda.{u + 1}.obj P.obj, isSheaf_uliftYoneda P⟩

/-- Blueprint `thm-galois-lc-etale`: the sheaf of sections of a finite étale `Y`-scheme is
finite locally constant. -/
lemma isFiniteLocallyConstantSheafOfTypes_sectionsSheaf (P : Y.FiniteEtale) :
    IsFiniteLocallyConstantSheafOfTypes (sectionsSheaf P) :=
  have : IsFinite P.obj.hom := P.property
  ((isFiniteLocallyConstant_yoneda_and_exists_iso Y).1 P.obj.left P.obj.hom).snd

variable (Y) in
/-- Blueprint `thm-galois-lc-etale`: the functor `FÉt(Y) ⥤ FLC(Y)` sending a finite étale
`Y`-scheme `P` to its sheaf of sections `U ↦ Hom_Y(U, P)`. -/
noncomputable def sectionsFunctor : Y.FiniteEtale ⥤ Y.FiniteLocallyConstant :=
  ObjectProperty.lift _
    (ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ uliftYoneda.{u + 1}) isSheaf_uliftYoneda)
    isFiniteLocallyConstantSheafOfTypes_sectionsSheaf

@[simp]
lemma sectionsFunctor_obj_obj_obj (P : Y.FiniteEtale) :
    ((sectionsFunctor Y).obj P).obj.obj = uliftYoneda.{u + 1}.obj P.obj := rfl

@[simp]
lemma sectionsFunctor_map_hom_hom {P Q : Y.FiniteEtale} (f : P ⟶ Q) :
    ((sectionsFunctor Y).map f).hom.hom = uliftYoneda.{u + 1}.map f.hom := rfl

variable (Y) in
/-- The sheaf of sections functor is fully faithful, by the Yoneda lemma. -/
noncomputable def fullyFaithfulSectionsFunctor :
    (sectionsFunctor Y).FullyFaithful :=
  have h : (sectionsFunctor Y ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ULiftYoneda.fullyFaithful _)
  (h.ofCompFaithful (G := ObjectProperty.ι _ ⋙ ObjectProperty.ι _))

instance : (sectionsFunctor Y).Full := (fullyFaithfulSectionsFunctor Y).full

instance : (sectionsFunctor Y).Faithful := (fullyFaithfulSectionsFunctor Y).faithful

instance : (sectionsFunctor Y).EssSurj where
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
noncomputable def sectionsEquivalence : Y.FiniteEtale ≌ Y.FiniteLocallyConstant :=
  have : (sectionsFunctor Y).IsEquivalence := { }
  (sectionsFunctor Y).asEquivalence

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

lemma exists_eq_toPresheafFiber_yonedaSection (X : Y.Etale)
    (p : (pointSmallEtale s).presheafFiber.obj (yonedaPresheaf X)) :
    ∃ (Z : Y.Etale) (z : (pointSmallEtale s).fiber.obj Z) (f : Z ⟶ X),
      p = (pointSmallEtale s).toPresheafFiber Z z (yonedaPresheaf X) (yonedaSection f) := by
  obtain ⟨Z, z, f, rfl⟩ := (pointSmallEtale s).toPresheafFiber_jointly_surjective
    (P := yonedaPresheaf X) p
  exact ⟨Z, z, (show ULift.{u + 1} (Z ⟶ X) from f).down, rfl⟩

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
    obtain ⟨Z, z, f, rfl⟩ := exists_eq_toPresheafFiber_yonedaSection s X p
    change (pointSmallEtale s).toPresheafFiber X _ (yonedaPresheaf X)
      (yonedaSection (𝟙 X)) =
        (pointSmallEtale s).toPresheafFiber Z z (yonedaPresheaf X) (yonedaSection f)
    rw [presheafFiberUliftYonedaDesc_toPresheafFiber,
      ← GrothendieckTopology.Point.toPresheafFiber_w_apply]
    congr 1
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
  obtain ⟨Z, z, f, rfl⟩ := exists_eq_toPresheafFiber_yonedaSection s X p
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  change presheafFiberUliftYonedaEquiv s X' ((pointSmallEtale s).toPresheafFiber Z z
    (yonedaPresheaf X')
    (yonedaSection (f ≫ g))) = ULift.up ((pointSmallEtale s).fiber.map g
      (presheafFiberUliftYonedaEquiv s X ((pointSmallEtale s).toPresheafFiber Z z
        (yonedaPresheaf X)
        (yonedaSection f))).down)
  simp

/-- The stalk of the sheaf of sections of a finite étale `Y`-scheme `P` at a geometric point `s`
is the geometric fibre `P_s`. -/
noncomputable def sheafFiberSectionsSheafEquiv (P : Y.FiniteEtale) :
    (pointSmallEtale s).sheafFiber.obj ((sectionsFunctor Y).obj P).obj ≃
      ULift.{u + 1} ((fiber s).obj P) :=
  presheafFiberUliftYonedaEquiv s P.obj

lemma sheafFiberSectionsSheafEquiv_naturality {P Q : Y.FiniteEtale} (f : P ⟶ Q)
    (p : (pointSmallEtale s).sheafFiber.obj ((sectionsFunctor Y).obj P).obj) :
    sheafFiberSectionsSheafEquiv s Q
      ((pointSmallEtale s).sheafFiber.map ((sectionsFunctor Y).map f).hom p) =
      ULift.up ((fiber s).map f (sheafFiberSectionsSheafEquiv s P p).down) :=
  presheafFiberUliftYonedaEquiv_naturality s f.hom p

end Fiber

end FiniteEtale
namespace FiniteLocallyConstant

open FiniteEtale

section Action

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The stalk `F_s` of a finite locally constant sheaf of sets at a geometric point `s`. -/
noncomputable abbrev stalk (F : Y.FiniteLocallyConstant) : Type (u + 1) :=
  (pointSmallEtale s).sheafFiber.obj F.obj

/-- The map on stalks induced by a morphism of finite locally constant sheaves of sets. -/
noncomputable abbrev stalkMap {F F' : Y.FiniteLocallyConstant} (f : F ⟶ F') : stalk s F → stalk s F' :=
  (pointSmallEtale s).sheafFiber.map f.hom

lemma stalkMap_comp {F F' F'' : Y.FiniteLocallyConstant} (f : F ⟶ F') (f' : F' ⟶ F'')
    (x : stalk s F) : stalkMap s (f ≫ f') x = stalkMap s f' (stalkMap s f x) := by
  simp [stalkMap]

lemma stalkMap_id (F : Y.FiniteLocallyConstant) (x : stalk s F) : stalkMap s (𝟙 F) x = x := by
  simp [stalkMap]

/-- An identification `F ≅ Hom_Y(-, P)` of a finite locally constant sheaf of sets with the sheaf
of sections of a finite étale `Y`-scheme `P` identifies the stalk `F_s` with the geometric fibre
`P_s`. -/
noncomputable def isoStalkEquiv {F : Y.FiniteLocallyConstant} {P : Y.FiniteEtale}
    (i : F ≅ (sectionsFunctor Y).obj P) : stalk s F ≃ ULift.{u + 1} ((FiniteEtale.fiber s).obj P) :=
  ((pointSmallEtale s).sheafFiber.mapIso ((ObjectProperty.ι _).mapIso i)).toEquiv.trans
    (sheafFiberSectionsSheafEquiv s P)

lemma isoStalkEquiv_stalkMap {F F' : Y.FiniteLocallyConstant} {P P' : Y.FiniteEtale}
    (i : F ≅ (sectionsFunctor Y).obj P) (i' : F' ≅ (sectionsFunctor Y).obj P')
    (f : F ⟶ F') (φ : P ⟶ P') (h : f ≫ i'.hom = i.hom ≫ (sectionsFunctor Y).map φ)
    (x : stalk s F) :
    isoStalkEquiv s i' (stalkMap s f x) =
      ULift.up ((FiniteEtale.fiber s).map φ (isoStalkEquiv s i x).down) := by
  have h' := congrArg (fun k ↦ stalkMap s k x) h
  simp only [stalkMap_comp] at h'
  change sheafFiberSectionsSheafEquiv s P' (stalkMap s i'.hom (stalkMap s f x)) = _
  rw [h']
  exact sheafFiberSectionsSheafEquiv_naturality s φ _

variable (Y) in
/-- The finite étale `Y`-scheme representing a finite locally constant sheaf of sets. -/
noncomputable abbrev rep (F : Y.FiniteLocallyConstant) : Y.FiniteEtale :=
  (sectionsEquivalence Y).inverse.obj F

/-- The chosen identification of a finite locally constant sheaf of sets with the sheaf of
sections of its representing finite étale `Y`-scheme. -/
noncomputable abbrev repIso (F : Y.FiniteLocallyConstant) :
    F ≅ (sectionsFunctor Y).obj (rep Y F) :=
  ((sectionsEquivalence Y).counitIso.app F).symm

/-- The stalk `F_s` of a finite locally constant sheaf of sets is the geometric fibre of its
representing finite étale `Y`-scheme. -/
noncomputable abbrev repStalkEquiv (F : Y.FiniteLocallyConstant) :
    stalk s F ≃ ULift.{u + 1} ((FiniteEtale.fiber s).obj (rep Y F)) :=
  isoStalkEquiv s (repIso F)

lemma exists_sectionsFunctor_map_eq {P P' : Y.FiniteEtale}
    (f : (sectionsFunctor Y).obj P ⟶ (sectionsFunctor Y).obj P') :
    ∃ φ : P ⟶ P', (sectionsFunctor Y).map φ = f :=
  (sectionsFunctor Y).map_surjective f

variable [ConnectedSpace Y] (G : Type u) [Group G] [∀ P, MulAction G ((FiniteEtale.fiber s).obj P)]
  [IsNaturalSMul (FiniteEtale.fiber s) G]

/-- Blueprint `thm-galois-fundamental`: the action of a fundamental group `G = π₁(Y, s)` on the
stalk `F_s` of a finite locally constant sheaf of sets `F`, transported from its action on the
geometric fibre of the finite étale `Y`-scheme representing `F`. -/
noncomputable def smul {F : Y.FiniteLocallyConstant} (g : G) (x : stalk s F) : stalk s F :=
  (repStalkEquiv s F).symm (ULift.up (g • (repStalkEquiv s F x).down))

lemma isoStalkEquiv_smul {F : Y.FiniteLocallyConstant} {P : Y.FiniteEtale}
    (i : F ≅ (sectionsFunctor Y).obj P) (g : G) (x : stalk s F) :
    isoStalkEquiv s i (smul s G g x) = ULift.up (g • (isoStalkEquiv s i x).down) := by
  obtain ⟨φ, hφ⟩ := exists_sectionsFunctor_map_eq ((repIso F).inv ≫ i.hom)
  have h : 𝟙 F ≫ i.hom = (repIso F).hom ≫ (sectionsFunctor Y).map φ := by
    rw [hφ, Iso.hom_inv_id_assoc, Category.id_comp]
  have key (y : stalk s F) :
      isoStalkEquiv s i y = ULift.up ((FiniteEtale.fiber s).map φ (repStalkEquiv s F y).down) := by
    simpa [stalkMap_id] using isoStalkEquiv_stalkMap s (repIso F) i (𝟙 F) φ h y
  rw [key, key]
  unfold smul
  rw [Equiv.apply_symm_apply, IsNaturalSMul.naturality]

lemma stalkMap_smul {F F' : Y.FiniteLocallyConstant} (f : F ⟶ F') (g : G) (x : stalk s F) :
    stalkMap s f (smul s G g x) = smul s G g (stalkMap s f x) := by
  obtain ⟨φ, hφ⟩ := exists_sectionsFunctor_map_eq ((repIso F).inv ≫ f ≫ (repIso F').hom)
  have h : f ≫ (repIso F').hom = (repIso F).hom ≫ (sectionsFunctor Y).map φ := by
    rw [hφ, Iso.hom_inv_id_assoc]
  apply (repStalkEquiv s F').injective
  rw [isoStalkEquiv_smul, isoStalkEquiv_stalkMap s _ _ f φ h,
    isoStalkEquiv_stalkMap s _ _ f φ h, isoStalkEquiv_smul, IsNaturalSMul.naturality]

lemma one_smul {F : Y.FiniteLocallyConstant} (x : stalk s F) : smul s G 1 x = x := by
  unfold smul
  rw [_root_.one_smul]
  exact (repStalkEquiv s F).symm_apply_apply x

lemma mul_smul {F : Y.FiniteLocallyConstant} (g h : G) (x : stalk s F) :
    smul s G (g * h) x = smul s G g (smul s G h x) := by
  unfold smul
  rw [Equiv.apply_symm_apply, SemigroupAction.mul_smul]

lemma smul_sectionsFunctor (P : Y.FiniteEtale) (g : G)
    (x : stalk s ((sectionsFunctor Y).obj P)) :
    sheafFiberSectionsSheafEquiv s P (smul s G g x) =
      ULift.up (g • (sheafFiberSectionsSheafEquiv s P x).down) := by
  have := isoStalkEquiv_smul s G (Iso.refl _) g x
  simpa [isoStalkEquiv] using this

/-- The stalk functor is faithful on finite locally constant sheaves of sets. -/
lemma stalkMap_injective {F F' : Y.FiniteLocallyConstant} {f f' : F ⟶ F'}
    (h : ∀ x, stalkMap s f x = stalkMap s f' x) : f = f' := by
  obtain ⟨φ, hφ⟩ := exists_sectionsFunctor_map_eq ((repIso F).inv ≫ f ≫ (repIso F').hom)
  obtain ⟨φ', hφ'⟩ :=
    exists_sectionsFunctor_map_eq ((repIso F).inv ≫ f' ≫ (repIso F').hom)
  have e : φ = φ' := by
    refine (FiniteEtale.fiber s).map_injective (FintypeCat.hom_ext _ _ fun y ↦ ?_)
    obtain ⟨x, hx⟩ := (repStalkEquiv s F).surjective (ULift.up y)
    have h₁ := isoStalkEquiv_stalkMap s _ _ f φ (by rw [hφ, Iso.hom_inv_id_assoc]) x
    have h₂ := isoStalkEquiv_stalkMap s _ _ f' φ' (by rw [hφ', Iso.hom_inv_id_assoc]) x
    rw [h x, h₂, hx] at h₁
    exact (congrArg ULift.down h₁).symm
  rw [← cancel_epi (repIso F).inv, ← cancel_mono (repIso F').hom, Category.assoc,
    Category.assoc, ← hφ, ← hφ', e]

section Fundamental

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber s) G]

open scoped FintypeCatDiscrete in
/-- Blueprint `lem-galois-action-continuous`: the action of `π₁(Y, s)` on the stalk of a finite
locally constant sheaf of sets is continuous, i.e. every stabilizer is open. -/
lemma isOpen_setOf_smul_eq {F : Y.FiniteLocallyConstant} (x : stalk s F) :
    IsOpen {g : G | smul s G g x = x} := by
  have : {g : G | smul s G g x = x} =
      (MulAction.stabilizer G (repStalkEquiv s F x).down : Set G) := by
    ext g
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      have := congrArg (fun y ↦ (repStalkEquiv s F y).down) h
      simpa only [smul, Equiv.apply_symm_apply] using this
    · intro h
      unfold smul
      rw [h]
      exact (repStalkEquiv s F).symm_apply_apply x
  rw [this]
  exact stabilizer_isOpen G _

/-- The stalk functor is full onto `π₁(Y, s)`-equivariant maps: every equivariant map between
the stalks of two finite locally constant sheaves of sets is induced by a morphism of sheaves. -/
lemma exists_stalkMap_eq {F F' : Y.FiniteLocallyConstant} (t : stalk s F → stalk s F')
    (ht : ∀ g x, t (smul s G g x) = smul s G g (t x)) :
    ∃ f : F ⟶ F', ∀ x, stalkMap s f x = t x := by
  let t' : (FiniteEtale.fiber s).obj (rep Y F) → (FiniteEtale.fiber s).obj (rep Y F') :=
    fun y ↦ (repStalkEquiv s F' (t ((repStalkEquiv s F).symm (ULift.up y)))).down
  have ht' (g : G) (y) : t' (g • y) = g • t' y := by
    have := ht g ((repStalkEquiv s F).symm (ULift.up y))
    simp only [t']
    unfold smul at this
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.apply_symm_apply]
  let E := equivalenceContAction s G
  let a : E.functor.obj (rep Y F) ⟶ E.functor.obj (rep Y F') :=
    ObjectProperty.homMk ⟨FintypeCat.homMk t', fun g ↦ by
      ext y
      change t' (g • y) = g • t' y
      exact ht' g y⟩
  let φ := E.functor.preimage a
  have hφ (y) : (FiniteEtale.fiber s).map φ y = t' y := by
    change (E.functor.map φ).hom.hom y = _
    rw [E.functor.map_preimage a]
    rfl
  refine ⟨(repIso F).hom ≫ (sectionsFunctor Y).map φ ≫ (repIso F').inv, fun x ↦ ?_⟩
  apply (repStalkEquiv s F').injective
  rw [isoStalkEquiv_stalkMap s (repIso F) (repIso F') _ φ
    (by rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]), hφ]
  change repStalkEquiv s F' (t ((repStalkEquiv s F).symm (repStalkEquiv s F x))) = _
  rw [Equiv.symm_apply_apply]

end Fundamental

end Action

end FiniteLocallyConstant

end AlgebraicGeometry.Scheme
