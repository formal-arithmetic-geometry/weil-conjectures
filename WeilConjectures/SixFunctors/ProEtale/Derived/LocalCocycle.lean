/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.SixFunctors.ProEtale.LocalSections
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSections

/-!
# Local cocycles of complexes of pro-étale sheaves of modules

Let `X` be a scheme and `Λ` a commutative ring. This file records how cocycles of complexes of
pro-étale sheaves of `Λ`-modules behave locally on the small pro-étale site, and how global
sections are maps out of the unit sheaf.

## Main results

- `AlgebraicGeometry.ProEtale.exists_sieve_eq_d_of_exactAt`: a cocycle of a complex which is
  exact in its degree is locally a coboundary.
- `AlgebraicGeometry.ProEtale.exists_sieve_lift_cocycle`: along a quasi-isomorphism
  `φ : A ⟶ B`, a cocycle of `B` is locally cohomologous to the image of a cocycle of `A`. This
  applies the previous result to the acyclic mapping cone of `φ`.
- `AlgebraicGeometry.ProEtale.unitHomEquiv`: morphisms `𝟙_ ⟶ F` out of the unit sheaf correspond
  to the sections of `F` over the terminal object `X` of the pro-étale site, by evaluation at
  `1`.
- `AlgebraicGeometry.ProEtale.singleUnitHomEquiv`: chain maps from the unit placed in degree `0`
  to a complex `M` correspond to the cocycles of `M` in degree `0` over the terminal object.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite MonoidalCategory

namespace CategoryTheory

namespace Presheaf

variable {C : Type*} [Category* C] {T : C} (hT : IsTerminal T) {R : Type v} [CommRing R]

/-- On a category with a terminal object `T`, the morphism out of the unit presheaf of
`R`-modules sending `1` to the restrictions of a section `x` over `T`. -/
noncomputable def unitHomOfTerminal {P : Cᵒᵖ ⥤ ModuleCat.{v} R} (x : P.obj (op T)) :
    𝟙_ (Cᵒᵖ ⥤ ModuleCat.{v} R) ⟶ P where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (P.map (hT.from U.unop).op x))
  naturality U V g := by
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    have hg : (hT.from U.unop).op ≫ g = (hT.from V.unop).op :=
      Quiver.Hom.unop_inj (hT.hom_ext _ _)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul]
    rw [← ModuleCat.comp_apply, ← P.map_comp, hg]
    exact one_smul R _

/-- The morphism `unitHomOfTerminal hT x` sends `1` over `T` to `x`. -/
lemma unitHomOfTerminal_app_one {P : Cᵒᵖ ⥤ ModuleCat.{v} R} (x : P.obj (op T)) :
    (unitHomOfTerminal hT x).app (op T) (1 : R) = x := by
  simp only [Monoidal.tensorUnit_obj, unitHomOfTerminal, op_unop, IsTerminal.from_self, op_id,
    Functor.map_id, ModuleCat.hom_id, LinearMap.id_coe, id_eq, ConcreteCategory.hom_ofHom]
  exact one_smul R x

/-- A morphism out of the unit presheaf of `R`-modules on a category with a terminal object
`T` is determined by the image of `1` over `T`. -/
lemma unit_hom_ext_of_isTerminal (hT : IsTerminal T) {P : Cᵒᵖ ⥤ ModuleCat.{v} R}
    {φ ψ : 𝟙_ (Cᵒᵖ ⥤ ModuleCat.{v} R) ⟶ P} (h : φ.app (op T) (1 : R) = ψ.app (op T) (1 : R)) :
    φ = ψ := by
  have key (χ : 𝟙_ (Cᵒᵖ ⥤ ModuleCat.{v} R) ⟶ P) :
      χ = unitHomOfTerminal hT (χ.app (op T) (1 : R)) := by
    ext U : 2
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    simp only [unitHomOfTerminal, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
    rw [← NatTrans.naturality_apply]
    rfl
  rw [key φ, key ψ, h]

end Presheaf

namespace Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Type v} [Ring R]
  {F G H : Sheaf J (ModuleCat.{w} R)} {U : Cᵒᵖ}

/-- Sections along a composite of morphisms of sheaves of modules. -/
lemma comp_hom_app_apply (f : F ⟶ G) (g : G ⟶ H) (x : F.obj.obj U) :
    (f ≫ g).hom.app U x = g.hom.app U (f.hom.app U x) :=
  rfl

/-- Sections along the identity of a sheaf of modules. -/
lemma id_hom_app_apply (x : F.obj.obj U) : (InducedCategory.Hom.hom (𝟙 F)).app U x = x :=
  rfl

/-- Sections along a sum of morphisms of sheaves of modules. -/
lemma add_hom_app_apply (f g : F ⟶ G) (x : F.obj.obj U) :
    (f + g).hom.app U x = f.hom.app U x + g.hom.app U x :=
  rfl

/-- Sections along the negative of a morphism of sheaves of modules. -/
lemma neg_hom_app_apply (f : F ⟶ G) (x : F.obj.obj U) :
    (-f).hom.app U x = -f.hom.app U x :=
  rfl

/-- Sections along the zero morphism of sheaves of modules. -/
lemma zero_hom_app_apply (x : F.obj.obj U) : (0 : F ⟶ G).hom.app U x = 0 :=
  rfl

/-- Equal morphisms of sheaves of modules agree on sections. -/
lemma congr_hom_app_apply {f g : F ⟶ G} (h : f = g) (x : F.obj.obj U) :
    f.hom.app U x = g.hom.app U x := by
  rw [h]

end Sheaf

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme Sheaf

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Exactness of a short complex of pro-étale sheaves of modules is local: a section `z` of the
middle term with `g z = 0` is locally of the form `f w`. -/
lemma exists_sieve_eq_of_exact
    {S : ShortComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))} (hS : S.Exact)
    {U : X.ProEt} (z : S.X₂.obj.obj (op U)) (hz : S.g.hom.app (op U) z = 0) :
    ∃ R ∈ Scheme.ProEt.topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), R f →
      ∃ w : S.X₁.obj.obj (op V), S.f.hom.app (op V) w = S.X₂.obj.map f.op z := by
  let p := kernel.lift S.g S.f S.zero
  have : Epi p := hS.epi_kernelLift
  have := (Sheaf.isLocallySurjective_iff_epi' _ p).2 this
  have : PreservesLimits ((sheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)).obj (op U)) :=
    inferInstanceAs (PreservesLimits
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op U)))
  obtain ⟨k, hk⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((ShortComplex.exact_kernel S.g).map_of_mono_of_preservesKernel
      ((sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj (op U))
      inferInstance inferInstance) z hz
  refine ⟨_, Presheaf.imageSieve_mem _ p.hom k, fun V f ⟨w, hw⟩ ↦ ⟨w, ?_⟩⟩
  rw [← kernel.lift_ι S.g S.f S.zero, comp_hom_app_apply, hw, NatTrans.naturality_apply, ← hk]
  rfl

/-- **Local exactness of a complex.** If a cochain complex `K` of pro-étale sheaves of modules
is exact in degree `n`, then a cocycle `z` of `K` in degree `n` over `U` is, after restriction to
the members of a covering sieve, a coboundary. -/
lemma exists_sieve_eq_d_of_exactAt
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ}
    {m n : ℤ} (hmn : m + 1 = n) (hK : K.ExactAt n) {U : X.ProEt} (z : (K.X n).obj.obj (op U))
    (hz : (K.d n (n + 1)).hom.app (op U) z = 0) :
    ∃ R ∈ Scheme.ProEt.topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), R f →
      ∃ w : (K.X m).obj.obj (op V), (K.d m n).hom.app (op V) w = (K.X n).obj.map f.op z :=
  exists_sieve_eq_of_exact ((K.exactAt_iff' m n (n + 1) (by simp; lia) (by simp)).1 hK) z hz

/-- **Local lifting of cocycles along a quasi-isomorphism.** Let `φ : A ⟶ B` be a
quasi-isomorphism of cochain complexes of pro-étale sheaves of modules and `z` a cocycle of `B`
in degree `n` over `U`. After restriction to the members of a covering sieve, `z` is
cohomologous to the image of a cocycle of `A`.

The image `(0, z)` of `z` in the mapping cone of `φ` is a cocycle, hence locally the coboundary
of some `(z', -w)`; its components give the required cocycle `z'` and the correction `w`. -/
lemma exists_sieve_lift_cocycle
    {A B : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ}
    (φ : A ⟶ B) [QuasiIso φ] {m n : ℤ} (hmn : m + 1 = n) {U : X.ProEt}
    (z : (B.X n).obj.obj (op U)) (hz : (B.d n (n + 1)).hom.app (op U) z = 0) :
    ∃ R ∈ Scheme.ProEt.topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), R f →
      ∃ (z' : (A.X n).obj.obj (op V)) (w : (B.X m).obj.obj (op V)),
        (A.d n (n + 1)).hom.app (op V) z' = 0 ∧
          (φ.f n).hom.app (op V) z' = (B.X n).obj.map f.op z + (B.d m n).hom.app (op V) w := by
  open CochainComplex.mappingCone in
  have hC := (quasiIso_iff_acyclic φ).1 inferInstance
  have hy : ((CochainComplex.mappingCone φ).d n (n + 1)).hom.app (op U)
      (((inr φ).f n).hom.app (op U) z) = 0 := by
    rw [← comp_hom_app_apply, inr_f_d, comp_hom_app_apply, hz, map_zero]
  obtain ⟨R, hR, h⟩ := exists_sieve_eq_d_of_exactAt hmn (hC n) _ hy
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨c, hc⟩ := h f hf
  refine ⟨((fst φ).1.v m n hmn).hom.app (op V) c,
    -((snd φ).v m m (add_zero m)).hom.app (op V) c, ?_, ?_⟩
  · have := congr_hom_app_apply (d_fst_v φ m n (n + 1) hmn rfl) c
    rw [comp_hom_app_apply, hc, NatTrans.naturality_apply, ← comp_hom_app_apply, inr_f_fst_v,
      zero_hom_app_apply, map_zero, neg_hom_app_apply, comp_hom_app_apply] at this
    exact neg_eq_zero.1 this.symm
  · have := congr_hom_app_apply (d_snd_v φ m n hmn) c
    rw [comp_hom_app_apply, hc, NatTrans.naturality_apply, ← comp_hom_app_apply, inr_f_snd_v,
      id_hom_app_apply, add_hom_app_apply, comp_hom_app_apply, comp_hom_app_apply] at this
    rw [this, map_neg]
    abel

variable (X) in
/-- The terminal object `X` of the small pro-étale site of `X`. -/
noncomputable abbrev terminalProEt : X.ProEt :=
  Scheme.ProEt.mk (𝟙 X)

/-- The section `f(1)` over the terminal object of a morphism `f : 𝟙_ ⟶ F` out of the unit
sheaf. -/
noncomputable def sectionOfUnitHom {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (f : 𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶ F) :
    F.obj.obj (op (terminalProEt X)) :=
  (unitSection ≫ f.hom).app (op (terminalProEt X)) (1 : Λ)

/-- A morphism out of the unit sheaf is determined by its section `f(1)` over the terminal
object. -/
lemma sectionOfUnitHom_injective
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} :
    Function.Injective (sectionOfUnitHom (F := F)) := by
  intro f g h
  have h' := Presheaf.unit_hom_ext_of_isTerminal (Scheme.ProEt.isTerminalMkId X) h
  rw [unitSection, Category.assoc, Category.assoc] at h'
  have e := sheafify_hom_ext _ _ _ F.property h'
  exact (cancel_epi _).1 (Sheaf.hom_ext e)

/-- The morphism out of the unit sheaf sending `1` to the restrictions of a section `x` of `F`
over the terminal object. -/
noncomputable def unitHomOfSection {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (x : F.obj.obj (op (terminalProEt X))) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶ F :=
  (Functor.Monoidal.εIso (presheafToSheaf (Scheme.ProEt.topology X) _)).hom ≫
    ((sheafificationAdjunction _ _).homEquiv _ _).symm
      (Presheaf.unitHomOfTerminal (Scheme.ProEt.isTerminalMkId X) x)

/-- On constant sections, `unitHomOfSection x` is `unitHomOfTerminal x`. -/
lemma unitSection_comp_unitHomOfSection
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (x : F.obj.obj (op (terminalProEt X))) :
    unitSection ≫ (unitHomOfSection x).hom =
      Presheaf.unitHomOfTerminal (Scheme.ProEt.isTerminalMkId X) x := by
  let E := Functor.Monoidal.εIso (presheafToSheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} Λ))
  let L := ((sheafificationAdjunction _ _).homEquiv _ F).symm
    (Presheaf.unitHomOfTerminal (Scheme.ProEt.isTerminalMkId X) x)
  have e : (sheafToPresheaf _ _).map E.inv ≫ (E.hom ≫ L).hom = L.hom :=
    congrArg (·.hom) (E.inv_hom_id_assoc L)
  rw [unitSection, Category.assoc, unitHomOfSection, e]
  exact toSheafify_sheafifyLift _ _ F.property

/-- The morphism `unitHomOfSection x` sends `1` to `x`. -/
lemma sectionOfUnitHom_unitHomOfSection
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (x : F.obj.obj (op (terminalProEt X))) :
    sectionOfUnitHom (unitHomOfSection x) = x := by
  rw [sectionOfUnitHom, unitSection_comp_unitHomOfSection, Presheaf.unitHomOfTerminal_app_one]

/-- **Sections versus maps from the unit.** Morphisms `𝟙_ ⟶ F` out of the unit sheaf
correspond to the sections of `F` over the terminal object `X` of the pro-étale site, by
`f ↦ f(1)`. -/
noncomputable def unitHomEquiv (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶ F) ≃+
      F.obj.obj (op (terminalProEt X)) where
  toFun := sectionOfUnitHom
  invFun := unitHomOfSection
  left_inv _ := sectionOfUnitHom_injective (sectionOfUnitHom_unitHomOfSection _)
  right_inv := sectionOfUnitHom_unitHomOfSection
  map_add' _ _ := rfl

/-- `unitHomEquiv F f` is the image of the constant section `1` under `f`. -/
lemma unitHomEquiv_apply {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (f : 𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶ F) :
    unitHomEquiv F f = (unitSection ≫ f.hom).app (op (terminalProEt X)) (1 : Λ) :=
  rfl

/-- The identification `unitHomEquiv` is natural in `F`. -/
lemma unitHomEquiv_comp {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (f : 𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶ F) (g : F ⟶ G) :
    unitHomEquiv G (f ≫ g) = g.hom.app _ (unitHomEquiv F f) :=
  rfl

/-- **Chain maps from the unit.** Chain maps from the unit sheaf placed in degree `0` to a
cochain complex `M` correspond to the cocycles of `M` in degree `0` over the terminal object of
the pro-étale site. -/
noncomputable def singleUnitHomEquiv
    (M : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :
    ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) ⟶ M) ≃
      {x : (M.X 0).obj.obj (op (terminalProEt X)) //
        (M.d 0 1).hom.app (op (terminalProEt X)) x = 0} where
  toFun g := ⟨unitHomEquiv _ ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ g.f 0), by
    rw [← unitHomEquiv_comp, Category.assoc, g.comm]
    simp⟩
  invFun x := HomologicalComplex.mkHomFromSingle ((unitHomEquiv _).symm x.1) (fun k hk ↦ by
    obtain rfl : k = 1 := by simpa using hk.symm
    apply (unitHomEquiv _).injective
    rw [unitHomEquiv_comp, AddEquiv.apply_symm_apply, x.2, map_zero])
  left_inv g := HomologicalComplex.from_single_hom_ext (by
    rw [HomologicalComplex.mkHomFromSingle_f, AddEquiv.symm_apply_apply, Iso.hom_inv_id_assoc])
  right_inv x := Subtype.ext (by
    simp only [HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc,
      AddEquiv.apply_symm_apply])

end AlgebraicGeometry.ProEtale
