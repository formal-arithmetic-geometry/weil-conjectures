/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisSections
import all Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnitOfSections
import Sheaf.CategoryTheory.CoefficientPushCopowerCriterion
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Mathlib.Topology.Algebra.Module.FiniteDimension
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-!

# Compatibility of the six functors with the extension of `ℓ`-adic coefficients

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ_ℓ` inside `ℚ̄_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) and `Ω = ℚ̄_ℓ`. The inclusions of condensed rings
`E̲ ⟶ F̲` (`Profinite.padicSubfieldRingObjMap`) and `E̲ ⟶ ℚ̲̄_ℓ`
(`Profinite.padicSubfieldRingObjToPadicAlgCl`) of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension` pull back, on a
scheme `X`, to coefficient changes `ι : E_X ⟶ F_X` and `ι : E_X ⟶ ℚ̄_ℓ,X`
(`ProEtale.coefficientMap`), inducing the derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - .
```
The comparisons (Pull), (Push) and (Shriek) between these and the derived functors `Lf^*`,
`Rf_*`, `Rf_!` on module objects are the ones of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, for these two
coefficient changes. This file supplies the coefficient-specific input:

* `ℚ̄_ℓ,X = colim_E E_X` (`ProEtale.isColimitPadicAlgClRingObjCocone`), the pullback along the
  left adjoint `p_X^*` of `ℚ̲̄_ℓ = colim_E E̲` (`Profinite.isColimitPadicAlgClRingObjCocone`);
* both coefficient changes are flat, so that (Pull) and (Push) are defined on the unbounded
  derived categories, and (Pull) is an isomorphism there;
* for a finite extension `F/E`, (Push) is an isomorphism on all unbounded objects, hence so is
  (Shriek);
* for `E ⊆ Ω`, (Push) is an isomorphism on all unbounded objects when `f` is proper, but not
  for an arbitrary `f`. Since the proper part of a compactification is proper, (Shriek) is an
  isomorphism on all unbounded objects for every `f` with a compactification.

## Sorried input

* **(A0.2)** `ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`:
  for finite subextensions `E ≤ F`, the extension of scalars `F_X ⊗_{E_X} -` is exact, i.e.
  `F_X` is flat over `E_X`. Indeed `F_X` is finite free over `E_X`: an `E`-basis `b₁, …, bₙ` of
  `F` gives `C(-, F) ≅ C(-, E)^n`, `h ↦ (hᵢ)` with `h = ∑ hᵢ bᵢ`, on the point, and `p_X^*`
  preserves finite direct sums.
* **(A0.2)**
  `ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`:
  for a finite subextension `E`, the extension of scalars `ℚ̄_ℓ,X ⊗_{E_X} -` is exact, i.e.
  `ℚ̄_ℓ,X` is flat over `E_X`: it is the filtered colimit of the `F_X`, `F ≥ E`
  (`ProEtale.isColimitPadicAlgClRingObjCocone`), each of which is finite free over `E_X`.
* `ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap`: for a finite extension
  `F/E`, (Push) is an isomorphism on all unbounded objects, since `F_X ≅ E_X^n` reduces it to
  the compatibility of `Rf_*` with finite direct sums.
* `ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`:
  for `E ⊆ Ω` and `f` proper, (Push) is an isomorphism on all unbounded objects: `Rf_*` has a
  right adjoint `Rf^!`, hence commutes with the coproducts through which `ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` is
  computed from the finite stages. For a general `f` this fails, and (Push) is an isomorphism
  only at objects at which `Rf_*` commutes with the relevant coproducts; no such statement is
  made here.

-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

section FiniteBasisConstruction

universe v₁ v₂ u₁ u₂
open CategoryTheory.MonObj CategoryTheory.BraidedCategory
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false

/- The following finite free comparisons use only additive monoidal functors, so they apply
both to sheafification and to inverse image from the point. -/
namespace CategoryTheory.Mod

section Map
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  [Abelian D] [MonoidalPreadditive D]
  (F : C ⥤ D) [F.LaxMonoidal] [F.Additive]
  {R S : C} [MonObj R] [MonObj S]
  (a : R ⟶ S) [IsMonHom a]
private theorem additive_mapMod : (F.mapMod R).Additive where
  map_add := hom_ext _ _ F.map_add

private noncomputable def mapRegularIso :
    (F.mapMod R).obj (regular R) ≅ regular (F.obj R) :=
  isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])
private noncomputable def mapFiniteFreeIso (n : ℕ) :
    (F.mapMod R).obj (finiteFree R n) ≅ finiteFree (F.obj R) n := by
  have : (F.mapMod R).Additive := additive_mapMod F
  exact (F.mapMod R).mapBiproduct (fun _ : Fin n ↦ regular R) ≪≫
    biproduct.mapIso (fun _ ↦ mapRegularIso F)
private noncomputable def mapRestrictedRegularIso :
    (F.mapMod R).obj ((comap a).obj (regular S)) ≅
      (comap (F.map a)).obj (regular (F.obj S)) :=
  (F.mapModComapIso a).app (regular S) ≪≫
    (comap (F.map a)).mapIso (mapRegularIso F)
private noncomputable def mapFreeRestrictedRegularIso (n : ℕ)
    (e : (comap a).obj (regular S) ≅ finiteFree R n) :
    (comap (F.map a)).obj (regular (F.obj S)) ≅ finiteFree (F.obj R) n :=
  (mapRestrictedRegularIso F a).symm ≪≫ (F.mapMod R).mapIso e ≪≫ mapFiniteFreeIso F n
end Map
section RingIso
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  {R S : C} [MonObj R] [MonObj S]
private noncomputable def regularRingIso (r : R ≅ S) [IsMonHom r.hom] :
    (comap r.inv).obj (regular R) ≅ regular S :=
  isoMk r (by
    change (r.inv ▷ R ≫ μ[R]) ≫ r.hom = S ◁ r.hom ≫ μ[S]
    rw [Category.assoc, IsMonHom.mul_hom]
    rw [MonoidalCategory.tensorHom_def]
    rw [Category.assoc, ← comp_whiskerRight_assoc, r.inv_hom_id,
      id_whiskerRight, Category.id_comp])
private noncomputable def comapFreeIso (e : R ≅ S) [IsMonHom e.hom] (n : ℕ) :
    (comap e.inv).obj (finiteFree R n) ≅ finiteFree S n := by
  let : PreservesBiproduct (fun _ : Fin n ↦ regular R) (comap e.inv) :=
    preservesBiproduct_of_preservesProduct _
  let er := regularRingIso e
  exact (comap e.inv).mapBiproduct (fun _ : Fin n ↦ regular R) ≪≫
    biproduct.mapIso (fun _ ↦ er)

variable {R' S' : C} [MonObj R'] [MonObj S']
private noncomputable def restrictedRegularIsoOfRingIso
    (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
    (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
    (h : a' ≫ s.inv = r.inv ≫ a) :
    (comap a').obj (regular S') ≅
      (comap r.inv).obj ((comap a).obj (regular S)) := by
  let es := regularRingIso s
  exact (comap a').mapIso es.symm ≪≫
    ((comapComp a' s.inv).symm ≪≫ comapCongr h ≪≫ comapComp r.inv a).app _
private noncomputable def freeRestrictedRegularIsoOfRingIso
    (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
    (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
    (h : a' ≫ s.inv = r.inv ≫ a)
    (n : ℕ) (e : (comap a).obj (regular S) ≅ finiteFree R n) :
    (comap a').obj (regular S') ≅ finiteFree R' n :=
  restrictedRegularIsoOfRingIso a a' r s h ≪≫
    (comap r.inv).mapIso e ≪≫ comapFreeIso r n
end RingIso
end CategoryTheory.Mod

/- Work sectionwise before sheafification: a continuous field-linear map gives an internal
module morphism, and the coordinate maps of a finite basis give inverse biproduct maps. -/
namespace Profinite

private noncomputable def continuousAddHomPresheaf
    {S T : Type} [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Ring T] [TopologicalSpace T] [IsTopologicalRing T]
    (l : S →+ T) (hl : Continuous l) :
    continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} ⟶
      continuousMapRingPresheaf T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} where
  app U := AddCommGrpCat.ofHom
    { toFun f := ULift.up ⟨fun x ↦ l (f.down x), hl.comp f.down.continuous⟩
      map_zero' := by
        change ULift.up _ = ULift.up _
        congr 1
        ext x
        exact map_zero l
      map_add' f g := by
        change ULift.up _ = ULift.up _
        congr 1
        ext x
        exact map_add l _ _ }
  naturality _ _ _ := rfl

private noncomputable def continuousLinearPresheafHom
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (l : S →ₗ[R] R) (hl : Continuous l) :
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ⟶
    Mod.regular (continuousMapRingPresheaf R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  Mod.homMk (continuousAddHomPresheaf l.toAddMonoidHom hl) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up (⟨fun x ↦ l ((algebraMap R S (r.down x)) * s.down x), _⟩ :
      C(U.unop, R)) = ULift.up _
    congr 1
    ext x
    change l ((algebraMap R S (r.down x)) * s.down x) = r.down x * l (s.down x)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      l.map_smul (r.down x) (s.down x))

private noncomputable def continuousLinearPresheafHomFrom
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (l : R →ₗ[R] S) (hl : Continuous l) :
    Mod.regular (continuousMapRingPresheaf.{u} R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ⟶
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) :=
  Mod.homMk (continuousAddHomPresheaf l.toAddMonoidHom hl) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up _ = ULift.up _
    congr 1
    ext x
    change l (r.down x * s.down x) = algebraMap R S (r.down x) * l (s.down x)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      l.map_smul (r.down x) (s.down x))

private noncomputable def continuousBasisIso
    {R S : Type} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (n : ℕ) (b : Module.Basis (Fin n) R S)
    (hc : ∀ i, Continuous (b.coord i)) :
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ≅
    Mod.finiteFree (continuousMapRingPresheaf R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) n := by
  let p (i : Fin n) := continuousLinearPresheafHom ha (b.coord i) (hc i)
  let q (i : Fin n) := continuousLinearPresheafHomFrom ha
    (LinearMap.toSpanSingleton R S (b i))
    (by
      change Continuous (fun r : R ↦ r • b i)
      simp_rw [Algebra.smul_def]
      exact ha.mul_const (b i))
  refine
    { hom := biproduct.lift p
      inv := biproduct.desc q
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [biproduct.lift_desc]
    apply Mod.hom_ext
    change (Mod.forget _).map (∑ i, p i ≫ q i) = _
    rw [Functor.map_sum]
    apply NatTrans.ext
    funext U
    simp only [NatTrans.app_sum]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    let ev : (AddCommGrpCat.of (ULift.{u + 1} C(U.unop, S)) ⟶
        AddCommGrpCat.of (ULift.{u + 1} C(U.unop, S))) →+ S :=
      { toFun g := (g.hom f).down x
        map_zero' := rfl
        map_add' _ _ := rfl }
    change ev (∑ i, _) = f.down x
    rw [map_sum]
    change (∑ i, (b.coord i (f.down x)) • b i) = f.down x
    exact b.sum_repr (f.down x)
  · apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      Category.id_comp]
    apply Mod.hom_ext
    by_cases hij : j = i
    · subst j
      rw [biproduct.ι_π_self]
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change ULift.up _ = f
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      change b.coord i ((f.down x) • b i) = f.down x
      simp
    · rw [biproduct.ι_π_ne _ hij]
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change ULift.up _ = (0 : ULift.{u + 1} C(U.unop, R))
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      change b.coord i ((f.down x) • b j) = 0
      simp [hij]

private noncomputable def continuousBasisSheafIso
    {R S : Type} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (n : ℕ) (b : Module.Basis (Fin n) R S)
    (hc : ∀ i, Continuous (b.coord i)) :
    (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (continuousMapRingSheafMap (algebraMap R S) ha))).obj
      (Mod.regular (continuousMapRingObj S)) ≅ Mod.finiteFree (continuousMapRingObj R) n := by
  let a := Functor.whiskerRight (continuousMapRingPresheafMap
    (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let sh := presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  exact Mod.freeRestrictedRegularIsoOfRingIso (sh.map a) _
    (Sheaf.sheafifyRingPresheafIso _ (continuousMapRingSheaf R))
    (Sheaf.sheafifyRingPresheafIso _ (continuousMapRingSheaf S))
    (by rw [Sheaf.sheafCompose_map_eq]; simp [sh, a, continuousMapRingSheafMap_hom]) n
    (Mod.mapFreeRestrictedRegularIso sh a n (continuousBasisIso ha n b hc))

end Profinite

end FiniteBasisConstruction


namespace CategoryTheory.Mod

private theorem restrictionReflectsIsomorphisms
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] :
    (comap (D := C) φ).ReflectsIsomorphisms := by
  refine ⟨?_⟩
  intro M N f hf
  have : IsIso f.hom := by
    change IsIso ((forget R).map ((comap φ).map f))
    infer_instance
  have : IsIso ((forget S).map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f (forget S)

end CategoryTheory.Mod

namespace CategoryTheory.Adjunction

private theorem isIso_mate_pushHomOfComapIso
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} (κ : G' ⋙ U' ≅ U ⋙ G) :
    IsIso (mateEquiv adj adj' (pushHomOfComapIso adj adj' κ)) := by
  change IsIso ((mateEquiv adj adj') ((mateEquiv adj adj').symm
    (TwoSquare.mk _ _ _ _ κ.inv)))
  rw [Equiv.apply_symm_apply]
  infer_instance

end CategoryTheory.Adjunction


namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-! ### The coefficient rings `E_X`, `ℚ̄_ℓ,X` and their inclusions -/

section RingObj

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coefficient ring object `E_X = p_X^* E̲` on `X_proét`, for a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev padicSubfieldRingObj (E : FiniteIntermediateField ℓ) :
    Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj E) X

/-- The coefficient ring object `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ` on `X_proét`. -/
noncomputable abbrev padicAlgClRingObj : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.padicAlgClRingObj ℓ) X

/-- The inclusion `E_X ⟶ F_X` for finite subextensions `E ≤ F`, the coefficient change induced by
the inclusion `E̲ ⟶ F̲` of condensed rings. -/
noncomputable abbrev padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObj X ℓ E ⟶ padicSubfieldRingObj X ℓ F :=
  coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) X

/-- The inclusion `E_X ⟶ ℚ̄_ℓ,X` for a finite subextension `E`, the coefficient change induced by
the inclusion `E̲ ⟶ ℚ̲̄_ℓ` of condensed rings. -/
noncomputable abbrev padicSubfieldRingObjToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObj X ℓ E ⟶ padicAlgClRingObj X ℓ :=
  coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X

/-- The inclusion `E_X ⟶ F_X` followed by the inclusion `F_X ⟶ ℚ̄_ℓ,X` is the inclusion
`E_X ⟶ ℚ̄_ℓ,X`. -/
@[reassoc]
lemma padicSubfieldRingObjMap_comp_toPadicAlgCl {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjToPadicAlgCl X ℓ F =
      padicSubfieldRingObjToPadicAlgCl X ℓ E := by
  rw [← coefficientMap_comp, Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl]

/-- The inverse image `p_X^*` from condensed abelian groups is a left adjoint, being the
composite `π_X^* ∘ p^*` of two left adjoints. -/
instance isLeftAdjoint_upperStarFromPoint : (upperStarFromPoint X).IsLeftAdjoint :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint

/-- The cocone over the diagram `E ↦ E_X` with vertex `ℚ̄_ℓ,X`, given by the inclusions
`E_X ⟶ ℚ̄_ℓ,X`: the image under `p_X^*` of `Profinite.padicAlgClRingObjCocone`. -/
noncomputable abbrev padicAlgClRingObjCocone :
    Cocone (Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X) :=
  (upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone ℓ)

/-- **`ℚ̄_ℓ,X = colim_E E_X`**: the inclusions `E_X ⟶ ℚ̄_ℓ,X` exhibit `ℚ̄_ℓ,X` as the filtered
colimit of the `E_X` in abelian pro-étale sheaves on `X`. This is the image of
`ℚ̲̄_ℓ = colim_E E̲` (`Profinite.isColimitPadicAlgClRingObjCocone`) under the left adjoint
`p_X^*`. -/
noncomputable def isColimitPadicAlgClRingObjCocone : IsColimit (padicAlgClRingObjCocone X ℓ) :=
  isColimitOfPreserves (upperStarFromPoint X) (Profinite.isColimitPadicAlgClRingObjCocone ℓ)

end RingObj

namespace CondensedRing

open Scheme PadicAlgCl

attribute [local irreducible] derivedPushHom derivedComapLowerStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction Adjunction.mapDerivedCategoryAdjunction
  Mod.extendRestrictAdjunction upperStarFromPoint ProEtale.upperStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### Flatness of the coefficient inclusions -/

section Flat

open MonObj

private theorem point_finiteFree (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Nonempty ((Mod.comap (Profinite.padicSubfieldRingObjMap.{u} ℓ h)).obj
      (Mod.regular (Profinite.continuousMapRingObj.{u} F)) ≅
      Mod.finiteFree (Profinite.continuousMapRingObj.{u} E)
        (@Module.finrank E F inferInstance inferInstance
          (Module.compHom F (IntermediateField.inclusion h).toRingHom))) := by
  let := Sheaf.symmetricCategory (coherentTopology Profinite.{u}) Ab.{u + 1}
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E F
  let b := Module.finBasis E F
  have hb (i : Fin (Module.finrank E F)) : Continuous (b.coord i) :=
    ((b.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
  have ha : Continuous (algebraMap E F) := continuous_subtype_val.subtype_mk _
  exact ⟨Profinite.continuousBasisSheafIso ha _ b hb⟩


private theorem point_finiteCopower (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    ∃ (I : Type (u + 1)) (_ : Finite I), Nonempty
      ((∐ fun _ : I ↦ Mod.regular (Profinite.continuousMapRingObj.{u} E)) ≅
        (Mod.comap (Profinite.padicSubfieldRingObjMap ℓ h)).obj
          (Mod.regular (Profinite.continuousMapRingObj.{u} F))) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) := IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  obtain ⟨e⟩ := point_finiteFree.{u} ℓ h
  let n := @Module.finrank E F inferInstance inferInstance
    (Module.compHom F (IntermediateField.inclusion h).toRingHom)
  let I := ULift.{u + 1} (Fin n)
  let e' : (∐ fun _ : I ↦ Mod.regular (Profinite.continuousMapRingObj.{u} E)) ≅
      (Mod.comap (Profinite.padicSubfieldRingObjMap ℓ h)).obj
        (Mod.regular (Profinite.continuousMapRingObj.{u} F)) :=
    Sigma.reindex Equiv.ulift
      (fun _ : Fin n ↦ Mod.regular (Profinite.continuousMapRingObj.{u} E)) ≪≫
        (biproduct.isoCoproduct _).symm ≪≫ e.symm
  exact ⟨I, inferInstance, ⟨e'⟩⟩

variable (X : Scheme.{u})

/-- **(A0.2)** For finite subextensions `E ≤ F`, the extension of scalars along `E_X ⟶ F_X` is
exact: `F_X` is finite free, in particular flat, over `E_X`. See the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) := IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  obtain ⟨e⟩ := point_finiteFree.{u} ℓ h
  let n := @Module.finrank E F inferInstance inferInstance
    (Module.compHom F (IntermediateField.inclusion h).toRingHom)
  let e' : (∐ fun _ : ULift.{u + 1} (Fin n) ↦
      Mod.regular (Profinite.continuousMapRingObj.{u} E)) ≅
      (Mod.comap (Profinite.padicSubfieldRingObjMap ℓ h)).obj
        (Mod.regular (Profinite.continuousMapRingObj.{u} F)) :=
    Sigma.reindex Equiv.ulift
      (fun _ : Fin n ↦ Mod.regular (Profinite.continuousMapRingObj.{u} E)) ≪≫
        (biproduct.isoCoproduct _).symm ≪≫ e.symm
  obtain ⟨b, hb, hflat, hunit⟩ := scheme_basis_from_point _ _
    (Profinite.padicSubfieldRingObjMap ℓ h) (ULift.{u + 1} (Fin n)) e'
  exact hflat X

/-- **(A0.2)** For a finite subextension `E`, the extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` is
exact: `ℚ̄_ℓ,X` is flat over `E_X`, being a filtered colimit of finite free `E_X`-modules. See
the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
    (E : FiniteIntermediateField ℓ) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) := by
  obtain ⟨I, b, hb, hflat, hcopower⟩ := exists_condensedQbar_scalar_basis_sections.{u} ℓ E
  exact hflat X

end Flat

attribute [local irreducible] Mod.extendScalars
  Functor.leftDerivedFunctorIsoMapDerivedCategory Functor.CommShift.ofIso

private theorem reflectsDerivedIsomorphisms
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

private theorem centralUnitCopower
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} [U'.ReflectsIsomorphisms]
    (β : G ⋙ L' ⟶ L ⋙ G') (hκ : IsIso (mateEquiv adj adj' β))
    (M : A) (I : Type*) [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦ G.obj M)]
    (τ : I → CatCenter B) (τ' : I → CatCenter B')
    (hs : ∀ i K, G'.map ((τ i).app K) = (τ' i).app (G'.obj K))
    (hC : IsIso (Sigma.desc fun i ↦
      (show M ⟶ U.obj (L.obj M) from adj.unit.app M) ≫ U.map ((τ i).app (L.obj M))))
    (hD : IsIso (Sigma.desc fun i ↦
      (show G.obj M ⟶ U'.obj (L'.obj (G.obj M)) from adj'.unit.app (G.obj M)) ≫
        U'.map ((τ' i).app (L'.obj (G.obj M)))))
    (hc : IsIso (Sigma.desc fun i : I ↦ G.map (Sigma.ι (fun _ : I ↦ M) i))) :
    IsIso (β.app M) := by
  have := hC
  have := hD
  apply (Adjunction.isIso_iff_unitCoproductComparison adj adj' β hκ M I
    (fun i ↦ (τ i).app _) (fun i ↦ (τ' i).app _) (fun i ↦ ?_)).2 hc
  exact ((τ' i).naturality (β.app M)).symm.trans
    (congrArg (fun g ↦ β.app M ≫ g) (hs i (L.obj M))).symm

private theorem centralUnitCopowerExplicit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} [U'.ReflectsIsomorphisms]
    (β : G ⋙ L' ⟶ L ⋙ G') (hκ : IsIso (mateEquiv adj adj' β))
    (M : A) (I : Type*) [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦ G.obj M)]
    (τ : I → CatCenter B) (τ' : I → CatCenter B')
    (hs : ∀ i K, G'.map ((τ i).app K) = (τ' i).app (G'.obj K))
    (hC : IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
      adj.unit.app M ≫ U.map ((τ i).app (L.obj M))))
    (hD : IsIso (Sigma.desc (f := fun _ : I ↦ G.obj M) fun i ↦
      adj'.unit.app (G.obj M) ≫
        U'.map ((τ' i).app (L'.obj (G.obj M)))))
    (hc : IsIso (Sigma.desc fun i : I ↦ G.map (Sigma.ι (fun _ : I ↦ M) i))) :
    IsIso (β.app M) := by
  exact centralUnitCopower adj adj' β hκ M I τ τ' hs hC hD hc

private theorem coefficientDerivedCoproducts (Λ : Sheaf
    (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Z : Scheme.{u}) : HasCoproducts.{u + 1}
      (DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ Z))) := by
  let C := Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    CategoryTheory.IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfShape.of_small.{u + 1, u + 1} C (Discrete J)
  exact CategoryTheory.derived_hasCoproducts


private theorem centralUnitCopower_iff
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} [U'.ReflectsIsomorphisms]
    (β : G ⋙ L' ⟶ L ⋙ G') (hκ : IsIso (mateEquiv adj adj' β))
    (M : A) (I : Type*) [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦ G.obj M)]
    (τ : I → CatCenter B) (τ' : I → CatCenter B')
    (hs : ∀ i K, G'.map ((τ i).app K) = (τ' i).app (G'.obj K))
    (hC : IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
      adj.unit.app M ≫ U.map ((τ i).app (L.obj M))))
    (hD : IsIso (Sigma.desc (f := fun _ : I ↦ G.obj M) fun i ↦
      adj'.unit.app (G.obj M) ≫
        U'.map ((τ' i).app (L'.obj (G.obj M)))))
    : IsIso (β.app M) ↔
      IsIso (Sigma.desc fun i : I ↦ G.map (Sigma.ι (fun _ : I ↦ M) i)) := by
  have := hC
  have := hD
  apply Adjunction.isIso_iff_unitCoproductComparison adj adj' β hκ M I
    (fun i ↦ (τ i).app _) (fun i ↦ (τ' i).app _)
  intro i
  exact ((τ' i).naturality (β.app M)).symm.trans
    (congrArg (fun g ↦ β.app M ≫ g) (hs i (L.obj M))).symm

set_option maxHeartbeats 400000 in
-- The comparison elaborates derived adjunctions in several internal module categories.
/-- The scalar-basis argument for an arbitrary copower, with its continuity input explicit. -/
private theorem push_of_pointCopower_iff_continuity
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (I : Type (u + 1))
    [HasCoproducts.{u + 1} (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R)]
    (e : (∐ fun _ : I ↦ Mod.regular R) ≅ (Mod.comap a).obj (Mod.regular S))
    : IsIso (derivedPushHom a f) ↔
      ∀ M : DerivedCategory
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)),
      let := coefficientDerivedCoproducts R X
      let := coefficientDerivedCoproducts R Y
      IsIso (sigmaComparison R((f)_*⟦R⟧) (fun _ : I ↦ M)) := by
  classical
  obtain ⟨b, hb, hflat, hunit⟩ := scheme_basis_from_point R S a I e
  have hderived (Z : Scheme.{u})
      (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj R Z))) [HasCoproduct (fun _ : I ↦ M)] :
      IsIso (Sigma.desc fun i ↦ Mod.qbar_scalarUnitLeg
        (coefficientMap a Z) (b Z i) M) := by
    let : HasColimitsOfSize.{u + 1, u + 1}
        (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) :=
      IsGrothendieckAbelian.hasColimits _
    let : HasCoproducts.{u + 1}
        (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) :=
      fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
    exact qbar_isIso_unit _ (b Z) (fun N ↦ hunit Z N) M
  let := coefficientDerivedCoproducts R X
  let := coefficientDerivedCoproducts R Y
  have hcomp (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))) :
      IsIso ((derivedPushHom a f).app M) ↔
        IsIso (sigmaComparison R((f)_*⟦R⟧) (fun _ : I ↦ M)) := by
    have : HasCoproduct (fun _ : I ↦ M) :=
      (coefficientDerivedCoproducts R X I).has_colimit _
    have : HasCoproduct (fun _ : I ↦ R((f)_*⟦R⟧).obj M) :=
      (coefficientDerivedCoproducts R Y I).has_colimit _
    have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap a Y)).ReflectsIsomorphisms :=
      Mod.restrictionReflectsIsomorphisms _
    have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap a
          Y)).mapDerivedCategory.ReflectsIsomorphisms := reflectsDerivedIsomorphisms _
    have hκ : IsIso (mateEquiv
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          a X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          a Y))
        (derivedPushHom a f)) := by
      unfold derivedPushHom
      exact Adjunction.isIso_mate_pushHomOfComapIso _ _ _
    refine centralUnitCopower_iff
      (G := R((f)_*⟦R⟧))
      (G' := R((f)_*⟦S⟧))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
        a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
        a Y))
      (derivedPushHom a f) hκ M I
      (fun i ↦ qbar_derivedCenter (Mod.qbar_scalarNatEndo (b X i)))
      (fun i ↦ qbar_derivedCenter (Mod.qbar_scalarNatEndo (b Y i))) ?_ ?_ ?_
    · intro i K
      exact qbar_lowerStar_derivedScalarEndo_of_eq f (b X i) (b Y i) (hb f i) K
    · simpa only [Mod.qbar_scalarUnitLeg_eq] using hderived X M
    · simpa only [Mod.qbar_scalarUnitLeg_eq] using
        hderived Y (R((f)_*⟦R⟧).obj M)
  constructor
  · intro h M
    have := h
    exact (hcomp M).1 (NatIso.isIso_app_of_isIso _ M)
  · intro h
    have (M : DerivedCategory
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))) :
        IsIso ((derivedPushHom a f).app M) := (hcomp M).2 (h M)
    exact NatIso.isIso_of_isIso_app _

/-! ### (Push) and (Shriek) -/

section Push

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 400000 in
-- The generic mate comparison elaborates several derived adjunctions.
/-- A finite point copower gives finite scalar units on schemes; the mate criterion then
reduces coefficient pushforward to additivity of the derived direct image. -/
private theorem finitePush_of_pointCopower
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (I : Type (u + 1)) [Finite I]
    [HasCoproducts.{u + 1} (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R)]
    (e : (∐ fun _ : I ↦ Mod.regular R) ≅ (Mod.comap a).obj (Mod.regular S)) :
    IsIso (derivedPushHom a f) := by
  classical
  obtain ⟨b, hb, hflat, hunit⟩ := scheme_basis_from_point R S a I e
  have hderived (Z : Scheme.{u})
      (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj R Z))) [HasCoproduct (fun _ : I ↦ M)] :
      IsIso (Sigma.desc fun i ↦ Mod.qbar_scalarUnitLeg
        (coefficientMap a Z) (b Z i) M) := by
    let : HasColimitsOfSize.{u + 1, u + 1}
        (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) :=
      IsGrothendieckAbelian.hasColimits _
    let : HasCoproducts.{u + 1}
        (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) :=
      fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
    exact qbar_isIso_unit _ (b Z) (fun N ↦ hunit Z N) M
  have hcomp (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))) :
      IsIso ((derivedPushHom a f).app M) := by
    have : HasCoproduct (fun _ : I ↦ M) :=
      (coefficientDerivedCoproducts R X I).has_colimit _
    have : HasCoproduct (fun _ : I ↦ R((f)_*⟦R⟧).obj M) :=
      (coefficientDerivedCoproducts R Y I).has_colimit _
    have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap a Y)).ReflectsIsomorphisms :=
      Mod.restrictionReflectsIsomorphisms _
    have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap a
          Y)).mapDerivedCategory.ReflectsIsomorphisms := reflectsDerivedIsomorphisms _
    have hκ : IsIso (mateEquiv
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          a X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          a Y))
        (derivedPushHom a f)) := by
      unfold derivedPushHom
      exact Adjunction.isIso_mate_pushHomOfComapIso _ _ _
    refine centralUnitCopowerExplicit
      (G := R((f)_*⟦R⟧))
      (G' := R((f)_*⟦S⟧))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
        a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
        a Y))
      (derivedPushHom a f) hκ M I
      (fun i ↦ qbar_derivedCenter (Mod.qbar_scalarNatEndo (b X i)))
      (fun i ↦ qbar_derivedCenter (Mod.qbar_scalarNatEndo (b Y i))) ?_ ?_ ?_ ?_
    · intro i K
      exact qbar_lowerStar_derivedScalarEndo_of_eq f (b X i) (b Y i) (hb f i) K
    · simpa only [Mod.qbar_scalarUnitLeg_eq] using hderived X M
    · simpa only [Mod.qbar_scalarUnitLeg_eq] using
        hderived Y (R((f)_*⟦R⟧).obj M)
    · have : Finite I := inferInstance
      have : R((f)_*⟦R⟧).Additive := inferInstance
      have : PreservesFiniteCoproducts R((f)_*⟦R⟧) :=
        inferInstance
      have : PreservesColimitsOfShape (Discrete I)
          R((f)_*⟦R⟧) := inferInstance
      exact inferInstanceAs (IsIso (sigmaComparison
        R((f)_*⟦R⟧) (fun _ : I ↦ M)))
  exact NatIso.isIso_of_isIso_app _

set_option maxHeartbeats 800000 in
-- Matching the concrete coefficient categories compares canonical subfield structures.
/-- **(Push)** is an isomorphism for a finite extension `F/E`, on all unbounded objects: `F_X`
is finite free over `E_X`, so both sides are finite direct sums of copies of `Rf_*^E`. See the
module docstring. -/
instance isIso_derivedPushHom_padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) : IsIso (derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) f) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := point_finiteCopower ℓ h
  let := hI
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) := IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  exact finitePush_of_pointCopower f _ _
    (Profinite.padicSubfieldRingObjMap ℓ h) I e

-- STATEMENT-DISPUTED: the mate criterion makes this force infinite copower continuity,
-- hence countable coproduct continuity. The generic-point counterexample extends to
-- internal E_X-modules via scalar action (r * s)(t) = r|_t * s(t) on coevaluation.
-- See the B5 report for the ringed argument and its remaining formalization checks.
/-- **(Push)** is an isomorphism for `E ⊆ ℚ̄_ℓ` and `f` *proper*, on all unbounded objects: `Rf_*`
then admits a right adjoint `Rf^!`, hence commutes with the coproducts through which the derived
extension of scalars along the flat `E_X ⟶ ℚ̄_ℓ,X` is computed. See the module docstring. -/
instance isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper [IsProper f]
    (E : FiniteIntermediateField ℓ) :
    IsIso (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) :=
  sorry

variable [HasCompactification f]

/-- **(Shriek)** is an isomorphism for a finite extension `F/E`, on all unbounded objects. -/
example {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsIso (derivedLowerShriekHom (Profinite.padicSubfieldRingObjMap ℓ h) f) :=
  inferInstance

/-- **(Shriek)** is an isomorphism for `E ⊆ ℚ̄_ℓ`, on all unbounded objects: the proper part of
the compactification contributes (Push) for a proper morphism, which is an isomorphism. -/
example (E : FiniteIntermediateField ℓ) :
    IsIso (derivedLowerShriekHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) :=
  inferInstance

end Push

end CondensedRing

end AlgebraicGeometry.ProEtale
