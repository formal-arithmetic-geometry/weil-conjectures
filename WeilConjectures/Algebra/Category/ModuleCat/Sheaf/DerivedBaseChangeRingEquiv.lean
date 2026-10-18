/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# Restriction of scalars along ring isomorphisms and uniqueness of derived base change

Let `(C, J)` be an essentially small site. This file records formal properties of restriction
of scalars `Res_f : D(J, A') ⥤ D(J, A)` along ring morphisms `f : A →+* A'`:

- restriction of scalars along the identity is the identity
  (`CategoryTheory.Sheaf.restrictScalarsIdIso`), so that restriction of scalars along a ring
  isomorphism is an equivalence (`CategoryTheory.Sheaf.restrictScalarsEquivalence`);
- restriction of scalars reflects bounds on the cohomology
  (`CategoryTheory.Sheaf.homologyConcentratedIn_of_derivedRestrictScalars`), being exact and
  faithful;
- two derived base changes of the same object along the same ring morphism are isomorphic
  (`CategoryTheory.Sheaf.IsDerivedBaseChange.nonempty_iso`), and along a ring isomorphism
  `e` a derived base change of `K` is `Res_{e⁻¹} K`
  (`CategoryTheory.Sheaf.isDerivedBaseChange_ringEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

section RestrictScalars

variable {R S : Type (u + 1)} [CommRing R] [CommRing S]

/-- Restriction of scalars along the identity of `R` is the identity functor, computed
objectwise by `ModuleCat.restrictScalarsId'`. -/
noncomputable def restrictScalarsIdIso (f : R →+* R) (hf : f = RingHom.id R) :
    restrictScalars J f ≅ 𝟭 (Sheaf J (ModuleCat.{u + 1} R)) :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId' f hf)))
    (fun {F G} φ ↦ (fullyFaithfulSheafToPresheaf J _).map_injective (by
      ext U : 2
      exact (ModuleCat.restrictScalarsId' f hf).hom.naturality (φ.hom.app U)))

/-- Restriction of scalars along a ring isomorphism `e : R ≃+* S` is an equivalence between
sheaves of `S`-modules and sheaves of `R`-modules, with quasi-inverse the restriction of scalars
along `e⁻¹`. -/
noncomputable def restrictScalarsEquivalence (e : R ≃+* S) :
    Sheaf J (ModuleCat.{u + 1} S) ≌ Sheaf J (ModuleCat.{u + 1} R) :=
  Equivalence.mk (restrictScalars J e.toRingHom) (restrictScalars J e.symm.toRingHom)
    ((restrictScalarsIdIso J (RingHom.id S) rfl).symm ≪≫
      (restrictScalarsCompIso J e.symm.toRingHom e.toRingHom (RingHom.id S)
        (by ext; simp)).symm)
    (restrictScalarsCompIso J e.toRingHom e.symm.toRingHom (RingHom.id R) (by ext; simp) ≪≫
      restrictScalarsIdIso J (RingHom.id R) rfl)

instance (e : R ≃+* S) : (restrictScalars J e.toRingHom).IsEquivalence :=
  (restrictScalarsEquivalence J e).isEquivalence_functor

end RestrictScalars

section Reflect

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (f : A →+* A')

variable {J} in
/-- Restriction of scalars reflects bounds below on the derived category: it is exact and
faithful, so it reflects the vanishing of cohomology sheaves. -/
lemma isGE_of_isGE_derivedRestrictScalars_obj (M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A')))
    (n : ℤ) [((derivedRestrictScalars J f).obj M).IsGE n] : M.IsGE n := by
  let R := restrictScalars J f
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have h : IsZero (R.obj ((DerivedCategory.homologyFunctor _ i).obj M)) :=
    ((DerivedCategory.isGE_iff _ n).1 inferInstance i hi).of_iso
      ((R.mapDerivedCategoryHomologyFunctorIso i).app M)
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact R.map_injective (by rw [R.map_id, h, R.map_zero])

variable {J} in
/-- Restriction of scalars reflects bounds above on the derived category: it is exact and
faithful, so it reflects the vanishing of cohomology sheaves. -/
lemma isLE_of_isLE_derivedRestrictScalars_obj (M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A')))
    (n : ℤ) [((derivedRestrictScalars J f).obj M).IsLE n] : M.IsLE n := by
  let R := restrictScalars J f
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have h : IsZero (R.obj ((DerivedCategory.homologyFunctor _ i).obj M)) :=
    ((DerivedCategory.isLE_iff _ n).1 inferInstance i hi).of_iso
      ((R.mapDerivedCategoryHomologyFunctorIso i).app M)
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact R.map_injective (by rw [R.map_id, h, R.map_zero])

variable {J} in
/-- Restriction of scalars reflects the concentration of cohomology in an interval. -/
lemma homologyConcentratedIn_of_derivedRestrictScalars {a b : ℤ}
    {M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A'))}
    (h : DerivedCategory.homologyConcentratedIn a b ((derivedRestrictScalars J f).obj M)) :
    DerivedCategory.homologyConcentratedIn a b M := by
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨isGE_of_isGE_derivedRestrictScalars_obj f M a,
    isLE_of_isLE_derivedRestrictScalars_obj f M b⟩

end Reflect

namespace IsDerivedBaseChange

variable {J} {A A' : Type (u + 1)} [CommRing A] [CommRing A'] {f : A →+* A'}
  {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
  {K' K'' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A'))}

/-- Two derived base changes of the same object along the same ring morphism are isomorphic. -/
lemma nonempty_iso {η : K ⟶ (derivedRestrictScalars J f).obj K'}
    {η' : K ⟶ (derivedRestrictScalars J f).obj K''} (hη : IsDerivedBaseChange η)
    (hη' : IsDerivedBaseChange η') : Nonempty (K' ≅ K'') := by
  obtain ⟨g, hg⟩ := (hη K'').2 η'
  have := hη.isIso hη' g hg
  exact ⟨asIso g⟩

end IsDerivedBaseChange

section RingEquiv

variable {J} {R S : Type (u + 1)} [CommRing R] [CommRing S] (e : R ≃+* S)

/-- For a ring isomorphism `e : R ≃+* S`, restricting scalars along `e⁻¹` and then along `e` is
the identity of `D(J, R)`. -/
noncomputable def derivedRestrictScalarsRingEquivIso :
    derivedRestrictScalars J e.symm.toRingHom ⋙ derivedRestrictScalars J e.toRingHom ≅ 𝟭 _ :=
  derivedRestrictScalarsCompIso J (f := e.toRingHom) (g := e.symm.toRingHom)
      (gf := RingHom.id R) (by ext; simp) ≪≫
    Functor.mapDerivedCategoryNatIso (restrictScalarsIdIso J (RingHom.id R) rfl) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- For a ring isomorphism `e : R ≃+* S` and `K ∈ D(J, R)`, `Res_e Res_{e⁻¹} K ≅ K`. -/
noncomputable def derivedRestrictScalarsRingEquivObjIso
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    (derivedRestrictScalars J e.toRingHom).obj ((derivedRestrictScalars J e.symm.toRingHom).obj K) ≅
      K :=
  (derivedRestrictScalarsRingEquivIso e).app K

/-- Along a ring isomorphism `e : R ≃+* S`, the restriction of scalars `Res_{e⁻¹} K` along `e⁻¹`
is a derived base change of `K`: the comparison `K ≅ Res_e Res_{e⁻¹} K` is universal, since
`Res_e` is an equivalence. -/
lemma isDerivedBaseChange_ringEquiv (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    IsDerivedBaseChange (f := e.toRingHom) (derivedRestrictScalarsRingEquivObjIso e K).inv :=
  fun _ ↦ (derivedRestrictScalarsRingEquivObjIso e K).homFromEquiv.bijective.comp
    ((Functor.FullyFaithful.ofFullyFaithful
      (derivedRestrictScalars J e.toRingHom)).map_bijective _ _)

end RingEquiv

end CategoryTheory.Sheaf
