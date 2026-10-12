/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.AlgebraicGeometry.AffineFiniteProjectiveHomModel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Affine RHom of a pseudo-coherent complex is quasi-coherent

Source: Stacks Project, Tag 0A6H, clauses (1) and (3)(a)
(blueprint: lem-sc-affine-pseudo-coherent-rhom-qcoherent).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory

/-- Termwise tilde into the shared sheaf carrier preserves zero morphisms.
Source: Stacks Project, Tag 0A6H, affine calculation
(blueprint: lem-sc-affine-pseudo-coherent-rhom-qcoherent).

Proof: tilde is additive (Mathlib's tilde.functor Additive instance). Changing the
category instance to the shared SheafOfModules carrier changes neither the underlying
morphisms nor zero; therefore the image of each zero morphism is zero. -/
theorem affineTildeSheaf_preservesZeroMorphisms (R : Type u) [CommRing R] :
    (@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
        (tilde.functor (CommRingCat.of R))).PreservesZeroMorphisms := by
  exact ⟨fun _ _ ↦ tilde.map_zero⟩

attribute [instance] affineTildeSheaf_preservesZeroMorphisms

private theorem affineTildeSheaf_preservesHomology (R : Type u) [CommRing R] :
    (@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
        (tilde.functor (CommRingCat.of R))).PreservesHomology := by
  let T : ModuleCat.{u} R ⥤ SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace) := tilde.functor (.of R)
  let : T.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let G := RingedSpace.globalSectionsFunctor (Spec (.of R)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom
  have adj : T ⊣ G := tilde.adjunction
  let : T.IsLeftAdjoint := adj.isLeftAdjoint
  let : PreservesFiniteColimits T := inferInstance
  let : T.PreservesMonomorphisms := ⟨by
    intro M N f hf
    let : Mono f := hf
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U s t h
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) h⟩
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels T

private theorem affineTildeSheaf_qcoh (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))]
    (c : CochainComplex (ModuleCat.{u} R) ℤ) :
    schemeDerivedQCohProperty (Spec (CommRingCat.of R))
      (DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj c)) := by
  let T : ModuleCat.{u} R ⥤ SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace) := tilde.functor (.of R)
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : T.PreservesHomology := affineTildeSheaf_preservesHomology R
  intro n
  let e := (DerivedCategory.homologyFunctorFactors _ n).app
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj c) ≪≫ (c.sc n).mapHomologyIso T
  apply (SheafOfModules.isQuasicoherent
    (moduleRings (Spec (CommRingCat.of R)).toRingedSpace)).prop_of_iso e.symm
  exact instIsQuasicoherentOpensCarrierCarrierCommRingCatSpecOfCarrierObjModuleCatModulesFunctor _

private theorem sheafHomComplex_bounded_of_products (U : RingedSpace.{u})
    (E G H : CochainComplex (SheafOfModules.{u}
      (moduleRings U)) ℤ)
    (π : ∀ n i : ℤ, H.X n ⟶ SheafOfModules.homObj
      (R := U.sheaf) (E.X i) (G.X (i + n)))
    (hπ : ∀ n : ℤ, Nonempty (IsLimit (Fan.mk (H.X n) (π n))))
    (b a : ℤ) [E.IsStrictlyLE b] [G.IsStrictlyGE a] :
    H.IsStrictlyGE (a - b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  let fan := Fan.mk (H.X n)
    (fun i : ℤ ↦ π n i)
  have hfan : IsLimit fan := (hπ n).some
  apply (IsZero.iff_id_eq_zero _).mpr
  apply hfan.hom_ext
  rintro ⟨i⟩
  have hz : IsZero (SheafOfModules.homObj
      (R := U.sheaf) (E.X i) (G.X (i + n))) := by
    by_cases hi : b < i
    · let F := (SheafOfModules.homFunctor U.sheaf).flip.obj
        (G.X (i + n))
      exact F.map_isZero (E.isZero_of_isStrictlyLE b i hi).op
    · let F := (SheafOfModules.homFunctor U.sheaf).obj (op (E.X i))
      let : F.Additive := ⟨by
        intro M N f g
        apply SheafOfModules.hom_ext
        ext U φ
        rfl⟩
      exact F.map_isZero (G.isZero_of_isStrictlyGE a (i + n) (by omega))
  exact hz.eq_of_tgt _ _

private theorem affineHomComplex_bounded (U : RingedSpace.{u})
    (E G : CochainComplex (SheafOfModules.{u}
      (moduleRings U)) ℤ)
    (b a : ℤ) [E.IsStrictlyLE b] [G.IsStrictlyGE a] :
    (homComplex (R := U.sheaf) E G).IsStrictlyGE (a - b) := by
  classical
  have hs := Classical.choose_spec
    (homComplex_exists (C := Opens U)
      (J := Opens.grothendieckTopology U)
      (R := U.sheaf))
  let π := Classical.choose hs
  have hh := Classical.choose_spec hs
  exact sheafHomComplex_bounded_of_products U E G _
    (fun n i ↦ π E G n i (i + n) rfl) (fun n ↦ hh.1 E G n) b a

/-- Affine computation of derived internal Hom.
Source: Stacks Project, Tag 0A6H, clauses (1) and (3)(a)
(blueprint: lem-sc-affine-pseudo-coherent-rhom-qcoherent).

Proof:
1. Replace the bounded-above finite-projective representative by a homotopy equivalent
   bounded-above finite-free complex using complementary projectives (Stacks Tag 064U).
2. Truncate the second representative below its cohomological lower bound. The ordinary
   module Hom complex computes derived Hom by lem-sc-affine-projective-complex-derived-hom.
3. Termwise tilde carries the homotopy equivalence to a homotopy equivalence. Apply
   lem-sc-derived-hom-finite-free-model. In each degree only finitely many Hom factors
   occur, and finite-free Hom and the matrix differentials commute with tilde.
4. By lem-weil-pbc-localization-module-exact and
   lem-weil-pbc-spec-module-tilde-sections, cohomology commutes with tilde on principal opens.
5. The associated cohomology sheaves are quasi-coherent by
   lem-weil-pbc-spec-module-tilde-sections and vanish sufficiently far below, since a
   nonzero Hom factor requires p ≤ b and p + n ≥ a. -/
theorem affinePseudoCoherentRHomQuasiCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))]
    (P L : DerivedCategory (ModuleCat.{u} R))
    (p l : CochainComplex (ModuleCat.{u} R) ℤ)
    (_hp : ∃ b : ℤ, p.IsStrictlyLE b)
    (_hfinite : ∀ i : ℤ, Module.Finite R (p.X i))
    (_hprojective : ∀ i : ℤ, Module.Projective R (p.X i))
    (_hL : ∃ a : ℤ, L.IsGE a)
    (_eP : Nonempty (DerivedCategory.Q.obj p ≅ P))
    (_eL : Nonempty (DerivedCategory.Q.obj l ≅ L))
    (c : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : ∀ n : ℤ, c.X n ≅ ModuleCat.of R (CochainComplex.HomComplex.Cochain p l n))
    (_hc : ∀ n m : ℤ, c.d n m ≫ (e m).hom =
      (e n).hom ≫ ModuleCat.ofHom (CochainComplex.HomComplex.δ_hom R p l n m)) :
    Nonempty ((derivedInternalHom (Opens.grothendieckTopology
        (Spec (CommRingCat.of R))) (Spec (CommRingCat.of R)).sheaf).obj
      (op (DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj p)),
        DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj l)) ≅
      DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj c)) ∧
    schemeDerivedQCohProperty (Spec (CommRingCat.of R))
      ((derivedInternalHom (Opens.grothendieckTopology (Spec (CommRingCat.of R)))
        (Spec (CommRingCat.of R)).sheaf).obj
      (op (DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj p)),
        DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj l))) ∧
    ∃ a : ℤ,
      ((derivedInternalHom (Opens.grothendieckTopology (Spec (CommRingCat.of R)))
        (Spec (CommRingCat.of R)).sheaf).obj
      (op (DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj p)),
        DerivedCategory.Q.obj
        ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
          (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
            (tilde.functor (CommRingCat.of R))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj l))).IsGE a := by
  classical
  let T : ModuleCat.{u} R ⥤ SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace) := tilde.functor (.of R)
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let Tc := T.mapHomologicalComplex (ComplexShape.up ℤ)
  obtain ⟨b, hb⟩ := _hp
  obtain ⟨a, ha⟩ := _hL
  obtain ⟨el⟩ := _eL
  let : L.IsGE a := ha
  have hl : l.IsGE a := (DerivedCategory.isGE_Q_obj_iff l a).mp
    (DerivedCategory.TStructure.t.isGE_of_iso el.symm a)
  obtain ⟨E, G, f, hf, hE, hG, hfree, ⟨eg⟩, ⟨ec⟩⟩ :=
    affineFiniteProjectiveHomModel R p l b a hb hl _hfinite _hprojective c e _hc
  let : QuasiIso f := hf
  let : E.IsStrictlyLE b := hE
  let : G.IsStrictlyGE a := hG
  obtain ⟨eh⟩ := derivedInternalHom_of_boundedAbove_finiteFree
    (Spec (CommRingCat.of R)).toRingedSpace E G (Tc.obj p)
    ⟨b, fun i hi ↦ E.isZero_of_isStrictlyLE b i hi⟩ hfree
    ⟨a, fun i hi ↦ G.isZero_of_isStrictlyGE a i hi⟩ f
  let H := derivedInternalHom (Opens.grothendieckTopology (Spec (CommRingCat.of R)))
    (Spec (CommRingCat.of R)).sheaf
  let eh' := eh ≪≫ H.mapIso ((Iso.refl (DerivedCategory.Q.obj (Tc.obj p))).op.prod eg)
  let cmp := eh'.symm ≪≫ ec
  refine ⟨⟨cmp⟩, ?_, ?_⟩
  · intro n
    apply (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace)).prop_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso cmp.symm)
    exact affineTildeSheaf_qcoh R c n
  · let : (homComplex (R := (Spec (CommRingCat.of R)).sheaf) E G).IsStrictlyGE (a - b) :=
      affineHomComplex_bounded (Spec (CommRingCat.of R)).toRingedSpace E G b a
    exact ⟨a - b, DerivedCategory.TStructure.t.isGE_of_iso eh' (a - b)⟩

end CategoryTheory
