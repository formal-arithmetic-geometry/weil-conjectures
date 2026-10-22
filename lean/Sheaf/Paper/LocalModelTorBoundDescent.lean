/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.CategoryTheory.InternalSectionModuleFlat
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Tor bounds from bounded flat models on a finite pro-etale cover

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2) Local models; Stacks Tags 06YQ, 06YY, 07A4, 06YU
(blueprint: lem-sfb-local-model-tor-bound-descent).

Module objects are identified with sectionwise module sheaves by the existing
`InternalAbelianSheafModule.sectionModuleEquivalence`. Flatness below uses exactly
`SheafOfModules.IsFlatOnSite` on that sectionwise encoding. The derived tensor and Tor
amplitude use the internal-module encoding of the recorded Tor-amplitude dependency.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem flatTensorCalculation
    {A : Type*} [Category A] [Abelian A] [IsGrothendieckAbelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A]
    (P : CochainComplex A ℤ) (r s : ℤ)
    (hbound : ∀ q : ℤ, q < r ∨ s < q → IsZero (P.X q))
    (hflat : ∀ q : ℤ, ObjectProperty.flat (P.X q)) :
    (∀ N : A, Nonempty (DerivedCategory.Q.obj P ⊗
      (DerivedCategory.singleFunctor A 0).obj N ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P
        ((CochainComplex.singleFunctor A 0).obj N) (curriedTensor A)))) ∧
      (∀ (N : A) (q : ℤ), q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor A q).obj
          (DerivedCategory.Q.obj P ⊗ (DerivedCategory.singleFunctor A 0).obj N))) := by
  let : P.IsStrictlyGE r := (P.isStrictlyGE_iff r).2 (fun q hq ↦ hbound q (Or.inl hq))
  let : P.IsStrictlyLE s := (P.isStrictlyLE_iff s).2 (fun q hq ↦ hbound q (Or.inr hq))
  have hk := CochainComplex.kFlat_of_bounded_of_flat P r s hflat
  constructor
  · intro N
    exact ⟨DerivedCategory.QObjTensorSingleFunctorObjIso P hk N ≪≫
      DerivedCategory.Q.mapIso (CochainComplex.mapBifunctorSingle₂Iso
        (curriedTensor A) N P).symm⟩
  · intro N q hq
    have ht := DerivedCategory.torAmplitudeIn_Q_obj_of_flat P r s hflat N
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ r).1 ht.1 q hq
    · exact (DerivedCategory.isLE_iff _ s).1 ht.2 q hq

private noncomputable def transportTensorIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) (e : G ≅ F) (Q N : C) (P M : D)
    (hQ : F.obj Q ≅ P) (hN : F.obj N ≅ M)
    (t : G.obj (Q ⊗ N) ≅ G.obj Q ⊗ G.obj N) :
    F.obj (Q ⊗ N) ≅ P ⊗ M :=
  (e.app _).symm ≪≫ t ≪≫ tensorIso (e.app Q) (e.app N) ≪≫ tensorIso hQ hN

private theorem moduleZeroDescent
    (Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X] (S : Scheme.{u})
    (𝒰 : Scheme.Cover Scheme.proetalePrecoverage S)
    (H : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
    (h : ∀ i, IsZero ((CondensedRing.upperStar Γ.X (𝒰.f i)).obj H)) : IsZero H := by
  have hs : IsZero ((DerivedCategory.singleFunctor _ 0).obj H) := by
    apply (condensed_cover_restriction_conservative Γ S 𝒰).2
    intro i
    exact ((DerivedCategory.singleFunctor _ 0).map_isZero (h i)).of_iso
      (((CondensedRing.upperStar Γ.X (𝒰.f i)).mapDerivedCategorySingleFunctor 0).app H)
  exact IsZero.of_full_of_faithful_of_isZero (DerivedCategory.singleFunctor _ 0) H hs

attribute [local irreducible] CondensedRing.upperStar Functor.mapDerivedCategory
  Functor.mapDerivedCategoryHomologyFunctorIso Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.instMonoidalCategory_weilConjectures
  CategoryTheory.Mod.monoidalClosed DerivedCategory.monoidalClosed

private theorem coverHomologyZero
    (Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X] (S : Scheme.{u})
    (𝒰 : Scheme.Cover Scheme.proetalePrecoverage S)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)))
    (q : ℤ)
    (h : ∀ i, IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.upperStar Γ.X (𝒰.f i)).mapDerivedCategory.obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  apply moduleZeroDescent Γ S 𝒰
  intro i
  exact (h i).of_iso
    (((CondensedRing.upperStar Γ.X (𝒰.f i)).mapDerivedCategoryHomologyFunctorIso q).app K)

set_option linter.unusedVariables false in
/-- A common interval of bounded flat local models bounds Tor amplitude globally.
Source: blueprint main-20261015, det-prop-scalar-six-ctf.proof.md (2) Local models
(blueprint: lem-sfb-local-model-tor-bound-descent).

Proof:
1. Identify the site over each cover object with its slice by
   lem-weil-proetale-weakly-etale-localization (1). The section formula of
   def-pur-localized-ringed-site and the Cartesian coefficient isomorphism
   lem-sfb-alpha-iso identify inverse image with restriction and transport of scalars.
2. Exact inverse image commutes with cohomology and preserves quasi-isomorphisms by
   lem-weil-pbc-exact-functor-complex-cohomology. Apply lem-pc-kflat-resolution and
   lem-weil-pbc-ringed-topoi-derived-pullback to identify it with derived inverse image.
3. Apply lem-weil-pbc-ringed-topoi-derived-tensor-pullback to Q and N in degree zero,
   then substitute the given local isomorphism from the pullback of Q to L_i.
4. Each L_i is bounded above and termwise flat, hence K-flat by
   lem-pc-bounded-above-flat-kflat-site. The identity-coefficient specialization of
   lem-trf-site-derived-tensor-restriction computes its tensor with the pullback of N
   by the ordinary total tensor complex. This gives the asserted local isomorphism.
5. By def-pc-tensor-complex-sheaves, its degree-q term is L_i^q tensor g_i^*N and is
   zero outside [r,s]. Thus its cohomology vanishes there. The exact-functor cohomology
   comparison gives zero restrictions of H^q(Q tensor-derived N) on every cover member.
6. Base change the cover to any site object using def-weil-pbc-sites-and-cohomology.
   The restriction formula of def-pur-localized-ringed-site makes every restricted
   section zero. Sheaf separatedness forces every section to be zero, also for an
   empty cover. For arbitrary N and q this is the condition in
   det-def-sfb-constructible-tor-amplitude (3). No flatness of N is used. -/
theorem localModel_torBound_descent
    (Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X]
    (S : Scheme.{u})
    (Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)))
    (n : ℕ) (V : Fin n → S.ProEt)
    (hcover : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom) ∈
      Scheme.proetalePrecoverage S)
    (r s : ℤ) (hrs : r ≤ s)
    (L : ∀ i : Fin n, CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology (V i).left) Ab.{u + 1})
        (condensedRingObj Γ.X (V i).left)) ℤ)
    (hbound : ∀ (i : Fin n) (q : ℤ), q < r ∨ s < q → IsZero ((L i).X q))
    (hflat : ∀ (i : Fin n) (q : ℤ), SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (V i).left)
      (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left))
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left)).functor.obj
          ((L i).X q)))
    (model : ∀ i : Fin n,
      (CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj Q ≅
        DerivedCategory.Q.obj (L i)) :
    (∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (i : Fin n), Nonempty
        ((CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor (L i)
          ((CochainComplex.singleFunctor _ 0).obj
            ((CondensedRing.upperStar Γ.X (V i).hom).obj N)) (curriedTensor _)))) ∧
    (∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (q : ℤ), q < r ∨ s < q → IsZero
        ((DerivedCategory.homologyFunctor _ q).obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N))) ∧
    DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)) r s Q := by
  classical
  have hf (i : Fin n) (q : ℤ) : ObjectProperty.flat ((L i).X q) :=
    (InternalAbelianSheafModule.flat_iff_sectionModule
      (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left) _).2 (hflat i q)
  have hcalc (i : Fin n) :
      (∀ N : Mod (Sheaf (Scheme.ProEt.topology (V i).left) Ab.{u + 1})
          (condensedRingObj Γ.X (V i).left), Nonempty
        (DerivedCategory.Q.obj (L i) ⊗ (DerivedCategory.singleFunctor _ 0).obj N ≅
          DerivedCategory.Q.obj (CochainComplex.mapBifunctor (L i)
            ((CochainComplex.singleFunctor _ 0).obj N) (curriedTensor _)))) ∧
      (∀ (N : Mod (Sheaf (Scheme.ProEt.topology (V i).left) Ab.{u + 1})
          (condensedRingObj Γ.X (V i).left)) (q : ℤ), q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (DerivedCategory.Q.obj (L i) ⊗ (DerivedCategory.singleFunctor _ 0).obj N))) :=
    flatTensorCalculation (L i) r s (hbound i) (hf i)
  have localDerivedIso
      (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (i : Fin n) :
      (CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj
        (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
      DerivedCategory.Q.obj (L i) ⊗ (DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar Γ.X (V i).hom).obj N) := by
    let F := CondensedRing.upperStar Γ.X (V i).hom
    let e := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Γ.X (V i).hom
    let t := ((CondensedRing.leftDerivedUpperStarTensorIso Γ.X (V i).hom).app Q).app
      ((DerivedCategory.singleFunctor _ 0).obj N)
    exact transportTensorIso F.mapDerivedCategory _ e Q
      ((DerivedCategory.singleFunctor _ 0).obj N) (DerivedCategory.Q.obj (L i))
      ((DerivedCategory.singleFunctor _ 0).obj (F.obj N))
      (model i) ((F.mapDerivedCategorySingleFunctor 0).app N) t
  have localIso
      (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (i : Fin n) :
      Nonempty ((CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj
        (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor (L i)
        ((CochainComplex.singleFunctor _ 0).obj
          ((CondensedRing.upperStar Γ.X (V i).hom).obj N)) (curriedTensor _))) := by
    exact Nonempty.map (Iso.trans (localDerivedIso N i))
      ((hcalc i).1 ((CondensedRing.upperStar Γ.X (V i).hom).obj N))
  have hz (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Γ.X S)) (q : ℤ) (hq : q < r ∨ s < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N)) := by
    have hl (i : Fin n) : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N))) := by
      exact ((hcalc i).2 ((CondensedRing.upperStar Γ.X (V i).hom).obj N) q hq).of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso (localDerivedIso N i))
    let 𝒰 : Scheme.Cover Scheme.proetalePrecoverage S :=
      { I₀ := Fin n
        X i := (V i).left
        f i := (V i).hom
        mem₀ := hcover }
    exact coverHomologyZero Γ S 𝒰
      (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) q (fun i ↦ hl i)
  refine ⟨localIso, hz, ?_⟩
  intro N
  exact ⟨(DerivedCategory.isGE_iff _ r).2 (fun q hq ↦ hz N q (Or.inl hq)),
    (DerivedCategory.isLE_iff _ s).2 (fun q hq ↦ hz N q (Or.inr hq))⟩

end AlgebraicGeometry.ProEtale
