/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Sheaf.CategoryTheory.PerfectConstantLocalNullHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Local chain representatives from a perfect constant complex

Source: Stacks Project, Cohomology on Sites, Tag 09BD,
`lemma-map-out-of-locally-constant`, via Tag 08FR(1), `lemma-local-actual`
(blueprint: lem-sfb-perfect-constant-local-chain-representative).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wS wU

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Apply the recorded constant-module functor termwise, with its canonical
zero-map instance supplied by its recorded exactness theorem. This is the ordinary
termwise constant complex, with no replacement complex chosen.
Source: Stacks Project, Cohomology on Sites, Tag 09BD
(blueprint: lem-sfb-perfect-constant-local-chain-representative). -/
def constantModuleCochainFunctor {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type (max u v)) [CommRing R] :
    CochainComplex (ModuleCat.{max u v} R) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v}
        ((constantSheaf J RingCat.{max u v}).obj (RingCat.of R))) ℤ :=
  haveI := (siteConstantModuleFunctorGeneral_exact J R).1
  (siteConstantModuleFunctorGeneral J R).mapHomologicalComplex (.up ℤ)

/-- Restrict complexes by the existing module-sheaf restriction functor. The
recorded exactness theorem supplies its canonical zero-map compatibility.
Source: Stacks Project, Modules on Sites, Section 03DH; Cohomology on Sites, Tag 09BD
(blueprint: lem-sfb-perfect-constant-local-chain-representative). -/
def moduleCochainRestriction {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (S : Sheaf J RingCat.{max u v}) (U : C) :
    CochainComplex (SheafOfModules.{max u v} S) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v} (S.over U)) ℤ :=
  haveI := (ringedOverFunctor_exactGeneral S U).1
  (SheafOfModules.overFunctor.{max u v} S U).mapHomologicalComplex (.up ℤ)

/-- The canonical localization comparison identifies restriction of a localized
complex with localization of its restriction. This uses Mathlib's factorization
isomorphism for the exact restriction functor, with no arbitrary isomorphism choice.
Source: Stacks Project, Cohomology on Sites, Tags 08JB and 09BD
(blueprint: lem-sfb-perfect-constant-local-chain-representative). -/
def moduleCochainRestrictionQIso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (S : Sheaf J RingCat.{max u v}) (U : C)
    [HasDerivedCategory.{wS} (SheafOfModules.{max u v} S)]
    [HasDerivedCategory.{wU} (SheafOfModules.{max u v} (S.over U))]
    (K : CochainComplex (SheafOfModules.{max u v} S) ℤ) :
    (ringedDerivedRestrictionSized S U).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((moduleCochainRestriction S U).obj K) :=
  haveI := (ringedOverFunctor_exactGeneral S U).1
  haveI := (ringedOverFunctor_exactGeneral S U).2.1
  haveI := (ringedOverFunctor_exactGeneral S U).2.2
  (SheafOfModules.overFunctor.{max u v} S U).mapDerivedCategoryFactors.app K

/-- The homotopy cone triangle gives lifts after applying an additive functor. -/
private theorem lift_of_cone_null_homotopy
    {A D : Type*} [Category A] [Abelian A] [Category D] [Abelian D]
    (T : A ⥤ D) [T.Additive]
    {B E : CochainComplex A ℤ} (s : B ⟶ E)
    (h : Homotopy
      ((T.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr s)) 0) :
    ∃ t : (T.mapHomologicalComplex (.up ℤ)).obj E ⟶
        (T.mapHomologicalComplex (.up ℤ)).obj B,
      Nonempty (Homotopy (t ≫ (T.mapHomologicalComplex (.up ℤ)).map s) (𝟙 _)) := by
  let q := HomotopyCategory.quotient D (.up ℤ)
  let triangle := (T.mapHomotopyCategory (.up ℤ)).mapTriangle.obj
    (CochainComplex.mappingCone.triangleh s)
  have hd : triangle ∈ distTriang _ :=
    (T.mapHomotopyCategory (.up ℤ)).map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished s)
  have hz : 𝟙 _ ≫ triangle.mor₂ = 0 := by
    change 𝟙 _ ≫ q.map ((T.mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.mappingCone.inr s)) = 0
    simpa only [Category.id_comp, Functor.map_zero] using
      HomotopyCategory.eq_of_homotopy _ _ h
  obtain ⟨t, ht⟩ := triangle.coyoneda_exact₂ hd (𝟙 _) hz
  obtain ⟨t, rfl⟩ := q.map_surjective t
  refine ⟨t, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  change q.map (t ≫ (T.mapHomologicalComplex (.up ℤ)).map s) = _
  rw [Functor.map_comp]
  exact ht.symm

/-- Localizing a homotopy right inverse gives the representative of a right fraction. -/
private theorem representative_of_cone_null_homotopy
    {A D : Type*} [Category A] [Abelian A] [Category D] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (T : A ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {B E G : CochainComplex A ℤ} (s : B ⟶ E) [QuasiIso s] (g : B ⟶ G)
    (ψ : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G)
    (hψ : ψ = inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g)
    (h : Homotopy
      ((T.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr s)) 0) :
    ∃ a : (T.mapHomologicalComplex (.up ℤ)).obj E ⟶
        (T.mapHomologicalComplex (.up ℤ)).obj G,
      DerivedCategory.Q.map a = T.mapDerivedCategoryFactors.inv.app E ≫
        T.mapDerivedCategory.map ψ ≫ T.mapDerivedCategoryFactors.hom.app G := by
  obtain ⟨t, ⟨ht⟩⟩ := lift_of_cone_null_homotopy T s h
  refine ⟨t ≫ (T.mapHomologicalComplex (.up ℤ)).map g, ?_⟩
  have hn := T.mapDerivedCategoryFactors.hom.naturality s
  have hn' := T.mapDerivedCategoryFactors.hom.naturality g
  have hts := DerivedCategory.Q_map_eq_of_homotopy _ ht
  simp only [Functor.map_comp, Functor.map_id] at hts ⊢
  have ht' : DerivedCategory.Q.map t =
      inv (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map s)) := by
    apply (cancel_mono (DerivedCategory.Q.map
      ((T.mapHomologicalComplex (.up ℤ)).map s))).mp
    simpa only [IsIso.inv_hom_id] using hts
  rw [ht', hψ, Functor.map_comp, Functor.map_inv]
  apply (cancel_epi (T.mapDerivedCategoryFactors.hom.app E)).mp
  apply (cancel_epi (T.mapDerivedCategory.map (DerivedCategory.Q.map s))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, IsIso.hom_inv_id_assoc]
  simp only [Functor.comp_map] at hn hn'
  rw [← Category.assoc, hn]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact hn'.symm

/-- Every derived map from a bounded termwise finite-projective constant complex
has chain representatives on a covering. The target complex is arbitrary.
Source: Stacks Project, Cohomology on Sites, Tag 09BD, via Tags 08FR(1), 08FQ,
08FP and 08FN (blueprint: lem-sfb-perfect-constant-local-chain-representative).

Proof:
1. Write psi as a right fraction inv(Q(s)) followed by Q(g), with s a
   quasi-isomorphism into the constant source complex E. Its cone is acyclic.
2. Apply the bounded constant finite-projective local null-homotopy theorem to
   E -> Cone(s), obtaining an actual covering of X.
3. On each slice, exact restriction preserves acyclicity and quasi-isomorphisms.
   Apply restriction to the distinguished cone triangle in the homotopy category.
   The null homotopy kills its second arrow. Coyoneda exactness therefore lifts
   the identity through its first arrow. Fullness of the quotient gives a chain
   map t with t followed by the restriction of s homotopic to the identity.
4. Localization kills homotopies, so Q(t) is the inverse of Q(s). Compose t with
   the restriction of g. Naturality of the canonical exact-functor factorization
   for s and g gives exactly the restriction-conjugation equality in the statement.
The target complex and the fraction denominator need no bounds. The local
null-homotopy induction handles zero terms and empty covers. -/
theorem exists_perfect_constant_local_chain_representative
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (X : C) (_hX : IsTerminal X)
    (R : Type (max u v)) [CommRing R]
    [siteModuleHasDerivedCategory.{u, v, wS}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))]
    [∀ U : C, siteModuleHasDerivedCategory.{max u v, v, wU}
      (((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)).over U)]
    (F : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q))
    [∀ q : ℤ, Module.Finite R (F.X q)]
    [∀ q : ℤ, Module.Projective R (F.X q)]
    (G : CochainComplex (SheafOfModules.{max u v}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))) ℤ)
    (ψ : DerivedCategory.Q.obj ((constantModuleCochainFunctor J.toGrothendieck R).obj F) ⟶
      DerivedCategory.Q.obj G) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ a :
        (moduleCochainRestriction
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) (U i)).obj
          ((constantModuleCochainFunctor J.toGrothendieck R).obj F) ⟶
        (moduleCochainRestriction
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) (U i)).obj G,
        DerivedCategory.Q.map a =
          (moduleCochainRestrictionQIso
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) (U i)
            ((constantModuleCochainFunctor J.toGrothendieck R).obj F)).inv ≫
          (ringedDerivedRestrictionSized
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
            (U i)).map ψ ≫
          (moduleCochainRestrictionQIso
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
            (U i) G).hom := by
  let S := (constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)
  obtain ⟨B, s, hs, g, hψ⟩ := DerivedCategory.right_fac ψ
  have hsq : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp hs
  obtain ⟨I, U, f, hcover, hnull⟩ := exists_perfect_constant_local_null_homotopy
    J _hJ X R F _hbounded (CochainComplex.mappingCone s)
    ((CochainComplex.mappingCone.quasiIso_iff_acyclic s).mp hsq)
    (CochainComplex.mappingCone.inr s)
  refine ⟨I, U, f, hcover, ?_⟩
  intro i
  have : (SheafOfModules.overFunctor.{max u v} S (U i)).Additive :=
    (ringedOverFunctor_exactGeneral S (U i)).1
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v} S (U i)) :=
    (ringedOverFunctor_exactGeneral S (U i)).2.1
  have : PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v} S (U i)) :=
    (ringedOverFunctor_exactGeneral S (U i)).2.2
  exact representative_of_cone_null_homotopy
    (SheafOfModules.overFunctor.{max u v} S (U i)) s g ψ hψ (hnull i).some

end CategoryTheory
