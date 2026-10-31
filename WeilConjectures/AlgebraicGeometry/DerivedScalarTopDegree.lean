/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Homology.BoundedAboveProjectiveModel
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.Factorizations.CM5a
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Top cohomology after derived extension of scalars

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-cor-trace/sk-cor-trace.proof.md, opening second paragraph;
Stacks Project, Tags 0645, 0646, 064K, 06Y6 and 00DF.
(blueprint: lem-pd-derived-scalar-top-degree).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat

section Comparison

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

-- Tensoring cycles always maps to cycles, even when the functor is not left exact.
private noncomputable def cyclesComparison (S : ShortComplex C) :
    F.obj S.cycles ⟶ (S.map F).cycles :=
  (S.map F).liftCycles (F.map S.iCycles) (by
    change F.map S.iCycles ≫ F.map S.g = 0
    rw [← F.map_comp, S.iCycles_g, F.map_zero])

omit [PreservesFiniteColimits F] in
private theorem cyclesComparison_i (S : ShortComplex C) :
    cyclesComparison F S ≫ (S.map F).iCycles = F.map S.iCycles :=
  ShortComplex.liftCycles_i _ _ _

omit [PreservesFiniteColimits F] in
private theorem toCycles_comparison (S : ShortComplex C) :
    F.map S.toCycles ≫ cyclesComparison F S = (S.map F).toCycles := by
  rw [← cancel_mono (S.map F).iCycles, Category.assoc, cyclesComparison_i,
    ← F.map_comp, ShortComplex.toCycles_i, ShortComplex.toCycles_i]
  rfl

-- Right exactness lets this map descend through the quotient by boundaries.
private noncomputable def homologyComparison (S : ShortComplex C) :
    F.obj S.homology ⟶ (S.map F).homology :=
  (CokernelCofork.IsColimit.desc'
    (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F)
    (cyclesComparison F S ≫ (S.map F).homologyπ) (by
      rw [← Category.assoc, toCycles_comparison, ShortComplex.toCycles_comp_homologyπ])).1

@[reassoc]
private theorem homologyComparison_π (S : ShortComplex C) :
    F.map S.homologyπ ≫ homologyComparison F S =
      cyclesComparison F S ≫ (S.map F).homologyπ :=
  (CokernelCofork.IsColimit.desc'
    (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F)
    (cyclesComparison F S ≫ (S.map F).homologyπ) _).2

omit [PreservesFiniteColimits F] in
private theorem cyclesComparison_naturality {S T : ShortComplex C} (f : S ⟶ T) :
    F.map (ShortComplex.cyclesMap f) ≫ cyclesComparison F T =
      cyclesComparison F S ≫ ShortComplex.cyclesMap (F.mapShortComplex.map f) := by
  rw [← cancel_mono (T.map F).iCycles]
  rw [Category.assoc, cyclesComparison_i, ← F.map_comp, ShortComplex.cyclesMap_i,
    F.map_comp, Category.assoc]
  erw [ShortComplex.cyclesMap_i]
  rw [← Category.assoc, cyclesComparison_i]
  rfl

private theorem homologyComparison_naturality {S T : ShortComplex C} (f : S ⟶ T) :
    F.map (ShortComplex.homologyMap f) ≫ homologyComparison F T =
      homologyComparison F S ≫ ShortComplex.homologyMap (F.mapShortComplex.map f) := by
  rw [← cancel_epi (F.map S.homologyπ), ← F.map_comp_assoc,
    ShortComplex.homologyπ_naturality, F.map_comp, Category.assoc,
    homologyComparison_π, homologyComparison_π_assoc,
    ← Category.assoc, cyclesComparison_naturality, Category.assoc]
  exact congrArg (fun k ↦ cyclesComparison F S ≫ k)
    (ShortComplex.homologyπ_naturality (F.mapShortComplex.map f)).symm

private theorem homologyComparison_isIso (S : ShortComplex C) (hg : S.g = 0) :
    IsIso (homologyComparison F S) := by
  have : F.PreservesLeftHomologyOf S := F.preservesLeftHomology_of_zero_g S hg
  have he : homologyComparison F S = (S.mapHomologyIso F).inv := by
    rw [← cancel_epi (F.map S.homologyπ), homologyComparison_π,
      ← cancel_mono (S.mapHomologyIso F).hom, Category.assoc,
      ShortComplex.homologyπ_comp_mapHomologyIso_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    have hc : cyclesComparison F S = (S.mapCyclesIso F).inv := by
      rw [← cancel_mono (S.map F).iCycles, cyclesComparison_i,
        ShortComplex.mapCyclesIso_inv_iCycles]
    rw [hc, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

end Comparison

/-- Derived scalar extension preserves an upper cohomological bound and identifies the
highest cohomology with ordinary scalar extension of that cohomology. The isomorphism
is specified on every K-flat representative: `t` tensors a cycle with the coefficient,
and the second equation says that `e.hom` sends its class to the class of that tensor.
The first equation determines `t` because the cycle inclusion is monic; the second
then determines `e.hom` because scalar extension preserves the epimorphism `homologyπ`.
Thus the conclusion specifies the canonical map, without choosing an arbitrary iso.

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-cor-trace/sk-cor-trace.proof.md, opening second paragraph.
(blueprint: lem-pd-derived-scalar-top-degree).

Proof:
1. Apply `lem-weil-pbc-bounded-above-projective-model` to obtain a projective complex
   `L` zero above `N` and `Q(L) ≅ P`. The homology factorization identifies its degree
   `N` cohomology with that of `P` (`def-weil-abstract-derived-category`).
2. Projective modules are flat (`lem-weil-pbc-projective-module-flat`), so the bounded
   flat criterion `lem-pc-module-bounded-flat-kflat` makes `L` K-flat. The canonical
   counit of `lem-pur-derived-change-of-rings` computes scalar extension on `L`.
3. Termwise scalar extension of `L` is zero above `N`, proving the standard bound
   (`def-sbc-standard-tstructure-derived-category`). Its degree `N` cohomology and
   that of `L` are the cokernels of their incoming differentials.
4. Tensor right exactness (`lem-weil-pbc-tensor-right-exact`) identifies these
   cokernels by `[x] tensor s ↦ [x tensor s]`. Transport through `Q(L) ≅ P` and the
   canonical counit. For any other K-flat representative, independence of K-flat
   computation gives the same map; tensoring cycle inclusions gives `t`. Passing
   to the homology quotients gives the displayed equations. No flatness of `φ` is used. -/
theorem exists_topDegreeScalarIso
    {B B' : Type u} [CommRing B] [CommRing B'] (φ : B →+* B')
    (P : DerivedCategory (ModuleCat.{u} B)) (N : ℤ)
    (hP : ∀ j : ℤ, N < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).obj P)) :
    ((ordinaryDerivedExtendScalars φ).obj P).IsLE N ∧
      ∃ e : (extendScalars φ).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) N).obj P) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B') N).obj
          ((ordinaryDerivedExtendScalars φ).obj P),
        ∀ K : CochainComplex (ModuleCat.{u} B) ℤ,
          (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat K →
          ∀ a : DerivedCategory.Q.obj K ≅ P,
          ∃ t : (extendScalars φ).obj (K.cycles N) ⟶
              (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K).cycles N,
            t ≫ (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K).iCycles N =
              (extendScalars φ).map (K.iCycles N) ∧
            (extendScalars φ).map (K.homologyπ N ≫
                (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) N).inv.app K ≫
                (DerivedCategory.homologyFunctor (ModuleCat.{u} B) N).map a.hom) ≫
              e.hom ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u} B') N).map
                ((ordinaryDerivedExtendScalars φ).map a.inv ≫
                  (ordinaryDerivedChangeOfRings φ).counit.app K) ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B') N).hom.app
                (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) =
              t ≫ (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K).homologyπ N := by
  classical
  let E := extendScalars φ
  let T := E.mapHomologicalComplex (.up ℤ)
  let F := ordinaryDerivedExtendScalars φ
  let ε := (ordinaryDerivedChangeOfRings φ).counit
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) N
  let H' := DerivedCategory.homologyFunctor (ModuleCat.{u} B') N
  let h := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) N
  let h' := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B') N
  obtain ⟨L, hp, hb, ⟨b⟩⟩ :=
    DerivedCategory.exists_boundedAbove_projective_model B P N hP
  have : L.IsStrictlyLE N := (L.isStrictlyLE_iff N).2 hb
  have (i : ℤ) : Module.Projective B (L.X i) := hp i
  have (i : ℤ) : Projective (L.X i) := inferInstance
  have hL : (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat L := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    have hz := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).1 hZ
    have ht := CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat L ⟨N, hb⟩
      (fun i ↦ inferInstance) Z hz
    have hm := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 ht
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      (β_ _ _) hm, hm⟩
  have hε : IsIso (ε.app L) := (ordinaryDerivedChangeOfRings φ).computes L hL
  let c : F.obj P ≅ DerivedCategory.Q.obj (T.obj L) :=
    F.mapIso b.symm ≪≫ asIso (ε.app L)
  have hTL : CochainComplex.IsStrictlyLE (T.obj L) N := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact E.map_isZero (hb i hi)
  have hbound : (F.obj P).IsLE N := by
    have : CochainComplex.IsStrictlyLE (T.obj L) N := hTL
    exact DerivedCategory.TStructure.t.isLE_of_iso c.symm N
  -- At the upper bound the outgoing differential is zero, so this comparison is invertible.
  have hg : (L.sc N).g = 0 := by
    apply (hb ((ComplexShape.up ℤ).next N) (by simp)).eq_of_tgt
  have hc : IsIso (homologyComparison E (L.sc N)) := homologyComparison_isIso E _ hg
  let bl : L.homology N ≅ H.obj P := h.symm.app L ≪≫ H.mapIso b
  let cl : H'.obj (F.obj P) ≅ (T.obj L).homology N :=
    H'.mapIso c ≪≫ h'.app (T.obj L)
  let e : E.obj (H.obj P) ≅ H'.obj (F.obj P) :=
    (E.mapIso bl).symm ≪≫ asIso (homologyComparison E (L.sc N)) ≪≫ cl.symm
  refine ⟨hbound, e, ?_⟩
  intro K hK a
  let bk : K.homology N ⟶ H.obj P := h.inv.app K ≫ H.map a.hom
  let ck : H'.obj (F.obj P) ⟶ (T.obj K).homology N :=
    H'.map (F.map a.inv ≫ ε.app K) ≫ h'.hom.app (T.obj K)
  -- Naturality along a projective representative makes the isomorphism canonical on every K.
  have heq : E.map bk ≫ e.hom ≫ ck = homologyComparison E (K.sc N) := by
    obtain ⟨f, hf⟩ := DerivedCategory.Q_map_surjective_of_projective L K N (b.hom ≫ a.inv)
    have : IsIso (DerivedCategory.Q.map f) := by rw [hf]; infer_instance
    have : QuasiIso f :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} B) f).1 inferInstance
    have hn : E.map (HomologicalComplex.homologyMap f N) ≫
        homologyComparison E (K.sc N) =
      homologyComparison E (L.sc N) ≫ HomologicalComplex.homologyMap (T.map f) N :=
      homologyComparison_naturality E ((HomologicalComplex.shortComplexFunctor _ _ N).map f)
    have hb' : HomologicalComplex.homologyMap f N ≫ bk = bl.hom := by
      dsimp only [bk, bl, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
      rw [← Category.assoc]
      erw [h.inv.naturality f]
      change h.inv.app L ≫ H.map (DerivedCategory.Q.map f) ≫ H.map a.hom =
        h.inv.app L ≫ H.map b.hom
      rw [← H.map_comp, hf]
      simp
    have hc' : cl.hom ≫ HomologicalComplex.homologyMap (T.map f) N = ck := by
      dsimp only [cl, ck, c, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
        Iso.symm_hom, asIso_hom]
      rw [Category.assoc]
      erw [← h'.hom.naturality (T.map f)]
      change H'.map (F.map b.inv ≫ ε.app L) ≫
        H'.map (DerivedCategory.Q.map (T.map f)) ≫ h'.hom.app (T.obj K) = _
      rw [← H'.map_comp_assoc]
      have hεn := ε.naturality f
      change F.map (DerivedCategory.Q.map f) ≫ ε.app K =
        ε.app L ≫ DerivedCategory.Q.map (T.map f) at hεn
      erw [Category.assoc, ← hεn, ← F.map_comp_assoc, hf]
      simp
    apply (cancel_epi (E.map (HomologicalComplex.homologyMap f N))).1
    rw [← E.map_comp_assoc, hb', hn]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_hom]
    change E.map bl.hom ≫ E.map bl.inv ≫
      homologyComparison E (L.sc N) ≫ cl.inv ≫ ck =
      homologyComparison E (L.sc N) ≫ HomologicalComplex.homologyMap (T.map f) N
    rw [← E.map_comp_assoc, bl.hom_inv_id, E.map_id, Category.id_comp]
    rw [← hc', Iso.inv_hom_id_assoc]
  refine ⟨cyclesComparison E (K.sc N), cyclesComparison_i E (K.sc N), ?_⟩
  change E.map (K.homologyπ N ≫ bk) ≫ e.hom ≫ ck = _
  rw [E.map_comp, Category.assoc, heq]
  exact homologyComparison_π E (K.sc N)

end ModuleCat
