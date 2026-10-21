/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-!
# The complete linear system of a closed-immersion subsystem

Source: Stacks Project, Constructions, Lemma 01NE and Definition 01NF; Morphisms, Lemmas 07RK
and 01W6; Étale Morphisms, Lemma 04XV; the projection argument in
`lem-pc-very-ample-ample`
(blueprint: lem-pc-complete-linear-system-closed).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHom_eq_generatingSections
    {Y S : Scheme.{u}} {I : Type u} [Finite I] (g : Y ⟶ S)
    (L : Y.Modules) [L.IsInvertible] (s : I → L.sections)
    (U : I → Y.Opens)
    (hs : ∀ i, IsFreeGenerator (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
      ((s i).val (Opposite.op ⊤)))) (hU : ⨆ i, U i = ⊤)
    (hgen : Epi (L.freeHomEquiv.symm s)) :
    homOfIsFreeGenerator (fun i ↦ (s i).val (Opposite.op ⊤)) U hs g hU =
      homOfGeneratingSections I g L s hgen := by
  let a : I → Γ(L, ⊤) := fun i ↦ (s i).val (Opposite.op ⊤)
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let φ := homOfIsFreeGenerator a U hs (specULiftZIsTerminal.from Y) hU
  let ε := asIso (twistRestrictHom a U hs (specULiftZIsTerminal.from Y) hU)
  let adj := Classical.choose (exists_tensorPullbackAdjunction φ)
  let c := (adj.leftAdjointUniq (pullbackPushforwardAdjunction φ)).app (twist I Z 1)
  have he : ∃ e : (tensorPullback φ).obj (twist I Z 1) ≅ L,
      ∀ i, e.hom.app ⊤ ((adj.unit.app (twist I Z 1)).val.app (Opposite.op ⊤)
        (twistOneSection I Z i)) = a i := by
    refine ⟨c ≪≫ ε, ?_⟩
    intro i
    have ht : c.hom.app ⊤ ((adj.unit.app (twist I Z 1)).val.app (Opposite.op ⊤)
        (twistOneSection I Z i)) = pullbackSection φ (twistOneSection I Z i) := by
      exact congrArg (fun t ↦ t.val.app (Opposite.op ⊤) (twistOneSection I Z i))
        (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction φ) (twist I Z 1))
    simp only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply]
    erw [ht]
    simpa only [φ, ε, asIso_hom, Scheme.Hom.preimage_top, presheaf_map_id_apply]
      using twistRestrictHom_app_pullbackSection a U hs (specULiftZIsTerminal.from Y) hU i
  have hφ : φ = integralHomOfGeneratingSections I L s hgen :=
    (Classical.choose_spec (generatingSections_integralHom_exists I L s hgen)).2 φ he
  apply (homOfGeneratingSections_spec I g L s hgen).2.2
  · exact homOfIsFreeGenerator_over a U hs g hU
  · rw [← hφ]
    apply Scheme.Opens.hom_ext_of_iSup_eq_top U hU
    intro i
    simp only [φ, a, ι_homOfIsFreeGenerator_assoc, localHom, homOfSections_toProjInt]

open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatingSections_pair
    {Y S : Scheme.{u}} {I : Type u} [Finite I] (g : Y ⟶ S)
    (L : Y.Modules) [L.IsInvertible] (s : I → L.sections)
    (hgen : Epi (L.freeHomEquiv.symm s)) :
    ∃ ε : twistRestrict (homOfGeneratingSections I g L s hgen) 1 ≅ L,
      ∀ i, ε.hom.app _ (pullbackSection _ (twistOneSection I S i)) =
        L.presheaf.map (homOfLE (le_top :
          homOfGeneratingSections I g L s hgen ⁻¹ᵁ ⊤ ≤ ⊤)).op
            ((s i).val (Opposite.op ⊤)) := by
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let ψ := integralHomOfGeneratingSections I L s hgen
  obtain ⟨e, he⟩ := integralHomOfGeneratingSections_spec I L s hgen
  let adj := Classical.choose (exists_tensorPullbackAdjunction ψ)
  let c := (adj.leftAdjointUniq (pullbackPushforwardAdjunction ψ)).app (twist I Z 1)
  let ε : twistRestrict ψ 1 ≅ L := c.symm ≪≫ e
  have hε (i : I) : ε.hom.app _ (pullbackSection ψ (twistOneSection I Z i)) =
      L.presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ ⊤ ≤ ⊤)).op
        ((s i).val (Opposite.op ⊤)) := by
    have hc : c.hom.app ⊤ ((adj.unit.app (twist I Z 1)).val.app (Opposite.op ⊤)
        (twistOneSection I Z i)) = pullbackSection ψ (twistOneSection I Z i) := by
      exact congrArg (fun t ↦ t.val.app (Opposite.op ⊤) (twistOneSection I Z i))
        (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction ψ) (twist I Z 1))
    simp only [Scheme.Hom.preimage_top, ε, Iso.trans_hom, Iso.symm_hom, Hom.comp_app,
      ConcreteCategory.comp_apply]
    rw [← hc]
    have hi (x) : c.inv.app ⊤ (c.hom.app ⊤ x) = x := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
      rfl
    rw [hi]
    simpa only [presheaf_map_id_apply] using he i
  let U (i : I) : Y.Opens := ψ ⁻¹ᵁ standardOpen I Z i
  have hU : ⨆ i, U i = ⊤ := ψ.iSup_preimage_eq_top (iSup_standardOpen I Z)
  have hs (i : I) : IsFreeGenerator (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
      ((s i).val (Opposite.op ⊤))) := isFreeGenerator_of_twistRestrict_iso ε.hom hε i
  rw [← nativeHom_eq_generatingSections g L s U hs hU hgen]
  exact ⟨asIso (twistRestrictHom _ U hs g hU),
    twistRestrictHom_app_pullbackSection _ U hs g hU⟩

/-- A finite-dimensional subsystem whose associated morphism is a closed immersion forces the
complete linear system to give a closed immersion, pulling back `O(1)` to the same module.
The subsystem `V` is given by a `k`-basis: a linearly independent finite family `s` of global
sections (`V` is its span); "associated morphism" is
`ProjectiveSpace.homOfGeneratingSections` of the family over `Spec k`
(def-weil-pbc-morphism-to-projective-space-by-sections), which needs `s` to generate `M`.
The complete linear system is a finite family `t` of global sections that is a `k`-basis of
`Γ(M, ⊤)`; its existence includes finite-dimensionality of `Γ(M, ⊤)`. The `k`-action on
`Γ(M, ⊤)` is restriction of scalars along `Scheme.globalSectionsRingHom`, as for `M.H n`.
Empty index types are allowed (the empty scheme has zero sections).

Source: Stacks Project, Constructions, Lemma 01NE and Definition 01NF; Morphisms, Lemmas 07RK
and 01W6 (blueprint: lem-pc-complete-linear-system-closed).

Proof:
1. An invertible module is quasi-coherent and finitely presented, so proper coherent
   cohomology is finite-dimensional in degree zero. Transport along H⁰ ≅ Γ(M).
2. Extend s to a basis indexed by J. Its index type is finite. Convert the basis vectors
   to global sections t. The inclusion of s in t and the stalk-span criterion preserve
   generation, including when the scheme or coordinate types are empty.
3. Compare the morphism defined by generating sections with the native chart construction.
   The comparison supplies a section-preserving isomorphism of its pullback of O(1) with M.
4. Each old coordinate is a coordinate of the extended basis. Apply the source library's
   mono_of_eq_sum_smul with Kronecker coefficients: since the original closed immersion is
   a monomorphism, the complete-system morphism is a monomorphism too.
5. The complete-system morphism is proper, since its composite with the separated projective
   space projection is the proper structure morphism. A proper monomorphism is a closed
   immersion (Stacks 04XV). The pullback isomorphism is supplied by step 3. -/
theorem completeLinearSystem_isClosedImmersion
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (M : X.Modules) [M.IsInvertible] :
    letI : Module k Γ(M, ⊤) :=
      Module.compHom Γ(M, ⊤) (Scheme.globalSectionsRingHom k (X := X))
    ∀ (I : Type u) [Finite I] (s : I → M.sections) (hs : Epi (M.freeHomEquiv.symm s)),
      LinearIndependent (M := Γ(M, ⊤)) k (fun i ↦ (s i).val (Opposite.op ⊤)) →
      IsClosedImmersion
        (ProjectiveSpace.homOfGeneratingSections I (X ↘ Spec (.of k)) M s hs) →
      Nonempty ((Scheme.Modules.tensorPullback
          (ProjectiveSpace.homOfGeneratingSections I (X ↘ Spec (.of k)) M s hs)).obj
            (ProjectiveSpace.twist I (Spec (.of k)) 1) ≅ M) →
      ∃ (J : Type u) (_ : Finite J) (t : J → M.sections) (ht : Epi (M.freeHomEquiv.symm t)),
        LinearIndependent (M := Γ(M, ⊤)) k (fun j ↦ (t j).val (Opposite.op ⊤)) ∧
        Submodule.span k (Set.range fun j ↦ (t j).val (Opposite.op ⊤) : Set Γ(M, ⊤)) = ⊤ ∧
        IsClosedImmersion
          (ProjectiveSpace.homOfGeneratingSections J (X ↘ Spec (.of k)) M t ht) ∧
        Nonempty ((Scheme.Modules.tensorPullback
            (ProjectiveSpace.homOfGeneratingSections J (X ↘ Spec (.of k)) M t ht)).obj
              (ProjectiveSpace.twist J (Spec (.of k)) 1) ≅ M) :=
  open Scheme.Modules ProjectiveSpace in by
  classical
  let : Module k Γ(M, ⊤) :=
    Module.compHom Γ(M, ⊤) (Scheme.globalSectionsRingHom k (X := X))
  intro I _ s hs hli hj _
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    IsInvertible.sheafOfModules_isInvertible M
  have : M.IsFiniteLocallyFree := SheafOfModules.IsInvertible.isFiniteLocallyFree M
  have : M.IsFinitePresentation := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation M
  have : FiniteDimensional k (M.H 0) := finiteDimensional_H_of_isProper M 0
  let e : M.H 0 ≃ₗ[k] Γ(M, ⊤) :=
    { H.zeroLinearEquiv M with
      map_smul' := fun r x ↦ (H.zeroLinearEquiv M).map_smul
        (Scheme.globalSectionsRingHom k r) x }
  have : FiniteDimensional k Γ(M, ⊤) := e.finiteDimensional
  let b := Module.Basis.extend hli.linearIndepOn_id
  let J := hli.linearIndepOn_id.extend (Set.subset_univ _)
  have : Finite J := Module.Finite.finite_basis b
  let f (i : I) : J := ⟨(s i).val (Opposite.op ⊤),
    hli.linearIndepOn_id.subset_extend _ (Set.mem_range_self i)⟩
  let t (j : J) : M.sections := M.unitHomEquiv (homOfGlobalSection M (b j))
  have htval (j : J) : (t j).val (Opposite.op ⊤) = b j := by
    exact (homOfGlobalSection_app_one M (b j) ⊤).trans (presheaf_map_id_apply _ _)
  have hbf (i : I) : b (f i) = (s i).val (Opposite.op ⊤) :=
    Module.Basis.extend_apply_self _ (f i)
  have ht : Epi (M.freeHomEquiv.symm t) := by
    rw [generating_sections_iff_stalk_span]
    intro x
    apply top_unique
    rw [← (generating_sections_iff_stalk_span X M s).mp hs x]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, congrArg (TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial)
      ((htval (f i)).trans (hbf i))⟩
  refine ⟨J, inferInstance, t, ht, ?_, ?_, ?_, ?_⟩
  · simpa only [htval] using b.linearIndependent
  · simpa only [htval] using b.span_eq
  · obtain ⟨εt, hεt⟩ := generatingSections_pair (X ↘ Spec (.of k)) M t ht
    obtain ⟨εs, hεs⟩ := generatingSections_pair (X ↘ Spec (.of k)) M s hs
    let _ := Fintype.ofFinite J
    have : Mono (homOfGeneratingSections I (X ↘ Spec (.of k)) M s hs) :=
      inferInstance
    have : Mono (homOfGeneratingSections J (X ↘ Spec (.of k)) M t ht) := by
      apply mono_of_eq_sum_smul εt.hom hεt εs.hom hεs
        (homOfGeneratingSections_spec J (X ↘ Spec (.of k)) M t ht).1
        (c := fun i j ↦ if j = f i then 1 else 0)
      · intro i
        simp [apply_ite, htval, hbf]
      · exact (homOfGeneratingSections_spec I (X ↘ Spec (.of k)) M s hs).1
    have : IsProper (homOfGeneratingSections J (X ↘ Spec (.of k)) M t ht ≫
        ℙ(J; Spec (.of k)) ↘ Spec (.of k)) := by
      rw [(homOfGeneratingSections_spec J (X ↘ Spec (.of k)) M t ht).1]
      infer_instance
    have : IsProper (homOfGeneratingSections J (X ↘ Spec (.of k)) M t ht) :=
      IsProper.of_comp _ (ℙ(J; Spec (.of k)) ↘ Spec (.of k))
    exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  · obtain ⟨ε, _⟩ := generatingSections_pair (X ↘ Spec (.of k)) M t ht
    let φ := homOfGeneratingSections J (X ↘ Spec (.of k)) M t ht
    let adj := Classical.choose (exists_tensorPullbackAdjunction φ)
    exact ⟨(adj.leftAdjointUniq (pullbackPushforwardAdjunction φ)).app _ ≪≫ ε⟩

end AlgebraicGeometry
