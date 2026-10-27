/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.RingTheory.Ideal.Cotangent
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.ImmersiveSystemSourceFirstJets
import Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.PointCount
import Mathlib.LinearAlgebra.Dimension.Finite
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # Independent first jets from an immersive linear system

Source: the finite-cover Bertini proof, paragraph 3, and Stacks Tags 01NE, 01NF, 0B2G.
(blueprint: lem-zl-immersive-system-local-cotangent-pair).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

private theorem closedPoint_residueMap_bijective
    (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] (y : Y)
    (hy : IsClosed ({y} : Set Y)) : Function.Bijective (p.residueFieldMap y).hom := by
  let := (p.residueFieldAlgebraMap y).toAlgebra
  have := p.finite_residueField_of_isClosed y hy
  have h : Function.Surjective (p.residueFieldAlgebraMap y) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
  refine ⟨(p.residueFieldMap y).hom.injective, ?_⟩
  unfold Scheme.Hom.residueFieldAlgebraMap at h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact Function.Surjective.of_comp h

private theorem tensorUnit_freeGenerator {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : Z.Modules) {U : Z.Opens} {e : Γ(M, U)}
    (he : Scheme.Modules.IsFreeGenerator e) :
    Scheme.Modules.IsFreeGenerator (M := (Scheme.Modules.tensorPullback g).obj M)
      (U := g ⁻¹ᵁ U)
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app M).app
        U e) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction g
  let b := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let c := (a.leftAdjointUniq b).app M
  have h := (he.pullback_unit_app g).app_hom c
  have hu := congrArg (fun f ↦ f.app U e) (a.unit_leftAdjointUniq_hom_app b M)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app] at hu
  change c.hom.app (g ⁻¹ᵁ U) ((a.unit.app M).app U e) =
    (b.unit.app M).app U e at hu
  rw [← hu]
  exact h

set_option linter.unusedVariables false in
/-- At a closed point of an etale pullback, an immersive linear system supplies
sections with independent first jets, together with a nonvanishing section.

Source: latest blueprint, `sk-lem-wgen-bertini-cover/lem-zl-bertini-finite-cover-curve.proof.md`,
paragraph 3; Stacks Tags 01NE, 01NF and 0B2G.
(blueprint: lem-zl-immersive-system-local-cotangent-pair).

Proof: finite type over the algebraically closed field makes t and its image rational.
Generation supplies a basis section nonzero at the image. Trivialize the line bundle
by that section and use the corresponding standard projective chart. Its coordinate
ratios pull back to the ratios of the basis sections. Since the projective map is an
immersion, its local ring map and hence its cotangent map are surjective. The classes
of the coordinate ratios minus their values therefore span the cotangent space at
the image. Subtracting the values times the nonvanishing section realizes these
classes by actual vectors of V. Etaleness and rationality make the cotangent map
to t surjective. Select two independent vectors in this spanning image, possible
by htdim, and take their k-linear combinations in V. A common affine neighbourhood
trivializes the pulled-back line bundle; the resulting coefficients have the chosen
independent germs. The originally selected section remains nonvanishing at t.
Only first jets are asserted: no prime ideal or irreducible component is chosen. -/
theorem immersiveSystem_local_cotangent_pair
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (T : Scheme.{u}) (π : T ⟶ X) [Etale π]
    (t : T) (ht : IsClosed ({t} : Set T))
    (htdim : 2 ≤ Module.finrank (IsLocalRing.ResidueField (T.presheaf.stalk t))
      (IsLocalRing.CotangentSpace (T.presheaf.stalk t)))
    (U₀ : X.Opens) (htU₀ : π t ∈ U₀)
    (L : X.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v)
    (hgen : Epi (((Scheme.Modules.tensorPullback U₀.ι).obj L).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down)))))))
    [IsImmersion (@ProjectiveSpace.homOfGeneratingSections
      (ULift.{u} (Fin r)) inferInstance U₀.toScheme (Spec (.of k))
      (U₀.ι ≫ (X ↘ Spec (.of k))) ((Scheme.Modules.tensorPullback U₀.ι).obj L)
      (Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U₀.ι)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction U₀.ι)).app L).symm)
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down))))) hgen)] :
    letI : ((Scheme.Modules.tensorPullback π).obj L).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction π)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction π)).app L).symm
    ∃ (v₁ v₂ v₃ : V),
      t ∈ Scheme.Modules.nonvanishingLocus ((Scheme.Modules.tensorPullback π).obj L)
        (Scheme.Modules.tensorSectionsUnit π L (ψ v₁)) ∧
      ∃ (U : T.affineOpens) (htU : t ∈ U.1)
        (e : Γ((Scheme.Modules.tensorPullback π).obj L, U.1)),
        Scheme.Modules.IsFreeGenerator e ∧
        ∃ f : Fin 2 → Γ(T, U.1),
          ((Scheme.Modules.tensorPullback π).obj L).presheaf.map
              (homOfLE (le_top : U.1 ≤ ⊤)).op
              (Scheme.Modules.tensorSectionsUnit π L (ψ v₂)) = f 0 • e ∧
          ((Scheme.Modules.tensorPullback π).obj L).presheaf.map
              (homOfLE (le_top : U.1 ≤ ⊤)).op
              (Scheme.Modules.tensorSectionsUnit π L (ψ v₃)) = f 1 • e ∧
          ∃ hf : ∀ i, T.presheaf.germ U.1 t htU (f i) ∈
              IsLocalRing.maximalIdeal (T.presheaf.stalk t),
            LinearIndependent (IsLocalRing.ResidueField (T.presheaf.stalk t))
              (fun i ↦ (IsLocalRing.maximalIdeal (T.presheaf.stalk t)).toCotangent
                ⟨T.presheaf.germ U.1 t htU (f i), hf i⟩) := by
  classical
  let pX := X ↘ Spec (.of k)
  let pT := π ≫ pX
  have : LocallyOfFiniteType pT := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace pX
  have hx : IsClosed ({π t} : Set X) :=
    π.closePoints_subset_preimage_closedPoints ht
  have hcot := (rational_unramified_iff_cotangent_surjective k T X pT pX π rfl t
    ht hx (closedPoint_residueMap_bijective k T pT t ht)
      (closedPoint_residueMap_bijective k X pX (π t) hx)).mp
        ⟨⊤, trivial, inferInstance, inferInstance⟩
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨U, hxU, -, e, he⟩ := Scheme.Modules.exists_isFreeGenerator L
    (x := π t) (W := ⊤) trivial
  have hjet := immersiveSystem_source_first_jets k X U₀ L V r b ψ hlinear hgen
    (π t) hx htU₀ U.1 hxU e he
  let P := (Scheme.Modules.tensorPullback π).obj L
  let : P.IsInvertible := Scheme.Modules.IsInvertible.of_iso
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction π)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction π)).app L).symm
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction π)).unit.app L
  let e' : Γ(P, π ⁻¹ᵁ U.1) := η.app U.1 e
  have he' : Scheme.Modules.IsFreeGenerator e' := tensorUnit_freeGenerator π L he
  obtain ⟨W, hW, htW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (x := t) (U := π ⁻¹ᵁ U.1) hxU
  let eW : Γ(P, W) := P.presheaf.map (homOfLE hWU).op e'
  have heW : Scheme.Modules.IsFreeGenerator eW := he'.map hWU
  let c : V → Γ(X, U.1) := fun v ↦
    he.coeff (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (ψ v))
  let f : V → Γ(T, W) := fun v ↦
    T.presheaf.map (homOfLE hWU).op (π.app U.1 (c v))
  have hcoeff (v : V) : P.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
      (Scheme.Modules.tensorSectionsUnit π L (ψ v)) = f v • eW := by
    have hc := he.coeff_smul (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (ψ v))
    have hη := Scheme.Modules.Hom.app_presheaf_map η
      (homOfLE (le_top : U.1 ≤ ⊤)) (ψ v)
    have hh : η.app U.1
        (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (ψ v)) =
        π.app U.1 (c v) • e' := by
      rw [← hc, Scheme.Modules.Hom.app_smul]
      rfl
    change η.app U.1 (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (ψ v)) =
      P.presheaf.map (homOfLE (π.preimage_mono (le_top : U.1 ≤ ⊤))).op
        (η.app ⊤ (ψ v)) at hη
    have htop : Scheme.Modules.tensorSectionsUnit π L (ψ v) = η.app ⊤ (ψ v) := by
      dsimp only [Scheme.Modules.tensorSectionsUnit, AddCommGrpCat.comp_apply]
      exact Scheme.Modules.presheaf_map_id_apply _ _
    let s : Γ(P, ⊤) := η.app ⊤ (ψ v)
    calc
      _ = P.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s :=
        congrArg (P.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) htop
      _ = P.presheaf.map (homOfLE hWU).op
          (P.presheaf.map (homOfLE (π.preimage_mono (le_top : U.1 ≤ ⊤))).op s) :=
        (Scheme.Modules.presheaf_map_homOfLE_map_homOfLE _ _ s).symm
      _ = P.presheaf.map (homOfLE hWU).op (π.app U.1 (c v) • e') :=
        congrArg (P.presheaf.map (homOfLE hWU).op) (hη.symm.trans hh)
      _ = f v • eW := Scheme.Modules.map_smul _ _ _ _
  let R := X.presheaf.stalk (π t)
  let S := T.presheaf.stalk t
  let mR := IsLocalRing.maximalIdeal R
  let mS := IsLocalRing.maximalIdeal S
  let φ : R →+* S := (π.stalkMap t).hom
  have hm : mR ≤ mS.comap φ :=
    Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le φ)
  have hm₂ : mR ^ 2 ≤ (mS ^ 2).comap φ :=
    (pow_le_pow_left' hm 2).trans (Ideal.le_comap_pow φ 2)
  have hgerm (v : V) : T.presheaf.germ W t htW (f v) =
      φ (X.presheaf.germ U.1 (π t) hxU (c v)) := by
    exact (T.presheaf.germ_res_apply (homOfLE hWU) t htW (π.app U.1 (c v))).trans
      (π.germ_stalkMap_apply U.1 t hxU (c v)).symm
  have hrealize (q : IsLocalRing.CotangentSpace S) :
      ∃ (v : V) (hv : T.presheaf.germ W t htW (f v) ∈ mS),
        mS.toCotangent ⟨T.presheaf.germ W t htW (f v), hv⟩ = q := by
    obtain ⟨qR, hqR⟩ := hcot q
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective mR qR
    obtain ⟨v, hv⟩ := hjet a.1
    have hdiff : T.presheaf.germ W t htW (f v) - φ a.1 ∈ mS ^ 2 := by
      rw [hgerm, ← map_sub]
      exact hm₂ hv
    have ha : φ a.1 ∈ mS := hm a.2
    have hv' : T.presheaf.germ W t htW (f v) ∈ mS := by
      have := mS.add_mem (Ideal.pow_le_self (by decide : 2 ≠ 0) hdiff) ha
      simpa only [sub_add_cancel] using this
    refine ⟨v, hv', ?_⟩
    rw [Ideal.mapCotangent_toCotangent] at hqR
    exact (mS.toCotangent_eq.mpr hdiff).trans hqR
  obtain ⟨v₁, hv₁⟩ := hjet 1
  have hone : T.presheaf.germ W t htW (f v₁) - 1 ∈ mS := by
    apply Ideal.pow_le_self (by decide : 2 ≠ 0)
    rw [hgerm, ← map_one φ, ← map_sub]
    exact hm₂ hv₁
  have hunit : IsUnit (T.presheaf.germ W t htW (f v₁)) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro h
    have h1 : (1 : S) ∈ mS := by
      have := mS.sub_mem h hone
      simpa only [sub_sub_cancel] using this
    exact (mS.ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal S).ne_top) h1
  have hnonvan : t ∈ Scheme.Modules.nonvanishingLocus P
      (Scheme.Modules.tensorSectionsUnit π L (ψ v₁)) := by
    apply (Scheme.Modules.mem_nonvanishingLocus_iff_generatesAt _ _ _).mpr
    apply Scheme.Modules.generatesAt_of_mem_basicOpen heW (hcoeff v₁)
    exact (T.mem_basicOpen _ t htW).mpr hunit
  obtain ⟨q, hq⟩ := exists_linearIndependent_of_le_finrank htdim
  choose v hv hqv using fun i : Fin 2 ↦ hrealize (q i)
  refine ⟨v₁, v 0, v 1, hnonvan, ⟨W, hW⟩, htW, eW, heW,
    (fun i ↦ f (v i)), hcoeff (v 0), hcoeff (v 1), hv, ?_⟩
  convert hq using 1
  exact funext hqv

end AlgebraicGeometry
