/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U7
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.Paper.FiniteCoproductCohomologyAssembly

/-! # Natural cardinalities for a single smooth proper curve

Source: Stacks Project, Etale Cohomology, Tags 03RQ and 0A5B.
(blueprint: lem-fin-smooth-proper-curve-natural-cardinalities).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The constant-coefficient cohomology cardinalities of a smooth proper curve,
without a connectedness assumption. No family or constructibility assertion occurs here.
Source: Stacks Project, Etale Cohomology, Tags 03RQ and 0A5B.
(blueprint: lem-fin-smooth-proper-curve-natural-cardinalities).

Proof: The connected components are finitely many clopen open subschemes. Restricting
smooth relative dimension one and properness makes each a smooth proper connected
curve. The connected curve calculation gives cardinalities n, n^(2g), n in degrees
zero, one, two and one thereafter. Restriction to the components identifies global
cohomology with their finite product. Coherent cohomology of the structure module is
the direct sum of that on the components, so arithmetic genus is the sum of their
genera by Serre duality. Multiplication of the component cardinalities gives the
formulas. For an empty scheme the component set is empty and all products are one. -/
theorem smooth_proper_curve_natural_cardinalities
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    letI : C.Over (Spec (.of k)) := ⟨f⟩
    let c := Nat.card (_root_.ConnectedComponents C)
    let g := Scheme.arithmeticGenus k C
    Nat.card (Sheaf.H (C.constantZMod n) 0) = n ^ c ∧
      Nat.card (Sheaf.H (C.constantZMod n) 1) = n ^ (2 * g) ∧
      Nat.card (Sheaf.H (C.constantZMod n) 2) = n ^ c ∧
      ∀ r, 2 < r → Nat.card (Sheaf.H (C.constantZMod n) r) = 1 := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := {}
  let I := _root_.ConnectedComponents C
  let : Fintype I := Fintype.ofFinite I
  let U (i : I) : C.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {i}, (isOpen_discrete {i}).preimage
      ConnectedComponents.continuous_coe⟩
  have hU : Pairwise (fun i j ↦ Disjoint (U i) (U j)) := fun i j hij ↦
    TopologicalSpace.Opens.coe_disjoint.mp
      ((Set.disjoint_singleton.mpr hij).preimage ConnectedComponents.mk)
  have hcover : ⨆ i, U i = ⊤ := eq_top_iff.mpr fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  have hclosed (i : I) : IsClosed (U i : Set C) :=
    (isClosed_discrete {i}).preimage ConnectedComponents.continuous_coe
  have hconn (i : I) : ConnectedSpace (U i) := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
    have he : (U (ConnectedComponents.mk x) : Set C) = connectedComponent x :=
      connectedComponents_preimage_singleton
    exact isConnected_iff_connectedSpace.mp (he ▸ isConnected_connectedComponent)
  let d (i : I) : (U i).toScheme ⟶ Spec (.of k) := (U i).ι ≫ f
  let (i : I) : (U i).toScheme.Over (Spec (.of k)) := ⟨d i⟩
  have hsm (i : I) : SmoothOfRelativeDimension 1 (d i) := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + 1) ((U i).ι ≫ f))
  have hprop (i : I) : IsProper (d i) := by
    have : IsClosedImmersion (U i).ι :=
      IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed i)
    exact inferInstanceAs (IsProper ((U i).ι ≫ f))
  have hcurve (i : I) : IsConnectedCurve (d i) := by
    have := hconn i
    have := hsm i
    have := hprop i
    exact { toIsCurve := { krullDim_le_one :=
              topologicalKrullDim_le_of_smoothOfRelativeDimension (d i) 1 }
            connectedSpace := inferInstance
            krullDim_eq_one :=
              topologicalKrullDim_eq_of_smoothOfRelativeDimension (d i) 1 }
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : (SheafOfModules.unit C.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have : FiniteDimensional k
      (Scheme.Modules.H (SheafOfModules.unit C.ringCatSheaf) 1) :=
    Scheme.Modules.finiteDimensional_H_of_isProper _ 1
  have hgenus : Scheme.arithmeticGenus k C = ∑ i : I, (d i).genus := by
    rw [Scheme.arithmeticGenus,
      Scheme.Modules.finrankH_eq_sum_of_pairwise_disjoint k U hU hcover]
    apply Finset.sum_congr rfl
    intro i _
    rw [Scheme.Modules.finrankH_congr k (Scheme.Modules.pullbackObjUnitIso (U i).ι)]
    have := hsm i
    have := hprop i
    let inst : (U i).toScheme.Over (Spec (.of k)) := ⟨d i⟩
    exact (@Scheme.genus_eq_arithmeticGenus _ _ (U i).toScheme inst (hsm i) (hprop i)).symm
  have hcard (r : ℕ) : Nat.card (Sheaf.H (C.constantZMod n) r) =
      ∏ i : I, Nat.card (Sheaf.H ((U i).toScheme.constantZMod n) r) := by
    obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (fun i : I ↦ (U i).ι)
      (by simpa using hcover) (by intro i j hij; simpa using hU hij)
    have h := Etale.finiteCoproductCohomologyAssembly
      (fun i : I ↦ (U i).toScheme) C (fun i ↦ (U i).ι) hc (C.constantZMod n) r
    rw [Nat.card_eq_of_bijective _ h, Nat.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    exact Nat.card_congr
      (((Sheaf.functorH _ r).mapIso
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (U i).ι).app
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))).addCommGroupIsoToAddEquiv.toEquiv)
  have hcomponent (i : I) := by
    have := hcurve i
    have := hsm i
    have := hprop i
    have : Smooth (d i) := SmoothOfRelativeDimension.smooth 1 (d i)
    exact IsConnectedCurve.sheafH_constantZMod_of_isProper (d i) n hn
  have hn0 : NeZero n := ⟨fun h ↦ hn (h ▸ Nat.cast_zero)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcard]
    simp_rw [fun i ↦ Nat.card_congr (hcomponent i).1.some.toEquiv]
    simp [Nat.card_eq_fintype_card]
    rfl
  · rw [hcard, hgenus]
    simp_rw [fun i ↦ Nat.card_congr (hcomponent i).2.1.some.toEquiv]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
  · rw [hcard]
    simp_rw [fun i ↦ Nat.card_congr (hcomponent i).2.2.1.some.toEquiv]
    simp [Nat.card_eq_fintype_card]
    rfl
  · intro r hr
    rw [hcard]
    have (i : I) : Subsingleton (Sheaf.H ((U i).toScheme.constantZMod n) r) :=
      (hcomponent i).2.2.2 r hr
    simp only [Nat.card_unique, Finset.prod_const_one]

end AlgebraicGeometry
