/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import Sheaf.RingTheory.ActiveRootNormalizationData
import Sheaf.RingTheory.ActiveRootSpecifiedSplittingDescent
import Sheaf.RingTheory.RootStagePunctureIndEtaleIntegralClosure
import Sheaf.RingTheory.ActiveRootStageNormalizationRestriction
import Sheaf.RingTheory.FlatRootTowerNonzerodivisor
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberBackward
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure

/-! # Specified active-root splittings and the actual normalization

Source: Stacks Project, Tags 01ZM, 05N9, 034M and 0CBF; ILO IX Proposition 2.1,
printed pp.133--134 (blueprint: lem-sfb-active-root-tower-normalization-splitting).

Pushouts of commutative rings express tensor products canonically. In particular,
pushing out along R -> R[1/f] is localization at the structural image of f.
All comparisons below retain the structural maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Algebra.ActiveRootNormalization

private theorem unit_of_not_mem_geometricPoint
    {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ Spec (.of B))
    (e : Spec (.of A) ≅ Scheme.strictHenselizationScheme v)
    (he : Spec.map (CommRingCat.ofHom (algebraMap B A)) =
      e.hom ≫ Scheme.strictHenselizationStructuralMap v)
    (b : B) (hb : b ∉ (v (IsLocalRing.closedPoint Ω)).asIdeal) :
    IsUnit (algebraMap B A b) := by
  classical
  obtain ⟨hlocal, _⟩ := strictHenselizationLocalStructure v
  let := hlocal
  let eRing : CommRingCat.of A ≅ Scheme.strictHenselizationRing v :=
    { hom := Spec.preimage e.inv
      inv := Spec.preimage e.hom
      hom_inv_id := by
        apply Spec.map_injective
        simp
      inv_hom_id := by
        apply Spec.map_injective
        simp }
  let : IsLocalRing A := eRing.symm.commRingCatIsoToRingEquiv.isLocalRing
  let e' : Spec (.of A) ≅ Scheme.strictLocalization v :=
    e ≪≫ Scheme.Spec.mapIso (Scheme.smallStrictHenselizationColimitIso v).symm.op
  have hpoint := Scheme.strictHenselizationStructuralMap_closedPoint_eq v e'
  have hpoint' : (e.hom ≫ Scheme.strictHenselizationStructuralMap v)
      (IsLocalRing.closedPoint A) = v (IsLocalRing.closedPoint Ω) := by
    change ((e.hom ≫ Spec.map (Scheme.smallStrictHenselizationColimitIso v).inv) ≫
      Scheme.strictLocalizationToBase v) (IsLocalRing.closedPoint A) = _ at hpoint
    rw [Category.assoc, Scheme.smallStrictHenselizationColimitIso_toBase] at hpoint
    exact hpoint
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap B A))
      (IsLocalRing.closedPoint A) = v (IsLocalRing.closedPoint Ω) := by
    rw [he]
    exact hpoint'
  have hmem : algebraMap B A b ∉ IsLocalRing.maximalIdeal A := by
    intro h
    apply hb
    rw [← hmap]
    exact h
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hmem

/-- A specified punctured active-root splitting descends and restricts to the actual
normalization, with its maps retained.
Source: Stacks Tags 01ZM/05N9, 034M and 0CBF; ILO IX Proposition 2.1, pp.133--134.
(blueprint: lem-sfb-active-root-tower-normalization-splitting).

Proof:
1. Positive prime-to-p orders under divisibility are directed, with initial order 1.
   Etaleness gives finite presentation of D. The finite product Q_1^d has the finite
   idempotent presentation e_i^2=e_i, e_i e_j=0, sum e_i=1, including 1=0 for d=0.
2. Descend the specified splitting and its inverse by the morphism clause of
   lem-weil-pbc-colimit-category-fp-algebras (Stacks 05N9(2), affine 01ZM(2)).
   Finite products commute with scalar extension by the coordinate-idempotent formulas.
3. Descend both inverse equations using 05N9(3) at a common later order. This yields
   an isomorphism whose scalar extension is the prescribed theta, without assuming
   injectivity of any transition map.
4. Iterated monic quotient coordinates (lem-sfb-monic-quotient-faithful-tensor-coordinates)
   show that multiplication by f on C_m is injective. Hence its puncture embeds in
   its total fraction ring. The empty root family has basis consisting of 1.
5. The affine-chart strict-henselization theorem gives B -> A ind-etale. Tensor-colimit
   compatibility and etale base change make C_m -> S_m ind-etale.
6. Normality and lem-weil-pbc-normal-ring-integrally-closed-total identify the closure
   of C_m in C_m[1/f] with C_m. Apply ind-etale integral-closure base change (0CBF) to
   this ambient algebra. Localization commutes with tensor product. It follows that
   S_m injects into its puncture, with structural image its integral closure there.
7. Apply 0CBF again, to D_m and its actual closure E_m. Reassociate tensor products
   to identify the result with E_m tensor_B A. The root-coordinate map T_m -> S_m
   induces Q_m -> S_m[1/f]. Extend the same theta_m through this specified map.
8. An algebra isomorphism preserves monic equations. Integrality of a product tuple
   implies integrality of every coordinate, so Step 6 puts the tuple in S_m^d.
   Conversely the product of X-s_j annihilates any tuple in S_m^d. For d=0 the
   zero ring is annihilated by X. Restrict the same splitting to these closures.
9. Taking spectra gives d disjoint copies with identity structural maps, the trivial
   finite etale cover, also for d=0. Inactive parameters are units at the chosen point;
   no roots of unity, regularity, Galois group or condition on d was used.
-/
theorem activeRootTower_normalization_splitting
    (p : ℕ) (hp : p.Prime) (B : Type u) [CommRing B] [Algebra (ZMod p) B]
    [IsNoetherianRing B] (r : ℕ) (t : Fin r → B)
    (hf : Function.Injective (fun b : B ↦ (∏ i, t i) * b))
    (hnormal : ∀ (m : ℕ+) (_hm : Nat.Coprime (m : ℕ) p)
      (q : Ideal (pthRootAlgebra m r B t)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i))))
    (hfinite : D.hom.hom.Finite) (hetale : D.hom.hom.Etale)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ Spec (.of B)) (A : Type u) [CommRing A] [Algebra B A]
    (e : Spec (.of A) ≅ Scheme.strictHenselizationScheme v)
    (he : Spec.map (CommRingCat.ofHom (algebraMap B A)) =
      e.hom ≫ Scheme.strictHenselizationStructuralMap v)
    (s : ℕ) (active : Fin s ↪ Fin r)
    (hactive : ∀ i : Fin r, i ∈ Set.range active ↔
      t i ∈ (v (IsLocalRing.closedPoint Ω)).asIdeal)
    (d : ℕ)
    (theta : extend D (activeColimit (A := A) t active p) ≅
      diagonal (activeColimit (A := A) t active p).right d) :
    (∀ i : Fin r, i ∉ Set.range active → IsUnit (algebraMap B A (t i))) ∧
    ∃ m : RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p},
      ∃ theta_m : extend D ((activeDiagram (A := A) t active p).obj m) ≅
          diagonal ((activeDiagram (A := A) t active p).obj m).right d,
        (∀ (x : D.right) (j : Fin d),
          (colimit.ι (activeDiagram (A := A) t active p) m).right
              (theta_m.hom.right (extendInclusion D _ x) j) =
            theta.hom.right (extendInclusion D _ x) j) ∧
        ∃ k : (activeDiagram (A := A) t active p).obj m ⟶
            strictPunctureOverBase (A := A) t m.1,
          (∀ a : A,
            k.right (activeInclusion (A := A) t active p m
              (algebraMap A _ a)) =
                (strictPuncture (A := A) t m.1).hom ((strictStage (A := A) t m.1).hom a)) ∧
          (∀ i : Fin s,
            k.right (activeInclusion (A := A) t active p m
              (simultaneousRoot (fun i ↦ algebraMap B A (t (active i))) m.1 i)) =
              (strictPuncture (A := A) t m.1).hom
                (strictStageMap (A := A) t m.1 (simultaneousRoot t m.1 (active i)))) ∧
          (∀ x : asAlgebra (strictPuncture (A := A) t m.1),
            IsIntegral (strictStage (A := A) t m.1).right x ↔
              ∃ a : (strictStage (A := A) t m.1).right,
                (strictPuncture (A := A) t m.1).hom a = x) ∧
          ∃ Theta : strictAmbient (A := A) t m.1 D ≅
              (Under.map (strictPuncture (A := A) t m.1).hom).obj
                (diagonal (strictPuncture (A := A) t m.1).right d),
            (∀ (x : D.right) (j : Fin d),
              Theta.hom.right (strictAmbientInclusion (A := A) t m.1 D x) j =
                k.right (theta_m.hom.right (extendInclusion D _ x) j)) ∧
            ∃ epsilon : strictClosure (A := A) t m.1 D ≅
                diagonal (strictStage (A := A) t m.1).right d,
              ((Under.pushout (strictStageMap (A := A) t m.1)).map
                  (closureInclusion (ambient t m.1 D))).right ≫ Theta.hom.right =
                epsilon.hom.right ≫
                  diagonalLocalization (strictPuncture (A := A) t m.1) d := by
  classical
  have _ := hp
  have _ := hfinite
  have hA : (algebraMap B A).IndEtale := by
    have h := Scheme.smallStrictHenselization_indEtale_of_affine_chart
      v (CommRingCat.of B) (𝟙 _) (Set.mem_range_self _) e (algebraMap B A)
      (by simpa only [Category.comp_id] using he)
    exact h
  refine ⟨?_, ?_⟩
  · intro i hi
    exact unit_of_not_mem_geometricPoint v e he (t i)
      (fun h ↦ hi ((hactive i).2 h))
  · obtain ⟨m, theta_m, htheta⟩ := activeRootTower_specified_splitting_descends
      t active p D hetale.finitePresentation d theta
    have hregular : Function.Injective
        (fun x : pthRootAlgebra m.1 r B t ↦ algebraMap B _ (∏ i, t i) * x) := by
      let F : RootTowerIndex (Set.univ : Set ℕ+) ⥤ CommRingCat.{u} :=
        simultaneousRootDiagram t Set.univ
      have hst := (flat_root_tower_nonzerodivisor B B (RingHom.id B)
        (RingHom.Flat.id B) r t (∏ i, t i) hf Set.univ (Set.mem_univ _)
        (fun n _ k _ ↦ ⟨n * k, Set.mem_univ _, Nat.dvd_mul_right _ _,
          Nat.dvd_mul_left _ _⟩)
        (↥(colimit F)) (RingHom.id _) (RingHom.Flat.id _)).2.1
      exact hst ⟨m.1, Set.mem_univ _⟩
    obtain ⟨hinj, hclosure⟩ := rootStage_puncture_indEtale_integralClosure
      t m.1 hregular (hnormal m.1 m.2) hA
    obtain ⟨k, hkA, hkroot, Theta, hTheta, epsilon, hepsilon⟩ :=
      activeRootStage_normalization_restriction t active p m hA hinj hclosure D d theta_m
    exact ⟨m, theta_m, htheta, k, hkA, hkroot, hclosure, Theta, hTheta,
      epsilon, hepsilon⟩

end Algebra.ActiveRootNormalization
