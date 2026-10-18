/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.Paper.SmoothProperCurveNaturalCardinalities
import Sheaf.AlgebraicGeometry.ProperSmoothGeometricComponentsLocallyConstant
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-!
# Betti cardinalities of smooth projective curve families

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1610
(blueprint: lem-fin-projective-curve-betti-cardinalities).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem constructible_comp_nat {T : Type*} [TopologicalSpace T]
    (a : T → ℕ) (ha : (Set.range a).Finite)
    (hc : ∀ n : ℕ, Topology.IsConstructible {s : T | a s = n}) (F : ℕ → ℕ) :
    (Set.range (fun s ↦ F (a s))).Finite ∧
      ∀ n : ℕ, Topology.IsConstructible {s : T | F (a s) = n} := by
  classical
  refine ⟨(ha.image F).subset ?_, fun n ↦ ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨a s, ⟨s, rfl⟩, rfl⟩
  · have he : {s : T | F (a s) = n} =
        ⋃ m ∈ (Set.range a ∩ {m | F m = n}), {s : T | a s = m} := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range]
      constructor
      · intro h
        exact ⟨a s, ⟨⟨s, rfl⟩, h⟩, rfl⟩
      · rintro ⟨m, ⟨_, hm⟩, hsm⟩
        exact hsm ▸ hm
    rw [he]
    exact Topology.IsConstructible.biUnion (ha.inter_of_left _) (fun m _ ↦ hc m)

/-- Betti cardinalities and their constructibility in a smooth projective curve family.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1610
(blueprint: lem-fin-projective-curve-betti-cardinalities).

The function `b r s` names the cardinality in degree `r`. Equality with `Cardinal.mk`
asserts actual finiteness, including for the empty fibre. The component count is
`Nat.card (ConnectedComponents _)`. On a disconnected smooth proper curve, `genus`
is the dimension of global differential forms, hence the sum of the component genera.
Constructibility is written as finite range and constructible level sets.

Proof plan from the node:
1. Projectivity implies properness (lem-pc-projective-proper). Base change preserves
   properness and smoothness (lem-pc-proper-base-change), giving smooth proper fibres.
2. Use lem-sbc-smooth-curve-points-decomposition. Purity excludes the point summands;
   the remaining connected clopen curves are proper by
   lem-weil-pbc-closed-immersion-proper. Empty fibres give an empty decomposition.
3. Resolve the structure module by injectives using
   lem-sc-ringed-space-module-sheaves-enough-injectives and restrict using
   lem-sc-ringed-space-restrict-injective-resolution. Sections over the finite clopen
   decomposition are products degreewise, so cohomology is the sum of the component
   cohomologies (def-sc-ringed-space-module-cohomology).
4. By lem-sc-global-functions and def-sc-genus, coherent h0 is the component count and
   coherent h1 is the sum of genera; finite sums include the empty sum.
5. Finite type over the Noetherian base makes X Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). The rank-one structure module is coherent
   by pqf-lem-coherent-ft-locnoeth and flat over the base by lem-pc-smooth-flat.
6. Apply lem-fin-projective-flat-coherent-ranks to the structure module to obtain
   constructibility of the component count and sum of genera.
7. Choose a primitive root by lem-sc-primitive-root. Apply thm-sc-proper-cohomology to
   each connected proper component, giving ranks 1, 2g, 1 and zero above degree two.
8. Restrict coefficients via lemma-constructible-pullback-constant and assemble with
   lem-weil-pbc-finite-coproduct-cohomology-assembly. Taking cardinalities gives the
   displayed powers of the prime; the empty product has cardinality one.
9. Refine the finite constructible partitions for the component count and genus sum.
   The displayed powers are constant on every refined piece; above degree two the
   cardinality is constantly one (def-weil-constructible-subset). -/
theorem projective_curve_betti_cardinalities
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] [IsProjective f]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hinv : ∀ s : S, (ℓ : S.residueField s) ≠ 0) :
    ∃ b : ℕ → S → ℕ,
      (∀ (r : ℕ) (s : S),
        Cardinal.mk ((Etale.cohomology AddCommGrpCat.{u + 1}
          (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) (r : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)).constantZMod ℓ))) = b r s) ∧
      (∀ (r : ℕ) (s : S), b r s =
        if r = 0 ∨ r = 2 then ℓ ^ Nat.card (ConnectedComponents
          ↥(pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)))
        else if r = 1 then ℓ ^ (2 * (pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)).genus)
        else 1) ∧
      ∀ r : ℕ, (Set.range (b r)).Finite ∧
        ∀ n : ℕ, Topology.IsConstructible {s : S | b r s = n} := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  obtain ⟨n, hn, i, hi, hif⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  let := hn
  let := hi
  let Xs : S → Scheme.{u} := fun s ↦ pullback f (S.geometricPointAt s)
  let c : S → ℕ := fun s ↦ Nat.card (_root_.ConnectedComponents (Xs s))
  let g : S → ℕ := fun s ↦
    letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
      ⟨pullback.snd f (S.geometricPointAt s)⟩
    Scheme.arithmeticGenus (AlgebraicClosure (S.residueField s)) (Xs s)
  have hcard (s : S) :
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 0) = ℓ ^ c s ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 1) = ℓ ^ (2 * g s) ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 2) = ℓ ^ c s ∧
      ∀ r, 2 < r → Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) r) = 1 := by
    have hℓK : (ℓ : AlgebraicClosure (S.residueField s)) ≠ 0 := by
      simpa only [map_natCast, map_zero] using
        (algebraMap (S.residueField s)
          (AlgebraicClosure (S.residueField s))).injective.ne (hinv s)
    exact smooth_proper_curve_natural_cardinalities
      (pullback.snd f (S.geometricPointAt s)) ℓ hℓK
  have hc : (Set.range c).Finite ∧
      ∀ m : ℕ, Topology.IsConstructible (c ⁻¹' {m}) := by
    have hlocal : IsLocallyConstant c :=
      (proper_smooth_geometric_components_locally_constant f).2.1
    refine ⟨hlocal.range_finite, fun m ↦ ?_⟩
    exact (hlocal.isClosed_fiber m).isCompact.isConstructible (hlocal.isOpen_fiber m)
  have hg : (Set.range g).Finite ∧
      ∀ m : ℕ, Topology.IsConstructible (g ⁻¹' {m}) := by
    let G := SheafOfModules.unit X.ringCatSheaf
    have : G.IsFinitePresentation :=
      SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
    have h := Scheme.Modules.finite_range_and_isConstructible_finrankH_geometricFibre
      f i hif G (Scheme.Modules.isFlatOver_of_isInvertible f G) 1
    let β : S → ℕ := fun s ↦
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      ((Scheme.Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj G).finrankH
        (AlgebraicClosure (S.residueField s)) 1
    change (Set.range β).Finite ∧
      (∀ m : ℕ, Topology.IsConstructible (β ⁻¹' {m})) at h
    have heq : β = g := by
      funext s
      let : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      exact Scheme.Modules.finrankH_congr (AlgebraicClosure (S.residueField s))
        (Scheme.Modules.pullbackObjUnitIso (pullback.fst f (S.geometricPointAt s))) 1
    rwa [heq] at h
  let b : ℕ → S → ℕ := fun r s ↦
    if r = 0 ∨ r = 2 then ℓ ^ c s else if r = 1 then ℓ ^ (2 * g s) else 1
  have hnat (r : ℕ) (s : S) :
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) r) = b r s := by
    by_cases hr : r = 0 ∨ r = 2
    · rcases hr with rfl | rfl
      · exact (hcard s).1
      · exact (hcard s).2.2.1
    · by_cases hr1 : r = 1
      · subst r
        exact (hcard s).2.1
      · rw [show b r s = 1 by simp only [b, if_neg hr, if_neg hr1]]
        exact (hcard s).2.2.2 r (by omega)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro r s
    have hb : b r s ≠ 0 := by
      dsimp [b]
      split_ifs
      · exact pow_ne_zero _ hℓ.ne_zero
      · exact pow_ne_zero _ hℓ.ne_zero
      · simp only [not_false_eq_true]
    have : Finite (Sheaf.H ((Xs s).constantZMod ℓ) r) :=
      Nat.finite_of_card_ne_zero ((hnat r s).trans_ne hb)
    obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso (Xs s) r
    have he := Cardinal.mk_congr
      ((e.app ((Xs s).constantZMod ℓ)).addCommGroupIsoToAddEquiv.toEquiv)
    change Cardinal.mk (Sheaf.H ((Xs s).constantZMod ℓ) r) = _ at he
    exact he.symm.trans (Nat.cast_card.symm.trans (congrArg Nat.cast (hnat r s)))
  · intro r s
    have he : (pullback.snd f (S.geometricPointAt s)).genus = g s := by
      let inst : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      have hd : SmoothOfRelativeDimension 1 (pullback.snd f (S.geometricPointAt s)) := by
        infer_instance
      have hp : IsProper (pullback.snd f (S.geometricPointAt s)) := by infer_instance
      exact @Scheme.genus_eq_arithmeticGenus _ _ (Xs s) inst hd hp
    change b r s = if r = 0 ∨ r = 2 then ℓ ^ c s else
      if r = 1 then ℓ ^ (2 * (pullback.snd f (S.geometricPointAt s)).genus) else 1
    rw [he]
  · intro r
    by_cases hr : r = 0 ∨ r = 2
    · simpa only [b, if_pos hr] using
        constructible_comp_nat c hc.1 hc.2 (fun n ↦ ℓ ^ n)
    · by_cases hr1 : r = 1
      · simpa only [b, if_neg hr, if_pos hr1] using
          constructible_comp_nat g hg.1 hg.2 (fun n ↦ ℓ ^ (2 * n))
      · simp only [b, if_neg hr, if_neg hr1]
        refine ⟨Set.finite_range_const, fun n ↦ ?_⟩
        by_cases hn : 1 = n <;> simp [hn]

end AlgebraicGeometry
