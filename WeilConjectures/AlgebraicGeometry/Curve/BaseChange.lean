/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.GeometricallyConnected
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Sites.FieldExtensionInjective

/-!
# Base change of curves along a field extension

Let `k ⊆ k'` be a field extension and `C` a curve over `k`. The base change
`C_{k'} = C ×_{Spec k} Spec k'` comes with the projections `π_{k'} : C_{k'} ⟶ C` and
`C_{k'} ⟶ Spec k'`, and étale sheaves and their cohomology pull back along `π_{k'}`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.baseChangeField`: the base change `C_{k'} ⟶ Spec k'`.
- `AlgebraicGeometry.Scheme.Hom.fieldExtensionCohomologyMap`: the pullback map
  `Hᵠ(C, F) ⟶ Hᵠ(C_{k'}, F_{k'})`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.baseChangeField_isCurve`: the base change of a smooth separated
  curve is a smooth separated curve, proper or affine if `C` is.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) (k' : Type u) [Field k']
  [Algebra k k']

/-- The base change `C_{k'} ⟶ Spec k'` of a `k`-scheme `C` along a field extension `k ⊆ k'`.
(blueprint: `def-sc-field-extension`) -/
noncomputable abbrev Scheme.Hom.baseChangeField :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⟶ Spec (.of k') :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))

/-- The pullback map `ρᵠ : Hᵠ(C_ét, F) ⟶ Hᵠ((C_{k'})_ét, F_{k'})` along the projection
`π_{k'} : C_{k'} ⟶ C`, where `F_{k'} = π_{k'}^* F`.
(blueprint: `def-sc-field-extension`) -/
noncomputable abbrev Scheme.Hom.fieldExtensionCohomologyMap
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :=
  Etale.cohomologyMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F q

/-- **Base change of a curve.** Let `C` be a smooth separated quasi-compact curve over `k`,
of relative dimension one, and `k'` a field extension of `k`. Then `C_{k'}` is a smooth
separated curve over `k'` of relative dimension one; it is proper if `C` is, and affine if `C`
is.
(blueprint: `lem-sc-base-change-curve`) -/
theorem Scheme.Hom.baseChangeField_isCurve [SmoothOfRelativeDimension 1 f] [IsSeparated f]
    [QuasiCompact f] :
    SmoothOfRelativeDimension 1 (f.baseChangeField k') ∧ IsCurve (f.baseChangeField k') ∧
      (IsProper f → IsProper (f.baseChangeField k')) ∧
        (IsAffine C → IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) := by
  have hs : SmoothOfRelativeDimension 1 (f.baseChangeField k') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) inferInstance
  have : Smooth (f.baseChangeField k') := hs.smooth
  refine ⟨hs, { krullDim_le_one :=
      topologicalKrullDim_le_of_smoothOfRelativeDimension (f.baseChangeField k') 1 },
    fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  have : IsAffineHom f := isAffineHom_of_isAffine f
  exact isAffine_of_isAffineHom (f.baseChangeField k')

/-- A nonempty scheme locally of finite type over an algebraically closed field `k` has a
`k`-rational point: the residue field of a closed point is `k`. -/
lemma Scheme.exists_comp_eq_id_of_isAlgClosed [IsAlgClosed k] [LocallyOfFiniteType f]
    [Nonempty C] : ∃ s : Spec (.of k) ⟶ C, s ≫ f = 𝟙 _ := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx⟩ : (closedPoints C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := closure_closedPoints (X := C)
    rw [h, closure_empty] at this
    exact Set.empty_ne_univ this
  have hx' : IsClosed ({x} : Set C) := hx
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have := isClosed_singleton_iff_isClosedImmersion.mp hx'
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := C.fromSpecResidueField x ≫ f)).mpr inferInstance
  rw [← f.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff] at this
  have : Module.Finite k (C.residueField x) := this
  let φ := RingEquiv.ofBijective (algebraMap k (C.residueField x))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))
  refine ⟨Spec.map (CommRingCat.ofHom φ.symm.toRingHom) ≫ C.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← f.specMap_residueFieldAlgebraMap, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact φ.symm_apply_apply a

/-- **Base change of a proper connected curve.** Over an algebraically closed field `k`, the
base change of a smooth proper connected curve to a field extension `k'` is a smooth proper
connected curve over `k'`: the curve has a rational point, so it is geometrically connected.
(blueprint: `lem-sc-base-change-curve`) -/
theorem IsConnectedCurve.baseChangeField [IsAlgClosed k] [IsConnectedCurve f] [Smooth f]
    [IsProper f] : IsConnectedCurve (f.baseChangeField k') := by
  have := IsConnectedCurve.connectedSpace' f
  have : SmoothOfRelativeDimension 1 f := IsConnectedCurve.smoothOfRelativeDimension_one f
  obtain ⟨hs, hc, -, -⟩ := f.baseChangeField_isCurve k'
  obtain ⟨s, hs'⟩ := Scheme.exists_comp_eq_id_of_isAlgClosed f
  have := GeometricallyConnected.of_universallyClosed_of_section f s hs'
  have hconn : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := f.baseChangeField k')
  have : Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
    hconn.toNonempty
  exact { krullDim_le_one := hc.krullDim_le_one
          connectedSpace := hconn
          krullDim_eq_one :=
            topologicalKrullDim_eq_of_smoothOfRelativeDimension (f.baseChangeField k') 1 }

/-- **The genus is invariant under base change.** For a smooth proper curve `C` over `k` and a
field extension `k'`, `g(C_{k'}) = g(C)`: both genera are arithmetic genera
(`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`), and `H¹(C_{k'}, 𝒪) = H¹(C, 𝒪) ⊗_k k'`.
(blueprint: `lem-sc-genus-invariant`) -/
theorem Scheme.Hom.genus_baseChangeField [SmoothOfRelativeDimension 1 f] [IsProper f] :
    (f.baseChangeField k').genus = f.genus := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : QuasiCompact (C ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
  have : QuasiSeparated (C ↘ Spec (.of k)) := inferInstanceAs (QuasiSeparated f)
  have h₁ := Scheme.genus_eq_arithmeticGenus (k := k) (X := C)
  obtain ⟨hs, -, hp, -⟩ := f.baseChangeField_isCurve k'
  have := hp inferInstance
  let : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Over (Spec (.of k')) :=
    ⟨f.baseChangeField k'⟩
  have : SmoothOfRelativeDimension 1
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ↘ Spec (.of k')) := hs
  have : IsProper
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ↘ Spec (.of k')) :=
    hp inferInstance
  have h₂ := Scheme.genus_eq_arithmeticGenus (k := k')
    (X := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
  have h₃ := Scheme.arithmeticGenus_pullback (k := k) (X := C) k'
  exact h₂.trans (h₃.trans h₁.symm)

/-- The cohomology of the pullback of `ℤ/n` to the base change is that of `ℤ/n`. -/
noncomputable def Scheme.Hom.sheafHBaseChangeConstantZModAddEquiv (n q : ℕ) :
    Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj (C.constantZMod n)) q
      ≃+ Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).constantZMod n)
        q :=
  ((Sheaf.functorH _ q).mapIso ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))).addCommGroupIsoToAddEquiv

/-- **Invariance of the cohomology of a smooth proper curve.** Let `k ⊆ k'` be algebraically
closed fields, `C` a smooth proper connected curve over `k` and `n` prime to `char k`. Then the
pullback `Hᵠ(C, ℤ/n) ⟶ Hᵠ(C_{k'}, ℤ/n)` is bijective for every `q`: it is injective
(`AlgebraicGeometry.injective_cohomologyMap_pullback_fst_of_isAlgClosed`), and both groups are
finite of the same order by the curve estimate
(`AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isProper`), since `C_{k'}` is again a
smooth proper connected curve of the same genus.
(blueprint: `thm-sc-constant-invariance`, proper case) -/
theorem IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isProper [IsAlgClosed k]
    [IsConnectedCurve f] [Smooth f] [IsProper f] [IsAlgClosed k'] (n : ℕ) (hn : (n : k) ≠ 0)
    (q : ℕ) : Function.Bijective (f.fieldExtensionCohomologyMap k' (C.constantZMod n) q) := by
  have := IsConnectedCurve.connectedSpace' f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace C := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have : SmoothOfRelativeDimension 1 f := IsConnectedCurve.smoothOfRelativeDimension_one f
  have hinj := injective_cohomologyMap_pullback_fst_of_isAlgClosed f k' (C.constantZMod n) q
  obtain ⟨hs, -, hp, -⟩ := f.baseChangeField_isCurve k'
  have := hp inferInstance
  have : Smooth (f.baseChangeField k') := hs.smooth
  have := IsConnectedCurve.baseChangeField f k'
  have hn' : (n : k') ≠ 0 := by
    rw [← map_natCast (algebraMap k k')]
    exact (map_ne_zero _).2 hn
  have hg := f.genus_baseChangeField k'
  obtain ⟨⟨e₀⟩, ⟨e₁⟩, ⟨e₂⟩, h₃⟩ := IsConnectedCurve.sheafH_constantZMod_of_isProper f n hn
  obtain ⟨⟨e₀'⟩, ⟨e₁'⟩, ⟨e₂'⟩, h₃'⟩ :=
    IsConnectedCurve.sheafH_constantZMod_of_isProper (f.baseChangeField k') n hn'
  let E := f.sheafHBaseChangeConstantZModAddEquiv k' n q
  have hnz : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ 2 < q by omega) with rfl | rfl | rfl | hq
  · have : Finite (Sheaf.H
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).constantZMod
        n) 0) :=
      Finite.of_equiv _ e₀'.symm.toEquiv
    have := Finite.of_equiv _ E.symm.toEquiv
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_congr E.toEquiv, Nat.card_congr e₀.toEquiv, Nat.card_congr e₀'.toEquiv]
  · have : Finite (Sheaf.H
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).constantZMod
        n) 1) :=
      Finite.of_equiv _ e₁'.symm.toEquiv
    have := Finite.of_equiv _ E.symm.toEquiv
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_congr E.toEquiv, Nat.card_congr e₁.toEquiv, Nat.card_congr e₁'.toEquiv, hg]
  · have : Finite (Sheaf.H
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).constantZMod
        n) 2) :=
      Finite.of_equiv _ e₂'.symm.toEquiv
    have := Finite.of_equiv _ E.symm.toEquiv
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_congr E.toEquiv, Nat.card_congr e₂.toEquiv, Nat.card_congr e₂'.toEquiv]
  · have := h₃' q hq
    have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj
          (C.constantZMod n)) q) := E.toEquiv.subsingleton
    exact ⟨hinj, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end AlgebraicGeometry
