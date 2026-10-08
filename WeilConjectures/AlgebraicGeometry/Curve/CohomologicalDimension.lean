/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.Affine
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The étale cohomological dimension of a curve

The étale cohomological dimension of a curve over an algebraically closed field is at most two,
and at most one if the curve is affine: `H^q(C_ét, F) = 0` for every torsion abelian sheaf `F`
(`CategoryTheory.Sheaf.IsTorsion`) and `q ≥ 3`, resp. `q ≥ 2`.

Neither statement needs smoothness, connectedness, or `char k` to be prime to the torsion of
`F`. The affine bound is first proved for smooth connected curves
(`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_of_two_le_of_isAffine_of_smooth`), by
comparing a torsion sheaf with its pushforward from the generic point; the general case reduces
to it (`AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_isAffine_of_forall`).

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`: `H^q(C, F) = 0` for `q ≥ 3`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`: `H^q(C, F) = 0` for
  `q ≥ 2` on an affine curve.
- `AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isAffine`: the Kummer computation
  of `H^q(C, ℤ/n)` on a smooth affine connected curve, for `n` prime to `char k`.
- `AlgebraicGeometry.subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero`: the
  cohomology of the constant sheaf `ℤ/d` on a smooth affine curve.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Vanishing in high degrees.** Let `C` be a curve over an algebraically closed field `k`.
Then `H^q(C_ét, F) = 0` for `q ≥ 3` and every torsion abelian sheaf `F` on `C_ét`: the étale
cohomological dimension of a curve over an algebraically closed field is at most two. The
sharper bound for affine `C` is
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`.
(blueprint: `sk-prop-cd`) -/
@[stacks 03SC "(1)"]
theorem subsingleton_sheafH_of_three_le (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 3 ≤ q) : Subsingleton (Sheaf.H F q) :=
  -- Proof sketch: after reducing to a smooth integral curve, the cohomology of `F` is compared
  -- with that of its pushforward from the generic point. The function field `k(C)` has
  -- cohomological dimension at most one, because every finite separable extension `L` of
  -- `k(C)` is `C₁` by Tsen's theorem `IsQuasiAlgClosed.of_trdeg_le_one`, hence has
  -- `Br(L) = 0` by `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup`. The `p`-primary
  -- part in characteristic `p` goes through the Artin–Schreier sequence.
  sorry

/-- **Generic replacement in degrees at least two.** Let `C` be a smooth integral curve over an
algebraically closed field `k`, with generic point `η : Spec k(C) ⟶ C`, and `F` a torsion étale
sheaf on `C`. Then the unit `F ⟶ η_* η^* F` induces isomorphisms `Hᵠ(C, F) ≅ Hᵠ(C, η_* η^* F)` for
`q ≥ 2`: its kernel and cokernel have zero generic restriction, hence are supported on finitely
many closed points and have no cohomology in positive degrees.
(blueprint: `lem-sc-generic-cohomology-comparison`) -/
theorem isIso_functorH_map_unit_fromSpecFunctionField (f : C ⟶ Spec (.of k)) [IsCurve f]
    [Smooth f] [IsIntegral C] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion) (q : ℕ) (hq : 2 ≤ q) :
    IsIso ((Sheaf.functorH _ q).map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        C.fromSpecFunctionField).unit.app F)) :=
  sorry

/-- **Reduction to smooth connected curves.** Let `C` be an affine curve over an algebraically
closed field `k`. If `H²(C', F') = 0` for every smooth affine connected curve `C'` over `k` and
every torsion sheaf `F'` on `C'`, then `H²(C, F) = 0` for every torsion sheaf `F` on `C`.

Cohomology of the quasi-compact quasi-separated scheme `C` commutes with filtered colimits, so
`F` may be taken constructible. A constructible sheaf embeds into a finite sum of sheaves
`π_* M` with `π : C' ⟶ C` finite and `M` a finite constant sheaf, with constructible cokernel;
since `π_*` is exact, a dimension shift reduces the claim to `F = ℤ/n`. Passing to the reduced
connected components and then to the normalization, which changes `F` only by a sheaf supported
on finitely many closed points, reduces it to smooth affine connected `C`.
(blueprint: `sk-prop-cd-affine`, the reduction step) -/
theorem subsingleton_sheafH_two_of_isAffine_of_forall (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsAffine C] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (H : ∀ (C' : Scheme.{u}) (f' : C' ⟶ Spec (.of k)), IsConnectedCurve f' → Smooth f' →
      IsAffine C' → ∀ F' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1}, F'.IsTorsion →
        Subsingleton (Sheaf.H F' 2)) :
    Subsingleton (Sheaf.H F 2) :=
  sorry

end IsCurve

namespace IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Cohomological dimension of a smooth affine curve.** Let `C` be a smooth affine connected
curve over an algebraically closed field `k`. Then `H^q(C_ét, F) = 0` for `q ≥ 2` and every
torsion abelian sheaf `F` on `C_ét`.

Degrees `q ≥ 3` are `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`. In degree two,
`H²(C, F) ≅ H²(C, η_* η^* F)` for the generic point `η` of `C`
(`AlgebraicGeometry.IsCurve.isIso_functorH_map_unit_fromSpecFunctionField`), and the latter
vanishes by `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar`.
(blueprint: `lem-sc-affine-cohomological-dimension`) -/
theorem subsingleton_sheafH_of_two_le_of_isAffine_of_smooth (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 ≤ q) : Subsingleton (Sheaf.H F q) := by
  obtain rfl | hq := hq.eq_or_lt
  · have := IsConnectedCurve.connectedSpace' f
    have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
    have : IsRegular C := IsRegular.of_smooth f
    have : IrreducibleSpace C := IsRegular.irreducibleSpace C
    have : IsReduced C := isReduced_of_isReduced_stalk C
    have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
    have := IsCurve.isIso_functorH_map_unit_fromSpecFunctionField f F hF 2 le_rfl
    let ε := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} C.fromSpecFunctionField).unit
    have : Subsingleton ((Sheaf.functorH _ 2).obj ((Etale.upperStar AddCommGrpCat.{u + 1}
        C.fromSpecFunctionField ⋙ Etale.lowerStar AddCommGrpCat.{u + 1}
          C.fromSpecFunctionField).obj F)) :=
      subsingleton_sheafH_two_lowerStar f _ (Etale.isTorsion_upperStar C.fromSpecFunctionField hF)
    exact (asIso ((Sheaf.functorH _ 2).map (ε.app F))).addCommGroupIsoToAddEquiv.subsingleton
  · exact IsCurve.subsingleton_sheafH_of_three_le f F hF q hq

end IsConnectedCurve

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Cohomological dimension of an affine curve.** Let `C` be an affine curve over an
algebraically closed field `k`. Then `H^q(C_ét, F) = 0` for `q ≥ 2` and every torsion abelian
sheaf `F` on `C_ét`: the étale cohomological dimension of an affine curve over an
algebraically closed field is at most one.

Degrees `q ≥ 3` are `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`. Degree two
reduces (`AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_isAffine_of_forall`) to smooth
affine connected curves, where it is
`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_of_two_le_of_isAffine_of_smooth`.
(blueprint: `sk-prop-cd-affine`) -/
@[stacks 03SC "(2)"]
theorem subsingleton_sheafH_of_two_le_of_isAffine (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsAffine C] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H F q) := by
  obtain rfl | hq := hq.eq_or_lt
  · exact subsingleton_sheafH_two_of_isAffine_of_forall f F hF
      fun _ f' _ _ _ F' hF' ↦
        IsConnectedCurve.subsingleton_sheafH_of_two_le_of_isAffine_of_smooth f' F' hF' 2 le_rfl
  · exact subsingleton_sheafH_of_three_le f F hF q hq

end IsCurve

/-- The constant sheaf `ℤ/d` with `d ≠ 0` is a torsion sheaf: its sections are killed by
`d`. -/
lemma Scheme.isTorsion_constantZMod (X : Scheme.{u}) {d : ℕ} (hd : d ≠ 0) :
    (X.constantZMod d).IsTorsion := by
  intro U s
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨d, Nat.pos_of_ne_zero hd, ?_⟩
  have h₀ : d • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))) = 0 := by
    ext x
    simp
  have h₁ : d • 𝟙 (X.constantZMod d) = 0 := by
    rw [← (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_id,
      ← Functor.map_nsmul, h₀, Functor.map_zero]
  have h₂ := congrArg (fun φ ↦ ((sheafToPresheaf _ _).map φ).app U) h₁
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h₂
  simpa using congrArg (fun g ↦ g.hom s) h₂

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- Blueprint `sbc-thm-cohomological-dimension-of-an-affine-curve`: Affine-curve cohomological
dimension.

Let `k` be algebraically closed, let `C` be a smooth affine curve over `k` and let `d ≥ 1`.
Then `H^q(C_ét, ℤ/d) = 0` for `q > 1`, and `H^0(C_ét, ℤ/d) = ℤ/d` when `C` is connected.

The vanishing is the case of the torsion sheaf `ℤ/d` of
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine` (blueprint
`sk-prop-cd-affine`), which does not need `d` to be prime to the characteristic; the degree
zero statement is `AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`. -/
@[stacks 03SC "(2)"]
theorem subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero
    (f : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsAffine C] {d : ℕ} (hd : d ≠ 0) :
    (∀ q, 1 < q → Subsingleton (Sheaf.H (C.constantZMod d) q)) ∧
      (ConnectedSpace C → Nonempty (Sheaf.H (C.constantZMod d) 0 ≃+ ZMod d)) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurve f :=
    { toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      krullDim_le_one := by
        simpa using topologicalKrullDim_le_of_smoothOfRelativeDimension f 1 }
  exact ⟨fun q hq ↦ IsCurve.subsingleton_sheafH_of_two_le_of_isAffine f _
    (C.isTorsion_constantZMod hd) q hq, fun _ ↦ C.nonempty_addEquiv_sheafH_zero_constantZMod d⟩

/-- **Kummer computation on an affine curve.** Let `C` be a smooth affine connected curve over an
algebraically closed field `k` and `n ≥ 1` prime to `char k`. Then

* `H⁰(C_ét, ℤ/n) ≅ ℤ/n`;
* `𝒪(C)ˣ / 𝒪(C)ˣⁿ` is finite;
* there is a short exact sequence `0 → 𝒪(C)ˣ / 𝒪(C)ˣⁿ → H¹(C_ét, ℤ/n) → Pic(C)[n] → 0`, with
  `Pic(C) = H¹(C_ét, 𝔾ₘ)`;
* `Pic(C)[n]` is finite;
* `H^q(C_ét, ℤ/n) = 0` for `q > 1`.

A primitive `n`-th root of unity identifies `ℤ/n` with `μₙ`
(`AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`), and the Kummer sequence together
with `Br(C) = 0`
(`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_connectedSpace`)
gives the sequence for `H¹` (`AlgebraicGeometry.IsCurve.sheafH_rootsOfUnitySheaf_of_subsingleton`).
The finiteness statements are `AlgebraicGeometry.IsConnectedCurve.finite_units_quotient` and
`AlgebraicGeometry.IsConnectedCurve.surjective_zsmul_pic_and_finite_torsionBy`, and the vanishing
is `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`.
(blueprint: `thm-sc-affine-cohomology`) -/
theorem IsConnectedCurve.sheafH_constantZMod_of_isAffine (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsAffine C] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n) ∧
      Finite (Additive Γ(C, ⊤)ˣ ⧸ (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) n).range) ∧
      (∃ (α : Additive Γ(C, ⊤)ˣ →+ Sheaf.H (C.constantZMod n) 1)
        (β : Sheaf.H (C.constantZMod n) 1 →+ C.CohomologicalPicardGroup),
        α.ker = (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) (n : ℤ)).range ∧
          Function.Exact α β ∧ β.range = AddSubgroup.torsionBy C.CohomologicalPicardGroup n) ∧
      Finite (AddSubgroup.torsionBy C.CohomologicalPicardGroup n) ∧
      ∀ q, 1 < q → Subsingleton (Sheaf.H (C.constantZMod n) q) := by
  have := IsConnectedCurve.connectedSpace' f
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := ⟨hn0⟩
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
  have e := ((Sheaf.functorH _ 1).mapIso
    (C.constantZModIsoRootsOfUnitySheaf n f hζ)).addCommGroupIsoToAddEquiv
  have hBr := IsCurve.subsingleton_cohomologicalBrauerGroup_of_connectedSpace f
  obtain ⟨⟨α, β, hα, hαβ, hβ⟩, -⟩ := IsCurve.sheafH_rootsOfUnitySheaf_of_subsingleton f n hn hBr
  obtain ⟨ePic⟩ := C.nonempty_addEquiv_cohomologicalPicardGroup
  have hfin := (surjective_zsmul_pic_and_finite_torsionBy f hn).2
  refine ⟨C.nonempty_addEquiv_sheafH_zero_constantZMod n,
    finite_units_quotient f n (Nat.pos_of_ne_zero hn0),
    ⟨e.symm.toAddMonoidHom.comp α, β.comp e.toAddMonoidHom, ?_, ?_, ?_⟩, ?_,
    fun q hq ↦ IsCurve.subsingleton_sheafH_of_two_le_of_isAffine f _
      (C.isTorsion_constantZMod hn0) q hq⟩
  · rw [← hα]
    ext x
    exact e.symm.map_eq_zero_iff
  · intro y
    refine (hαβ (e y)).trans ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩⟩
    · change e.symm (α x) = y
      rw [hx]
      exact e.symm_apply_apply y
    · change e.symm (α x) = y at hx
      rw [← hx]
      exact (e.apply_symm_apply _).symm
  · rw [← hβ]
    ext y
    refine ⟨fun ⟨x, hx⟩ ↦ ⟨e x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨e.symm x, ?_⟩⟩
    change β (e (e.symm x)) = y
    rw [e.apply_symm_apply x, hx]
  · refine Finite.of_injective (β := AddSubgroup.torsionBy (Additive C.Pic) n)
      (fun x ↦ ⟨ePic.symm x, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩) fun x y hxy ↦ ?_
    · rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero]
    · exact Subtype.ext (ePic.symm.injective (congrArg Subtype.val hxy))

end AlgebraicGeometry
