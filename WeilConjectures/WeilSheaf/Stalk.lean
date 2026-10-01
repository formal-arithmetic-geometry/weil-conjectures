/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.PointCount
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Stalks, trace functions and weights of Weil sheaves

Let `F` be a Weil sheaf on a `k₀`-scheme `X`: a constructible étale sheaf on the geometric
fiber `X̄ = X ×_{k₀} k̄` with an isomorphism `φ : Fr^* F ≅ F`, where `Fr = 𝟙 × σ` is the
geometric Galois Frobenius of `X̄` and `σ` the automorphism of `Spec k̄` induced by the
geometric Frobenius of `k̄`. This file constructs the geometric stalks of `F` with their local
Frobenius, the trace function, the support and the global sections of `F`, and phrases
punctual purity, upper weight bounds and reality on the stalks.

## The local Frobenius

For a geometric point `s : Spec k̄ ⟶ X̄`, the isomorphism `φ` induces
`F_{s ≫ Fr} ≅ (Fr^* F)_s ≅ F_s`, and iterating, `F_{s ≫ Frᵐ} ≅ F_s`. The point `s ≫ Fr` is not
`s` itself: its second component `Spec k̄ ⟶ Spec k̄` is `σ` instead of the identity. If `s`
lies over a point with values in a field with `qᵐ` elements, then `s ≫ Frᵐ = σᵐ ≫ s`, and
the reparametrisation `σᵐ ≫ s` of `s` by an automorphism of `Spec k̄` is an isomorphic point
of the étale site (`AlgebraicGeometry.Scheme.uliftPointSmallEtaleIsoOfIso`). The composite

`F_s ≅ F_{σᵐ ≫ s} = F_{s ≫ Frᵐ} ≅ F_s`

is the local Frobenius `F_x^{(m)}` on the stalk, `AlgebraicGeometry.WeilSheaf.stalkAt`.

At a closed point `x` of `X` with residue field `κ(x)` of degree `e_x` over `k₀`, the
geometric point is `Spec k̄ ⟶ Spec κ(x) ⟶ X` for a `k₀`-embedding `κ(x) ↪ k̄`, chosen by
`IsAlgClosed.lift`, lifted to `X̄`; at an `𝔽_{qⁿ}`-rational point the same construction is
made with an embedding `𝔽_{qⁿ} ↪ k̄`. The choice of embedding does not change the
isomorphism class of the stalk with its Frobenius, since two embeddings differ by a power of
the Frobenius of `k̄`, which `φ` identifies.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.stalkAt`: the stalk at a geometric point fixed by `Frᵐ`, up to
  reparametrisation, with its Frobenius.
- `AlgebraicGeometry.WeilSheaf.stalk`: the geometric stalk at a closed point with its local
  geometric Frobenius `Fₓ`.
- `AlgebraicGeometry.WeilSheaf.support`: the points of `X` under a geometric point with
  nonzero stalk.
- `AlgebraicGeometry.WeilSheaf.traceFunction`: the trace function `t_{F,n}`.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`,
  `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost` and `AlgebraicGeometry.WeilSheaf.IsReal`: the
  weight conditions and the reality condition.
- `AlgebraicGeometry.WeilSheaf.globalSections`: the global sections `Γ(X̄, F)` with the
  Frobenius induced by `φ`.

## Implementation notes

The stalks are those of the universe-lifted points `(pointSmallEtale s).ulift`, which is the
form in which the coefficients `AlgebraicGeometry.WeilCoefficients` take stalks. A module over
`ULift ℚ̄_ℓ` is made a `ℚ̄_ℓ`-module by restriction of scalars
(`AlgebraicGeometry.WeilCoefficients.Carrier`).

The finite-dimensionality of stalks and global sections is recorded as theorems with `sorry`
proofs. With the present discrete coefficients every Weil sheaf is zero (see
`WeilConjectures.WeilSheaf.Category`), so the finite-dimensionality statements are true but
degenerate.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

section SpecFrobenius

variable {k : Type u} [Field k] [Finite k]

/-- Precomposing `m` times with `σ` is precomposing with `Spec` of the `m`-th power of the
geometric Frobenius of `k̄`. -/
theorem iterate_specGeometricFrobenius_hom_comp {Y : Scheme.{u}} (m : ℕ)
    (t : Spec (.of (AlgebraicClosure k)) ⟶ Y) :
    letI := Fintype.ofFinite k
    ((specGeometricFrobenius k).hom ≫ ·)^[m] t =
      Spec.map (CommRingCat.ofHom
        ((FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)) ^ m :
          Gal(AlgebraicClosure k/k)).toRingEquiv.toRingHom) ≫ t := by
  let := Fintype.ofFinite k
  induction m generalizing t with
  | zero =>
    rw [pow_zero, Function.iterate_zero_apply]
    change _ = Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ t
    simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, specGeometricFrobenius_hom, ← Category.assoc,
      ← Spec.map_comp, pow_succ]
    rfl

/-- Postcomposing `m` times with `σ` is postcomposing with `Spec` of the `m`-th power of the
geometric Frobenius of `k̄`. -/
theorem comp_iterate_specGeometricFrobenius_hom {Y : Scheme.{u}} (m : ℕ)
    (t : Y ⟶ Spec (.of (AlgebraicClosure k))) :
    letI := Fintype.ofFinite k
    (· ≫ (specGeometricFrobenius k).hom)^[m] t =
      t ≫ Spec.map (CommRingCat.ofHom
        ((FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)) ^ m :
          Gal(AlgebraicClosure k/k)).toRingEquiv.toRingHom) := by
  let := Fintype.ofFinite k
  induction m generalizing t with
  | zero =>
    rw [pow_zero, Function.iterate_zero_apply]
    change _ = t ≫ Spec.map (CommRingCat.ofHom (RingHom.id _))
    simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, specGeometricFrobenius_hom, Category.assoc,
      ← Spec.map_comp, pow_succ']
    rfl

/-- The `m`-th power of the geometric Frobenius of `k̄` fixes the image of any embedding of a
field with `qᵐ` elements. -/
theorem geometricFrobenius_pow_comp_eq {K : Type u} [Field K] [Finite K] (m : ℕ)
    (hK : Nat.card K = Nat.card k ^ m) (ι : K →+* AlgebraicClosure k) :
    letI := Fintype.ofFinite k
    (((FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)) ^ m :
      Gal(AlgebraicClosure k/k)).toRingEquiv.toRingHom).comp ι = ι := by
  let := Fintype.ofFinite k
  let := Fintype.ofFinite K
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply,
    FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow]
  change ((FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m)⁻¹) (ι a) = ι a
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  change ι a = ι a ^ (Fintype.card k ^ m)
  rw [← map_pow]
  congr 1
  rw [← Fintype.card_eq_nat_card, ← Fintype.card_eq_nat_card] at hK
  rw [← hK, FiniteField.pow_card]

end SpecFrobenius

namespace Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The geometric point `Spec k̄ ⟶ X̄ = X ×_k k̄` of the geometric fiber lying over a point
`g : Spec K ⟶ X` of `X` with values in an algebraic extension `K` of `k`: the point
`Spec k̄ ⟶ Spec K ⟶ X` for a `k`-embedding `K ↪ k̄` chosen by `IsAlgClosed.lift`, together
with the identity of `Spec k̄`. -/
noncomputable def geometricFiberPoint {K : Type u} [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] (g : Spec (.of K) ⟶ X)
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber :=
  pullback.lift (Spec.map (CommRingCat.ofHom
      (IsAlgClosed.lift (R := k) (S := K) (M := AlgebraicClosure k)).toRingHom) ≫ g) (𝟙 _) (by
    rw [Category.assoc, hg, ← Spec.map_comp]
    simp only [Scheme.specAlgebraicClosure, Over.mk_hom, Over.mk_left, Category.id_comp]
    congr 1
    ext a
    simp)

/-- The geometric point of the geometric fiber over a point `x` of `X` with finite residue
field `κ(x)` (a closed point, for `X` of finite type over a finite field): the geometric point
`AlgebraicGeometry.Scheme.Hom.geometricFiberPoint` over `Spec κ(x) ⟶ X`, for the `k`-algebra
structure of `κ(x)` given by the structure morphism. -/
noncomputable def geometricFiberPointOfFinitePoint (x : X.finitePoints) :
    Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber :=
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  have : Algebra.IsAlgebraic k (X.residueField x.1) := inferInstance
  f.geometricFiberPoint (K := X.residueField x.1) (X.fromSpecResidueField x.1)
    (f.specMap_residueFieldAlgebraMap x.1).symm

variable [Finite k]

/-- The geometric Galois Frobenius commutes with the projection to `X`. -/
theorem iterate_geometricGaloisFrobenius_comp_geometricFiberProj (m : ℕ)
    (t : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber) :
    (· ≫ f.geometricGaloisFrobenius.hom)^[m] t ≫ f.geometricFiberProj =
      t ≫ f.geometricFiberProj := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih, Category.assoc,
      geometricGaloisFrobenius_hom_comp_geometricFiberProj]

/-- The geometric Galois Frobenius acts on the second component of a geometric point by `σ`. -/
theorem iterate_geometricGaloisFrobenius_comp_geometricFiberToAlgebraicClosure (m : ℕ)
    (t : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber) :
    (· ≫ f.geometricGaloisFrobenius.hom)^[m] t ≫ f.geometricFiberToAlgebraicClosure =
      (· ≫ (specGeometricFrobenius k).hom)^[m] (t ≫ f.geometricFiberToAlgebraicClosure) := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, Category.assoc,
      geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure, Category.assoc]

omit [Finite k] in
@[reassoc]
theorem geometricFiberPoint_comp_geometricFiberProj {K : Type u} [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] (g : Spec (.of K) ⟶ X)
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    f.geometricFiberPoint g hg ≫ f.geometricFiberProj = Spec.map (CommRingCat.ofHom
      (IsAlgClosed.lift (R := k) (S := K) (M := AlgebraicClosure k)).toRingHom) ≫ g :=
  pullback.lift_fst _ _ _

omit [Finite k] in
@[reassoc]
theorem geometricFiberPoint_comp_geometricFiberToAlgebraicClosure {K : Type u} [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] (g : Spec (.of K) ⟶ X)
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    f.geometricFiberPoint g hg ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- A geometric point over a point with values in a field with `qᵐ` elements is fixed by `Frᵐ`
up to reparametrisation: `s ≫ Frᵐ = σᵐ ≫ s`. -/
theorem iterate_geometricGaloisFrobenius_geometricFiberPoint {K : Type u} [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [Finite K] (m : ℕ) (hK : Nat.card K = Nat.card k ^ m)
    (g : Spec (.of K) ⟶ X) (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    (· ≫ f.geometricGaloisFrobenius.hom)^[m] (f.geometricFiberPoint g hg) =
      ((specGeometricFrobenius k).hom ≫ ·)^[m] (f.geometricFiberPoint g hg) := by
  rw [iterate_specGeometricFrobenius_hom_comp]
  apply pullback.hom_ext
  · change _ ≫ f.geometricFiberProj = _ ≫ f.geometricFiberProj
    rw [iterate_geometricGaloisFrobenius_comp_geometricFiberProj, Category.assoc,
      geometricFiberPoint_comp_geometricFiberProj, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, geometricFrobenius_pow_comp_eq m hK]
  · change _ ≫ f.geometricFiberToAlgebraicClosure = _ ≫ f.geometricFiberToAlgebraicClosure
    rw [iterate_geometricGaloisFrobenius_comp_geometricFiberToAlgebraicClosure,
      comp_iterate_specGeometricFrobenius_hom]
    simp only [Category.assoc,
      f.geometricFiberPoint_comp_geometricFiberToAlgebraicClosure g hg, Category.id_comp,
      Category.comp_id]

end Scheme.Hom

variable {l : ℕ} [Fact l.Prime]

/-- The underlying `ℚ̄_ℓ`-vector space of a module over `ULift ℚ̄_ℓ`, by restriction of scalars
along `ℚ̄_ℓ ≃ ULift ℚ̄_ℓ`. -/
def WeilCoefficients.Carrier (M : WeilCoefficients.{u} l) : Type (u + 1) :=
  M

namespace WeilCoefficients

noncomputable instance (M : WeilCoefficients.{u} l) : AddCommGroup (Carrier M) :=
  inferInstanceAs (AddCommGroup M)

noncomputable instance (M : WeilCoefficients.{u} l) : Module (PadicAlgCl l) (Carrier M) :=
  Module.compHom M (ULift.ringEquiv (R := PadicAlgCl l)).symm.toRingHom

/-- An isomorphism of modules over `ULift ℚ̄_ℓ` as a `ℚ̄_ℓ`-linear isomorphism of the
underlying `ℚ̄_ℓ`-vector spaces. -/
noncomputable def linearEquivOfIso {M N : WeilCoefficients.{u} l} (e : M ≅ N) :
    Carrier M ≃ₗ[PadicAlgCl l] Carrier N where
  toFun := e.hom
  invFun := e.inv
  map_add' := map_add e.hom.hom
  map_smul' c x := e.hom.hom.map_smul (ULift.up c) x
  left_inv := e.hom_inv_id_apply
  right_inv := e.inv_hom_id_apply

end WeilCoefficients

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

section GeometricStalk

variable (F : WeilSheaf k₀ l X)

/-- The stalk `F_s` of the underlying étale sheaf of a Weil sheaf at a geometric point
`s : Spec k̄ ⟶ X̄`. -/
noncomputable def stalkObj
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    WeilCoefficients.{u} l :=
  ((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj F.obj.carrier

/-- The isomorphism `F_{s ≫ Fr} ≅ (Fr^* F)_s ≅ F_s` induced by the Weil structure
`φ : Fr^* F ≅ F`. -/
noncomputable def stalkObjFrobeniusIso
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    F.stalkObj (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom) ≅
      F.stalkObj s :=
  (Etale.upperStarCompUliftSheafFiberIso _ _ s).symm.app F.obj.carrier ≪≫
    ((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber.mapIso F.obj.str

/-- The iterated isomorphism `F_{s ≫ Frᵐ} ≅ F_s`, composed of the isomorphisms
`AlgebraicGeometry.WeilSheaf.stalkObjFrobeniusIso` at `s, s ≫ Fr, …, s ≫ Frᵐ⁻¹`. -/
noncomputable def stalkObjFrobeniusIterateIso :
    ∀ (m : ℕ) (s : Spec (.of (AlgebraicClosure k₀)) ⟶
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      F.stalkObj ((· ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^[m] s) ≅
        F.stalkObj s
  | 0, _ => Iso.refl _
  | m + 1, s => stalkObjFrobeniusIterateIso m _ ≪≫ F.stalkObjFrobeniusIso s

/-- The isomorphism `F_{σ ≫ s} ≅ F_s` of the stalks at a geometric point `s` and at its
reparametrisation by the Frobenius automorphism `σ` of `Spec k̄`. -/
noncomputable def stalkObjSpecFrobeniusIso
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    F.stalkObj ((specGeometricFrobenius k₀).hom ≫ s) ≅ F.stalkObj s :=
  (GrothendieckTopology.Point.sheafFiberIso
    (Scheme.uliftPointSmallEtaleIsoOfIso (specGeometricFrobenius k₀) s)).app _

/-- The iterated isomorphism `F_{σᵐ ≫ s} ≅ F_s`. -/
noncomputable def stalkObjSpecFrobeniusIterateIso :
    ∀ (m : ℕ) (s : Spec (.of (AlgebraicClosure k₀)) ⟶
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      F.stalkObj (((specGeometricFrobenius k₀).hom ≫ ·)^[m] s) ≅ F.stalkObj s
  | 0, _ => Iso.refl _
  | m + 1, s => stalkObjSpecFrobeniusIterateIso m _ ≪≫ F.stalkObjSpecFrobeniusIso s

/-- The stalks of a Weil sheaf are finite-dimensional. -/
theorem finiteDimensional_stalkObj
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    FiniteDimensional (PadicAlgCl l) (WeilCoefficients.Carrier (F.stalkObj s)) := by
  sorry

/-- The stalk `F_s` of a Weil sheaf at a geometric point `s` with `s ≫ Frᵐ = σᵐ ≫ s`, with its
Frobenius `F_s ≅ F_{σᵐ ≫ s} = F_{s ≫ Frᵐ} ≅ F_s`. For `s` over a point with values in a field
with `qᵐ` elements this is the local Frobenius relative to that field. -/
noncomputable def stalkAt
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : (· ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^[m] s =
      ((specGeometricFrobenius k₀).hom ≫ ·)^[m] s) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  have := F.finiteDimensional_stalkObj s
  { carrier := WeilCoefficients.Carrier (F.stalkObj s)
    frobenius := WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusIterateIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusIterateIso m s) }

end GeometricStalk

/-- The geometric point over a closed point `x` is fixed by `Fr^{e_x}` up to reparametrisation,
`e_x = [κ(x) : k₀]`: both have the same image in `X`, since `σ^{e_x}` fixes the image of
`κ(x)` in `k̄`, and the same second component `σ^{e_x}`. -/
theorem geometricGaloisFrobenius_iterate_geometricFiberPointOfFinitePoint (x : X.finitePoints) :
    (· ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^[
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1]
        ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) =
      ((specGeometricFrobenius k₀).hom ≫ ·)^[(X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1]
        ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) := by
  let := ((X ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k₀ (X.residueField x.1) := Module.Finite.of_finite
  exact Scheme.Hom.iterate_geometricGaloisFrobenius_geometricFiberPoint _ _
    (Module.natCard_eq_pow_finrank (K := k₀) (V := X.residueField x.1)) _
    ((X ↘ Spec (CommRingCat.of k₀)).specMap_residueFieldAlgebraMap x.1).symm

/-- The geometric point over an `𝔽_{qⁿ}`-rational point is fixed by `Frⁿ` up to
reparametrisation. -/
theorem geometricGaloisFrobenius_iterate_geometricFiberPoint (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (· ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^[n]
        ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint x.1 x.2) =
      ((specGeometricFrobenius k₀).hom ≫ ·)^[n]
        ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint x.1 x.2) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rfl
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  exact Scheme.Hom.iterate_geometricGaloisFrobenius_geometricFiberPoint _ _
    (FiniteField.nat_card_galoisExtension k₀ n hn) _ _

variable (F : WeilSheaf k₀ l X)

-- TODO(unify): sk-d-real-weil
/-- The geometric stalk `F_x̄` of `F` at a closed point `x`, with its local geometric Frobenius
`Fₓ = F_x^{(e_x)}`, `e_x = [κ(x) : k₀]`. The stalk is taken at the geometric point
`AlgebraicGeometry.Scheme.Hom.geometricFiberPointOfFinitePoint`, for a chosen embedding
`κ(x) ↪ k̄`. -/
noncomputable def stalk (x : X.finitePoints) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  F.stalkAt _ _ (geometricGaloisFrobenius_iterate_geometricFiberPointOfFinitePoint x)

-- TODO(unify): sk-d-real-weil
/-- The support of a Weil sheaf: the points of `X` under a geometric point of `X̄` at which the
stalk is nonzero. -/
def support : Set X :=
  {x | ∃ s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base default = x ∧
      Nontrivial (WeilCoefficients.Carrier (F.stalkObj s))}

-- TODO(unify): sk-def-trace
/-- The trace function `t_{F,n}` of a Weil sheaf: the trace `Tr(F_x^{(n)} | F_x̄)` of the
Frobenius relative to `𝔽_{qⁿ}` on the stalk at an `𝔽_{qⁿ}`-rational point `x`. -/
noncomputable def traceFunction (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    PadicAlgCl l :=
  LinearMap.trace (PadicAlgCl l) _
    (F.stalkAt _ n (geometricGaloisFrobenius_iterate_geometricFiberPoint n x)).frobeniusEnd

/-- `F` is punctually `ι`-pure of weight `w`: at every closed point `x`, every eigenvalue `α`
of the local Frobenius `Fₓ` satisfies `|ι α| = q_x ^ (w / 2)`, with `q_x` the residue
cardinality at `x`. -/
def IsPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X.finitePoints,
    (F.stalk x).IsPureOfWeight ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w

/-- `F` has weights at most `w`: at every closed point `x`, every eigenvalue `α` of the local
Frobenius `Fₓ` satisfies `|ι α| ≤ q_x ^ (w / 2)`. -/
def HasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X.finitePoints,
    (F.stalk x).HasWeightsAtMost ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w

/-- A punctually pure sheaf has weights at most its weight. -/
theorem IsPunctuallyPureOfWeight.hasWeightsAtMost {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) :
    F.HasWeightsAtMost ι w :=
  fun x ↦ (h x).hasWeightsAtMost

-- TODO(unify): sk-d-real-weights
/-- `F` is `ι`-*real* if the realization under `ι` of the local Frobenius characteristic
polynomial `P_x(F, T) = det(1 - T Fₓ | F_x̄)` has real coefficients at every closed point `x`;
equivalently, if every complex local eigenvalue multiset is stable under complex
conjugation. -/
def IsReal (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : Prop :=
  ∀ (x : X.finitePoints) (n : ℕ),
    (starRingEnd ℂ) (ι ((F.stalk x).frobeniusEnd.charpolyRev.coeff n)) =
      ι ((F.stalk x).frobeniusEnd.charpolyRev.coeff n)

section GlobalSections

/-- The isomorphism `Γ(X̄, Fr^* F) ≅ Γ(X̄, F)`: sections over `X̄` of `Fr^* F` are sections over
`Fr^{-1} X̄ = X̄` of `Fr_* Fr^* F`, and the unit `F ⟶ Fr_* Fr^* F` is an isomorphism because
`Fr^*` is an equivalence, `Fr` being an isomorphism. -/
noncomputable def globalSectionsFrobeniusIso :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((frobeniusPullback k₀ l X).obj F.obj.carrier) ≅
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier :=
  have := Etale.isEquivalence_upperStar (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
  (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).app _ ≪≫
    ((frobeniusPullback k₀ l X).obj F.obj.carrier).obj.mapIso
      (PreservesTerminal.iso
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom.Etale).op ≪≫
    ((sheafSections _ _).obj (op (⊤_ _))).mapIso
      (asIso ((Etale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).unit.app
          F.obj.carrier)).symm ≪≫
    ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).app _).symm

/-- The global sections of a Weil sheaf are finite-dimensional. -/
theorem finiteDimensional_globalSections :
    FiniteDimensional (PadicAlgCl l)
      (WeilCoefficients.Carrier ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier)) := by
  sorry

/-- The global sections `Γ(X̄, F)` of a Weil sheaf, with the Frobenius
`Γ(X̄, F) ≅ Γ(X̄, Fr^* F) ⟶ Γ(X̄, F)` induced by the Weil structure `φ : Fr^* F ≅ F`. -/
noncomputable def globalSections : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  have := F.finiteDimensional_globalSections
  { carrier := WeilCoefficients.Carrier ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier)
    frobenius := WeilCoefficients.linearEquivOfIso
      (F.globalSectionsFrobeniusIso.symm ≪≫ (Sheaf.Γ _ _).mapIso F.obj.str) }

end GlobalSections

end WeilSheaf

end AlgebraicGeometry
