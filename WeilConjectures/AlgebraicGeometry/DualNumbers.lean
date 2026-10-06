/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.RingTheory.Nilpotent.Basic

/-!
# Dual-number thickenings of schemes

For a scheme `X`, the *dual-number thickening* `X[ε]` is the scheme with the same underlying
space as `X` and structure sheaf `𝒪_X[ε] = 𝒪_X ⊕ ε𝒪_X`, `ε² = 0`: the relative spectrum of the
sheaf of algebras `𝒪_X[ε]`, equivalently the fibre product `X ×_ℤ Spec ℤ[ε]`. Its sections over an
open `U` are, by definition, the dual numbers `Γ(X, U)[ε]` over `Γ(X, U)`. It comes with the
projection `p : X[ε] ⟶ X` (inclusion of constants), the closed immersion `i : X ⟶ X[ε]` (`ε ↦ 0`)
with `i ≫ p = 𝟙`, functoriality `f[ε] : X[ε] ⟶ Y[ε]` for `f : X ⟶ Y`, and the two-parameter
thickening `X[ε][δ]` with the map `X[ε][δ] ⟶ X[η]`, `η ↦ εδ`, which records the mixed infinitesimal
term.

Points of a scheme `G` with values in `S[ε]` reducing to a given point along `i` are the tangent
vectors of `G` at that point; for a group scheme this is the Lie algebra, see
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie`. For `S = Spec k`, the canonical morphism
`(Spec k)[ε] ⟶ Spec k[ε]` is an isomorphism, identifying these points with the points of `G` with
values in the ring `k[ε]`.

## Main definitions

- `DualNumber.mapRingHom`: functoriality of dual numbers in ring homomorphisms, and the functor
  `CommRingCat.dualNumber` with the natural transformations `dualNumberInl` (constants),
  `dualNumberFst` (`ε ↦ 0`) and `dualNumberMul` (`η ↦ εδ`).
- `AlgebraicGeometry.Scheme.dualNumbers`: the thickening `X[ε]`.
- `AlgebraicGeometry.Scheme.dualNumbersProj`, `AlgebraicGeometry.Scheme.dualNumbersι`: the
  projection `X[ε] ⟶ X` and the closed immersion `X ⟶ X[ε]`.
- `AlgebraicGeometry.Scheme.Hom.dualNumbers`: the morphism `f[ε] : X[ε] ⟶ Y[ε]`.
- `AlgebraicGeometry.Scheme.dualNumbersMul`: the map `X[ε][δ] ⟶ X[η]`, `η ↦ εδ`.
- `AlgebraicGeometry.Scheme.dualNumbersToSpec`: the isomorphism `(Spec R)[ε] ⟶ Spec R[ε]`.

## Implementation notes

The sheaf condition holds because `R ↦ R[ε]` preserves limits: its underlying type is `R × R`.
The stalk of `𝒪_X[ε]` at `x` maps onto `𝒪_{X,x}` (`ε ↦ 0`) with a section and a square-zero
kernel, so it is local and the stalk maps of the morphisms constructed here are local. For an
affine scheme `Z`, the stalks of `Z[ε]` are localizations of `Γ(Z)[ε]` and
`Spec Γ(Z)[ε] → Spec Γ(Z)` is a homeomorphism, so the canonical morphism `Z[ε] ⟶ Spec Γ(Z[ε])`
is an isomorphism. This gives the local affineness of `X[ε]` and `isIso_dualNumbersToSpec`.

## Blueprint

- `sk-d-tangent`: points with values in the dual numbers as tangent vectors.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace TrivSqZeroExt

/-! ### Dual numbers as a functor on commutative rings -/

namespace DualNumber

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A ring homomorphism `f : R → S` induces `R[ε] → S[ε]`, `a + εb ↦ f(a) + εf(b)`. -/
def mapRingHom (f : R →+* S) : R[ε] →+* S[ε] where
  toFun x := inl (f x.fst) + inr (f x.snd)
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

@[simp]
theorem fst_mapRingHom (f : R →+* S) (x : R[ε]) : (mapRingHom f x).fst = f x.fst := by
  simp [mapRingHom]

@[simp]
theorem snd_mapRingHom (f : R →+* S) (x : R[ε]) : (mapRingHom f x).snd = f x.snd := by
  simp [mapRingHom]

theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[ε] := by
  sorry

theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  sorry

/-- The ring homomorphism `R[η] → R[ε][δ]`, `a + ηb ↦ a + εδ b`, recording the mixed infinitesimal
term of the two-parameter dual numbers `R[ε][δ] = R[ε, δ]/(ε², δ²)`. -/
def mulRingHom : R[ε] →+* (R[ε])[ε] where
  toFun x := inl (inl x.fst) + inr (inr x.snd)
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

end DualNumber

namespace CommRingCat

/-- The dual numbers `R ↦ R[ε]` as an endofunctor of commutative rings. -/
noncomputable def dualNumber : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of (DualNumber R)
  map f := ofHom (DualNumber.mapRingHom f.hom)
  map_id _ := by
    ext1
    exact DualNumber.mapRingHom_id
  map_comp _ _ := by
    ext1
    exact DualNumber.mapRingHom_comp _ _

/-- The inclusion of constants `R → R[ε]`, naturally in `R`. -/
noncomputable def dualNumberInl : 𝟭 CommRingCat.{u} ⟶ dualNumber where
  app R := ofHom (TrivSqZeroExt.inlHom R R)
  naturality _ _ _ := by sorry

/-- The augmentation `R[ε] → R`, `ε ↦ 0`, naturally in `R`. -/
noncomputable def dualNumberFst : dualNumber ⟶ 𝟭 CommRingCat.{u} where
  app R := ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
  naturality _ _ _ := by sorry

/-- The map `R[η] → R[ε][δ]`, `η ↦ εδ`, naturally in `R`. -/
noncomputable def dualNumberMul : dualNumber ⟶ dualNumber ⋙ dualNumber where
  app R := ofHom DualNumber.mulRingHom
  naturality _ _ _ := by sorry

end CommRingCat

namespace CommRingCat

open Limits

/-- `R[ε]` as a type is `R × R`, written as maps out of a two-point type. -/
def dualNumberEquivHom (R : Type u) [CommRing R] : DualNumber R ≃ (ULift.{u} Bool ⟶ R) where
  toFun x := TypeCat.ofHom fun b : ULift.{u} Bool ↦ if b.down then x.snd else x.fst
  invFun g := (g ⟨false⟩, g ⟨true⟩)
  left_inv x := rfl
  right_inv g := by ext ⟨b⟩; cases b <;> simp

/-- The underlying type of `R[ε]` is `R × R`, naturally in `R`. -/
noncomputable def dualNumberCompForgetIso :
    dualNumber.{u} ⋙ forget CommRingCat ≅
      forget CommRingCat ⋙ CategoryTheory.coyoneda.obj (.op (ULift.{u} Bool : Type u)) :=
  NatIso.ofComponents (fun R ↦ (dualNumberEquivHom R).toIso)
    (fun f ↦ by
      refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
      change dualNumberEquivHom _ (DualNumber.mapRingHom f.hom x) =
        dualNumberEquivHom _ x ≫ TypeCat.ofHom f.hom
      ext ⟨b⟩
      cases b <;> simp [dualNumberEquivHom])

/-- `R ↦ R[ε]` preserves limits. -/
instance : PreservesLimitsOfSize.{u, u} dualNumber.{u} := by
  have : PreservesLimitsOfSize.{u, u} (dualNumber.{u} ⋙ forget CommRingCat) :=
    preservesLimits_of_natIso dualNumberCompForgetIso.symm
  have : ReflectsLimitsOfSize.{u, u} (forget CommRingCat.{u}) :=
    reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves dualNumber (forget CommRingCat)

end CommRingCat

namespace TopCat.Presheaf

variable {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u}) (x : T)

/-- The map `𝒪[ε]_x → 𝒪_x`, `ε ↦ 0`, on stalks. -/
noncomputable def dualNumberStalkFst : stalk (F ⋙ CommRingCat.dualNumber) x ⟶ F.stalk x :=
  (stalkFunctor CommRingCat x).map
    (Functor.whiskerLeft F CommRingCat.dualNumberFst ≫ F.rightUnitor.hom)

/-- The inclusion of constants `𝒪_x → 𝒪[ε]_x` on stalks. -/
noncomputable def dualNumberStalkInl : F.stalk x ⟶ stalk (F ⋙ CommRingCat.dualNumber) x :=
  (stalkFunctor CommRingCat x).map
    (F.rightUnitor.inv ≫ Functor.whiskerLeft F CommRingCat.dualNumberInl)

@[simp]
lemma dualNumberStalkFst_germ (U : Opens T) (hx : x ∈ U) (s : DualNumber (F.obj (.op U))) :
    F.dualNumberStalkFst x (germ (F ⋙ CommRingCat.dualNumber) U x hx s) = F.germ U x hx s.fst :=
  stalkFunctor_map_germ_apply (F := F ⋙ CommRingCat.dualNumber) U x hx
    (Functor.whiskerLeft F CommRingCat.dualNumberFst ≫ F.rightUnitor.hom) s

@[simp]
lemma dualNumberStalkInl_germ (U : Opens T) (hx : x ∈ U) (s : F.obj (.op U)) :
    F.dualNumberStalkInl x (F.germ U x hx s) =
      germ (F ⋙ CommRingCat.dualNumber) U x hx (TrivSqZeroExt.inl s) :=
  stalkFunctor_map_germ_apply (G := F ⋙ CommRingCat.dualNumber) U x hx
    (F.rightUnitor.inv ≫ Functor.whiskerLeft F CommRingCat.dualNumberInl) s

@[reassoc (attr := simp)]
lemma dualNumberStalkInl_fst : F.dualNumberStalkInl x ≫ F.dualNumberStalkFst x = 𝟙 _ := by
  refine stalk_hom_ext _ fun U hx ↦ ?_
  ext s
  change F.dualNumberStalkFst x (F.dualNumberStalkInl x (F.germ U x hx s)) = F.germ U x hx s
  rw [dualNumberStalkInl_germ, dualNumberStalkFst_germ]
  rfl

/-- The kernel of `𝒪[ε]_x → 𝒪_x` is square-zero. -/
lemma mul_self_eq_zero_of_dualNumberStalkFst_eq_zero
    (y : ToType (stalk (C := CommRingCat) (F ⋙ CommRingCat.dualNumber) x))
    (hy : F.dualNumberStalkFst x y = 0) :
    y * y = 0 := by
  obtain ⟨U, hx, s, rfl⟩ := exists_germ_eq (F ⋙ CommRingCat.dualNumber) y
  rw [dualNumberStalkFst_germ, ← map_zero (F.germ U x hx).hom] at hy
  obtain ⟨W, hxW, iU, iV, e⟩ := F.germ_eq x hx hx _ _ hy
  rw [map_zero] at e
  have h : DualNumber.mapRingHom (F.map iU.op).hom s * DualNumber.mapRingHom (F.map iU.op).hom s =
      0 := by
    ext <;> simp [e]
  rw [← map_mul, ← germ_res_apply (F ⋙ CommRingCat.dualNumber) iU x hxW, map_mul]
  exact (congrArg _ h).trans (map_zero _)

instance isLocalHom_dualNumberStalkFst : IsLocalHom (F.dualNumberStalkFst x).hom :=
  isLocalHom_of_rightInverse_of_mul_self_eq_zero _ (F.dualNumberStalkInl x).hom
    (fun y ↦ congr($(F.dualNumberStalkInl_fst x).hom y))
    (F.mul_self_eq_zero_of_dualNumberStalkFst_eq_zero x)

instance isLocalHom_dualNumberStalkInl : IsLocalHom (F.dualNumberStalkInl x).hom := by
  have : IsLocalHom ((F.dualNumberStalkFst x).hom.comp (F.dualNumberStalkInl x).hom) := by
    rw [← CommRingCat.hom_comp, F.dualNumberStalkInl_fst]
    exact isLocalHom_id _
  exact isLocalHom_of_comp _ (F.dualNumberStalkFst x).hom

/-- The map `𝒪[η]_x → 𝒪[ε][δ]_x`, `η ↦ εδ`, on stalks. -/
noncomputable def dualNumberStalkMul :
    stalk (F ⋙ CommRingCat.dualNumber) x ⟶
      stalk ((F ⋙ CommRingCat.dualNumber) ⋙ CommRingCat.dualNumber) x :=
  (stalkFunctor CommRingCat x).map (Functor.whiskerLeft F CommRingCat.dualNumberMul)

@[simp]
lemma dualNumberStalkMul_germ (U : Opens T) (hx : x ∈ U) (s : DualNumber (F.obj (.op U))) :
    F.dualNumberStalkMul x (germ (F ⋙ CommRingCat.dualNumber) U x hx s) =
      germ ((F ⋙ CommRingCat.dualNumber) ⋙ CommRingCat.dualNumber) U x hx
        (DualNumber.mulRingHom s) :=
  stalkFunctor_map_germ_apply (F := F ⋙ CommRingCat.dualNumber)
    (G := (F ⋙ CommRingCat.dualNumber) ⋙ CommRingCat.dualNumber) U x hx
    (Functor.whiskerLeft F CommRingCat.dualNumberMul) s

@[reassoc (attr := simp)]
lemma dualNumberStalkMul_fst_fst :
    F.dualNumberStalkMul x ≫ dualNumberStalkFst (F ⋙ CommRingCat.dualNumber) x ≫
      F.dualNumberStalkFst x = F.dualNumberStalkFst x := by
  refine stalk_hom_ext _ fun U hx ↦ ?_
  ext s
  change F.dualNumberStalkFst x (dualNumberStalkFst (F ⋙ CommRingCat.dualNumber) x
    (F.dualNumberStalkMul x (germ (F ⋙ CommRingCat.dualNumber) U x hx s))) =
      F.dualNumberStalkFst x (germ (F ⋙ CommRingCat.dualNumber) U x hx s)
  rw [dualNumberStalkMul_germ, dualNumberStalkFst_germ, dualNumberStalkFst_germ,
    dualNumberStalkFst_germ]
  congr 1
  change (TrivSqZeroExt.inl (TrivSqZeroExt.inl s.fst) +
    TrivSqZeroExt.inr (TrivSqZeroExt.inr s.snd) : DualNumber (DualNumber (F.obj _))).fst.fst =
      s.fst
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

instance isLocalHom_dualNumberStalkMul : IsLocalHom (F.dualNumberStalkMul x).hom := by
  let g := dualNumberStalkFst (F ⋙ CommRingCat.dualNumber) x ≫ F.dualNumberStalkFst x
  have : IsLocalHom (g.hom.comp (F.dualNumberStalkMul x).hom) := by
    rw [← CommRingCat.hom_comp, F.dualNumberStalkMul_fst_fst]
    infer_instance
  exact isLocalHom_of_comp _ g.hom

/-- The stalks of `𝒪[ε]` are local if those of `𝒪` are. -/
lemma isLocalRing_stalk_dualNumber [IsLocalRing (F.stalk x)] :
    IsLocalRing (stalk (C := CommRingCat) (F ⋙ CommRingCat.dualNumber) x) :=
  (F.dualNumberStalkFst x).hom.domain_isLocalRing

end TopCat.Presheaf

/-- `Spec R[ε] → Spec R`, induced by `ε ↦ 0`, is a homeomorphism. -/
lemma PrimeSpectrum.isHomeomorph_comap_dualNumberFst (R : Type*) [CommRing R] :
    IsHomeomorph (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine PrimeSpectrum.isHomeomorph_comap _ (fun y ↦ ⟨1, one_pos, inl y, by simp⟩)
    fun y hy ↦ ⟨2, ?_⟩
  have hy : y.fst = 0 := hy
  ext <;> simp [pow_two, hy]

namespace AlgebraicGeometry

section DualNumbersLRS

variable (Z : Scheme.{u}) [IsAffine Z] (x : Z)

namespace Scheme

/-- The locally ringed space underlying the dual-number thickening `X[ε]`. -/
noncomputable abbrev dualNumbersLRS (X : Scheme.{u}) : LocallyRingedSpace.{u} where
  carrier := X.carrier
  presheaf := X.presheaf ⋙ CommRingCat.dualNumber
  IsSheaf := Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.IsSheaf
  isLocalRing x := X.presheaf.isLocalRing_stalk_dualNumber x

/-- `ε ↦ 0` on the germ of a global section of `𝒪_X[ε]`. -/
lemma dualNumberStalkFst_Γgerm (X : Scheme.{u}) (x : X) (r : DualNumber Γ(X, ⊤)) :
    X.presheaf.dualNumberStalkFst x (X.dualNumbersLRS.presheaf.Γgerm x r) =
      X.presheaf.Γgerm x r.fst :=
  X.presheaf.dualNumberStalkFst_germ x ⊤ trivial r

/-- A global section `a + εb` of `𝒪_X[ε]` is invertible at `x` iff `a` is. -/
lemma isUnit_dualNumbersLRS_Γgerm_iff (X : Scheme.{u}) (x : X) (r : DualNumber Γ(X, ⊤)) :
    IsUnit (X.dualNumbersLRS.presheaf.Γgerm x r) ↔ IsUnit (X.presheaf.Γgerm x r.fst) := by
  rw [← dualNumberStalkFst_Γgerm]
  exact ⟨fun h ↦ h.map _, fun h ↦ h.of_map _⟩

/-- The point of `Spec Γ(X)[ε]` corresponding to `x` is the preimage of the point of `Spec Γ(X)`
corresponding to `x`. -/
lemma dualNumbersLRS_toΓSpecFun (X : Scheme.{u}) (x : X) :
    X.dualNumbersLRS.toΓSpecFun x =
      PrimeSpectrum.comap (TrivSqZeroExt.fstHom Γ(X, ⊤) Γ(X, ⊤) Γ(X, ⊤)).toRingHom
      (X.toLocallyRingedSpace.toΓSpecFun x) := by
  ext r
  rw [← not_iff_not, LocallyRingedSpace.notMem_prime_iff_unit_in_stalk]
  exact (isUnit_dualNumbersLRS_Γgerm_iff X x r).trans
    (LocallyRingedSpace.notMem_prime_iff_unit_in_stalk _ _ _).symm

/-- The germ of a constant global section of `𝒪_X[ε]`. -/
lemma dualNumbersLRS_Γgerm_inl (X : Scheme.{u}) (x : X) (a : Γ(X, ⊤)) :
    X.dualNumbersLRS.presheaf.Γgerm x (TrivSqZeroExt.inl a) =
      X.presheaf.dualNumberStalkInl x (X.presheaf.Γgerm x a) :=
  (X.presheaf.dualNumberStalkInl_germ x ⊤ trivial a).symm

/-- The germ of `a + εb` is `a + εb` in the stalk, with `ε` the germ of the global
section `ε`. -/
lemma dualNumbersLRS_germ_eq (X : Scheme.{u}) (x : X) (U : X.Opens) (hx : x ∈ U)
    (t : DualNumber Γ(X, U)) :
    X.dualNumbersLRS.presheaf.germ U x hx t =
      X.presheaf.dualNumberStalkInl x (X.presheaf.germ U x hx t.fst) +
        X.dualNumbersLRS.presheaf.Γgerm x (TrivSqZeroExt.inr 1) *
          X.presheaf.dualNumberStalkInl x (X.presheaf.germ U x hx t.snd) := by
  have ht : t = TrivSqZeroExt.inl t.fst + TrivSqZeroExt.inr 1 * TrivSqZeroExt.inl t.snd := by
    ext <;> simp
  have hE : X.dualNumbersLRS.presheaf.Γgerm x (TrivSqZeroExt.inr 1) =
      X.dualNumbersLRS.presheaf.germ U x hx (TrivSqZeroExt.inr 1) := by
    refine (TopCat.Presheaf.germ_res_apply (X.presheaf ⋙ CommRingCat.dualNumber)
      (homOfLE le_top) x hx (TrivSqZeroExt.inr 1 : DualNumber Γ(X, ⊤))).symm.trans ?_
    congr 1
    change DualNumber.mapRingHom _ (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1
    ext <;> simp
  rw [hE, X.presheaf.dualNumberStalkInl_germ, X.presheaf.dualNumberStalkInl_germ, ← map_mul,
    ← map_add, ← ht]

variable {Z} in
/-- For an affine scheme `Z`, the stalk of `𝒪_Z[ε]` at `x` is the localization of `Γ(Z)[ε]` at
the point of `Spec Γ(Z)[ε]` corresponding to `x`. -/
lemma isLocalization_dualNumbersLRS_stalk :
    let : Algebra (LocallyRingedSpace.Γ.obj (.op Z.dualNumbersLRS))
      (Z.dualNumbersLRS.presheaf.stalk x) := (Z.dualNumbersLRS.presheaf.Γgerm x).hom.toAlgebra
    IsLocalization (Z.dualNumbersLRS.toΓSpecFun x).asIdeal.primeCompl
      (Z.dualNumbersLRS.presheaf.stalk x) := by
  let : Algebra (LocallyRingedSpace.Γ.obj (.op Z.dualNumbersLRS))
    (Z.dualNumbersLRS.presheaf.stalk x) := (Z.dualNumbersLRS.presheaf.Γgerm x).hom.toAlgebra
  have hM (s : Γ(Z, ⊤)) : TrivSqZeroExt.inl s ∈ (Z.dualNumbersLRS.toΓSpecFun x).asIdeal.primeCompl ↔
      IsUnit (Z.presheaf.Γgerm x s) := by
    rw [Ideal.mem_primeCompl_iff, LocallyRingedSpace.notMem_prime_iff_unit_in_stalk]
    exact isUnit_dualNumbersLRS_Γgerm_iff Z x _
  refine ⟨fun s ↦ (LocallyRingedSpace.notMem_prime_iff_unit_in_stalk _ _ _).1 s.2, fun y ↦ ?_,
    fun {r₁ r₂} h ↦ ?_⟩
  · obtain ⟨U, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ y
    obtain ⟨a₁, s₁, hs₁, e₁⟩ := Z.exists_mul_Γgerm_eq x (Z.presheaf.germ U x hx t.fst)
    obtain ⟨a₂, s₂, hs₂, e₂⟩ := Z.exists_mul_Γgerm_eq x (Z.presheaf.germ U x hx t.snd)
    refine ⟨⟨TrivSqZeroExt.inl (a₁ * s₂) + TrivSqZeroExt.inr 1 * TrivSqZeroExt.inl (a₂ * s₁),
      ⟨TrivSqZeroExt.inl (s₁ * s₂), (hM _).2 (by rw [map_mul]; exact hs₁.mul hs₂)⟩⟩, ?_⟩
    change Z.dualNumbersLRS.presheaf.germ U x hx t *
        Z.dualNumbersLRS.presheaf.Γgerm x (TrivSqZeroExt.inl (s₁ * s₂)) =
      Z.dualNumbersLRS.presheaf.Γgerm x
        (TrivSqZeroExt.inl (a₁ * s₂) + TrivSqZeroExt.inr 1 * TrivSqZeroExt.inl (a₂ * s₁))
    have e₁' := congrArg (Z.presheaf.dualNumberStalkInl x) e₁
    have e₂' := congrArg (Z.presheaf.dualNumberStalkInl x) e₂
    simp only [map_mul] at e₁' e₂'
    rw [dualNumbersLRS_germ_eq, map_add, map_mul, dualNumbersLRS_Γgerm_inl,
      dualNumbersLRS_Γgerm_inl, dualNumbersLRS_Γgerm_inl]
    simp only [map_mul]
    linear_combination (Z.presheaf.dualNumberStalkInl x (Z.presheaf.Γgerm x s₂)) * e₁' +
      Z.dualNumbersLRS.presheaf.Γgerm x (TrivSqZeroExt.inr 1) *
        Z.presheaf.dualNumberStalkInl x (Z.presheaf.Γgerm x s₁) * e₂'
  · obtain ⟨W, hxW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (Z.presheaf ⋙ CommRingCat.dualNumber)
      (U := ⊤) (V := ⊤) x trivial trivial r₁ r₂ h
    have hU : iU = iV := Subsingleton.elim _ _
    subst hU
    have hfst : Z.presheaf.Γgerm x (r₁.fst - r₂.fst) = 0 := by
      have e' := congr(TrivSqZeroExt.fst $e)
      change TrivSqZeroExt.fst (DualNumber.mapRingHom (Z.presheaf.map iU.op).hom r₁) =
        TrivSqZeroExt.fst (DualNumber.mapRingHom (Z.presheaf.map iU.op).hom r₂) at e'
      rw [DualNumber.fst_mapRingHom, DualNumber.fst_mapRingHom] at e'
      rw [map_sub, sub_eq_zero]
      exact (Z.presheaf.Γgerm_res_apply (i := iU) x hxW _).symm.trans
        ((congrArg (Z.presheaf.germ W x hxW) e').trans
          (Z.presheaf.Γgerm_res_apply (i := iU) x hxW _))
    have hsnd : Z.presheaf.Γgerm x (r₁.snd - r₂.snd) = 0 := by
      have e' := congr(TrivSqZeroExt.snd $e)
      change TrivSqZeroExt.snd (DualNumber.mapRingHom (Z.presheaf.map iU.op).hom r₁) =
        TrivSqZeroExt.snd (DualNumber.mapRingHom (Z.presheaf.map iU.op).hom r₂) at e'
      rw [DualNumber.snd_mapRingHom, DualNumber.snd_mapRingHom] at e'
      rw [map_sub, sub_eq_zero]
      exact (Z.presheaf.Γgerm_res_apply (i := iU) x hxW _).symm.trans
        ((congrArg (Z.presheaf.germ W x hxW) e').trans
          (Z.presheaf.Γgerm_res_apply (i := iU) x hxW _))
    obtain ⟨s₁, hs₁, e₁⟩ := Z.exists_mul_eq_zero_of_Γgerm_eq_zero x _ hfst
    obtain ⟨s₂, hs₂, e₂⟩ := Z.exists_mul_eq_zero_of_Γgerm_eq_zero x _ hsnd
    refine ⟨⟨TrivSqZeroExt.inl (s₁ * s₂), (hM _).2 (by rw [map_mul]; exact hs₁.mul hs₂)⟩, ?_⟩
    change TrivSqZeroExt.inl (s₁ * s₂) * id (α := DualNumber Γ(Z, ⊤)) r₁ =
      TrivSqZeroExt.inl (s₁ * s₂) * id (α := DualNumber Γ(Z, ⊤)) r₂
    refine TrivSqZeroExt.ext (R := Γ(Z, ⊤)) (M := Γ(Z, ⊤)) ?_ ?_
    · rw [id, id, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
      linear_combination s₂ * e₁
    · rw [id, id, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_mul]
      simp
      linear_combination s₁ * e₂

/-- For an affine scheme `Z`, the stalk maps of `Z[ε] ⟶ Spec Γ(Z[ε])` are isomorphisms. -/
instance isIso_dualNumbersLRS_toΓSpec_stalkMap :
    IsIso (Z.dualNumbersLRS.toΓSpec.stalkMap x) := by
  let Y := Z.dualNumbersLRS
  let p := Y.toΓSpecFun x
  let : Algebra (LocallyRingedSpace.Γ.obj (.op Y)) (Y.presheaf.stalk x) :=
    (Y.presheaf.Γgerm x).hom.toAlgebra
  have : IsLocalization p.asIdeal.primeCompl (Y.presheaf.stalk x) :=
    isLocalization_dualNumbersLRS_stalk (Z := Z) x
  let e := IsLocalization.algEquiv p.asIdeal.primeCompl
    ((Spec.structureSheaf (LocallyRingedSpace.Γ.obj (.op Y))).presheaf.stalk p) (Y.presheaf.stalk x)
  have he : Y.toΓSpec.stalkMap x = e.toRingEquiv.toCommRingCatIso.hom := by
    ext1
    refine IsLocalization.ringHom_ext p.asIdeal.primeCompl
      (S := (Spec.structureSheaf (LocallyRingedSpace.Γ.obj (.op Y))).presheaf.stalk p) ?_
    ext r
    have := congr($(Y.toStalk_stalkMap_toΓSpec x).hom r)
    exact this.trans (e.commutes r).symm
  rw [he]
  infer_instance

/-- For an affine scheme `Z`, the map `Z[ε] ⟶ Spec Γ(Z[ε])` is a homeomorphism. -/
lemma isHomeomorph_dualNumbersLRS_toΓSpec_base :
    IsHomeomorph Z.dualNumbersLRS.toΓSpec.base := by
  have hZ : IsHomeomorph Z.toSpecΓ.base := (TopCat.isIso_iff_isHomeomorph _).mp inferInstance
  have : ⇑Z.dualNumbersLRS.toΓSpec.base =
      PrimeSpectrum.comap (TrivSqZeroExt.fstHom Γ(Z, ⊤) Γ(Z, ⊤) Γ(Z, ⊤)).toRingHom ∘
        Z.toSpecΓ.base := funext (dualNumbersLRS_toΓSpecFun Z)
  rw [this]
  exact (PrimeSpectrum.isHomeomorph_comap_dualNumberFst _).comp hZ

/-- For an affine scheme `Z`, the canonical morphism `Z[ε] ⟶ Spec Γ(Z[ε])` is an
isomorphism. -/
instance isIso_dualNumbersLRS_toΓSpec : IsIso Z.dualNumbersLRS.toΓSpec := by
  have h := isHomeomorph_dualNumbersLRS_toΓSpec_base Z
  have := LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ h.isOpenEmbedding
  have : Epi Z.dualNumbersLRS.toΓSpec.base := (TopCat.epi_iff_surjective _).2 h.surjective
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

/-- The locally ringed space `X[ε]` is locally the spectrum of a ring: over an affine open `U`
of `X` it is `Spec Γ(U)[ε]`. -/
lemma dualNumbersLRS_local_affine (X : Scheme.{u}) (x : X) :
    ∃ (U : OpenNhds x) (R : CommRingCat), Nonempty
      (X.dualNumbersLRS.restrict U.isOpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (.op R)) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsAffine (Scheme.Opens.toScheme U) := hU
  exact ⟨⟨U, hxU⟩, _, ⟨Iso.refl _ ≪≫ asIso (Scheme.Opens.toScheme U).dualNumbersLRS.toΓSpec⟩⟩

end Scheme

end DualNumbersLRS

namespace Scheme

variable (X : Scheme.{u})

/-- The dual-number thickening `X[ε]` of a scheme `X`: the same underlying space with structure
sheaf `𝒪_X[ε] = 𝒪_X ⊕ ε𝒪_X`, the relative spectrum of the sheaf of algebras `𝒪_X[ε]`.
(blueprint: `sk-d-tangent`) -/
noncomputable def dualNumbers : Scheme.{u} where
  carrier := X.carrier
  presheaf := X.presheaf ⋙ CommRingCat.dualNumber
  IsSheaf := X.dualNumbersLRS.IsSheaf
  isLocalRing := X.dualNumbersLRS.isLocalRing
  local_affine := X.dualNumbersLRS_local_affine

/-- The sections of `𝒪_{X[ε]}` over `U` are the dual numbers over the sections of `𝒪_X`. -/
theorem dualNumbers_obj (U : X.Opens) :
    Γ(X.dualNumbers, U) = CommRingCat.of (DualNumber Γ(X, U)) :=
  rfl

/-- The projection `p : X[ε] ⟶ X`: the identity on points and the inclusion of constants
`𝒪_X → 𝒪_X[ε]` on functions. -/
noncomputable def dualNumbersProj : X.dualNumbers ⟶ X where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberInl ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    rw [show PresheafedSpace.Hom.stalkMap _ x = X.presheaf.dualNumberStalkInl x from ?_]
    · exact X.presheaf.isLocalHom_dualNumberStalkInl x
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hx ↦ ?_
    rw [PresheafedSpace.stalkMap_germ]
    ext s
    exact (X.presheaf.dualNumberStalkInl_germ x U hx s).symm

/-- The closed immersion `i : X ⟶ X[ε]`, `ε ↦ 0`: the identity on points and the augmentation
`𝒪_X[ε] → 𝒪_X` on functions. Its ideal is the square-zero ideal `ε𝒪_X`. -/
noncomputable def dualNumbersι : X ⟶ X.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberFst ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    rw [show PresheafedSpace.Hom.stalkMap _ x = X.presheaf.dualNumberStalkFst x from ?_]
    · exact X.presheaf.isLocalHom_dualNumberStalkFst x
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hx ↦ ?_
    rw [PresheafedSpace.stalkMap_germ]
    ext s
    exact (X.presheaf.dualNumberStalkFst_germ x U hx s).symm

@[reassoc (attr := simp)]
theorem dualNumbersι_comp_proj : X.dualNumbersι ≫ X.dualNumbersProj = 𝟙 X := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a
  simp only [Hom.id_base, Hom.comp_base, Opens.map_comp_obj, Hom.comp_app, eqToHom_refl, op_id,
    Category.assoc, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Hom.id_app,
    CommRingCat.hom_id]
  exact (congrArg (fun φ ↦ CommRingCat.Hom.hom φ _) (X.presheaf.map_id _)).trans rfl

/-- The map `X[ε][δ] ⟶ X[η]`, `η ↦ εδ`: the identity on points, and on functions
`a + ηb ↦ a + εδb`. -/
noncomputable def dualNumbersMul : X.dualNumbers.dualNumbers ⟶ X.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberMul ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    rw [show PresheafedSpace.Hom.stalkMap _ x = X.presheaf.dualNumberStalkMul x from ?_]
    · exact X.presheaf.isLocalHom_dualNumberStalkMul x
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hx ↦ ?_
    rw [PresheafedSpace.stalkMap_germ]
    ext s
    exact (X.presheaf.dualNumberStalkMul_germ x U hx s).symm

variable {X} {Y : Scheme.{u}}

/-- Functoriality of the thickening: `f[ε] : X[ε] ⟶ Y[ε]` for `f : X ⟶ Y`, acting on functions by
`a + εb ↦ f^♯(a) + εf^♯(b)`. -/
noncomputable def Hom.dualNumbers (f : X ⟶ Y) : X.dualNumbers ⟶ Y.dualNumbers where
  base := f.base
  c := Functor.whiskerRight f.c CommRingCat.dualNumber
  prop x := by
    have key (φ : Y.dualNumbers.presheaf.stalk (f.base x) ⟶ X.dualNumbers.presheaf.stalk x)
        (h : φ ≫ X.presheaf.dualNumberStalkFst x =
          Y.presheaf.dualNumberStalkFst (f.base x) ≫ f.stalkMap x) : IsLocalHom φ.hom := by
      have : IsLocalHom ((X.presheaf.dualNumberStalkFst x).hom.comp φ.hom) := by
        rw [← CommRingCat.hom_comp, h, CommRingCat.hom_comp]
        have := Y.presheaf.isLocalHom_dualNumberStalkFst (f.base x)
        infer_instance
      exact isLocalHom_of_comp _ (X.presheaf.dualNumberStalkFst x).hom
    refine key _ (TopCat.Presheaf.stalk_hom_ext _ fun U hx ↦ ?_)
    refine (PresheafedSpace.stalkMap_germ_assoc
      (X := X.dualNumbers.toPresheafedSpace) (Y := Y.dualNumbers.toPresheafedSpace) _ U x hx
      _).trans ?_
    ext s
    change X.presheaf.dualNumberStalkFst x (TopCat.Presheaf.germ
        (X.presheaf ⋙ CommRingCat.dualNumber) (f ⁻¹ᵁ U) x hx
          (DualNumber.mapRingHom (f.app U).hom s)) =
      f.stalkMap x (Y.presheaf.dualNumberStalkFst (f.base x)
        (TopCat.Presheaf.germ (Y.presheaf ⋙ CommRingCat.dualNumber) U (f.base x) hx s))
    rw [TopCat.Presheaf.dualNumberStalkFst_germ, TopCat.Presheaf.dualNumberStalkFst_germ,
      DualNumber.fst_mapRingHom]
    exact (Scheme.Hom.germ_stalkMap_apply f U x hx s.fst).symm

@[reassoc (attr := simp)]
theorem Hom.dualNumbers_comp_proj (f : X ⟶ Y) :
    f.dualNumbers ≫ Y.dualNumbersProj = X.dualNumbersProj ≫ f := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a
  simp only [Hom.comp_base, Opens.map_comp_obj, Hom.comp_app, eqToHom_refl, op_id,
    Category.assoc, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  refine (congrArg (fun φ ↦ CommRingCat.Hom.hom φ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
  change (DualNumber.mapRingHom (f.app U).hom (TrivSqZeroExt.inl a) : DualNumber Γ(X, f ⁻¹ᵁ U)) =
    TrivSqZeroExt.inl (f.app U a)
  ext <;> simp

@[reassoc (attr := simp)]
theorem Hom.ι_comp_dualNumbers (f : X ⟶ Y) :
    X.dualNumbersι ≫ f.dualNumbers = f ≫ Y.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a
  simp only [Hom.comp_base, Opens.map_comp_obj, Hom.comp_app, eqToHom_refl, op_id,
    Category.assoc, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  refine (congrArg (fun φ ↦ CommRingCat.Hom.hom φ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
  change (DualNumber.mapRingHom (f.app U).hom a).fst = f.app U a.fst
  exact DualNumber.fst_mapRingHom _ _

theorem Hom.dualNumbers_id : Hom.dualNumbers (𝟙 X) = 𝟙 X.dualNumbers := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a
  simp only [Hom.id_base, eqToHom_refl, op_id, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply, Hom.id_app, CommRingCat.hom_id]
  refine (congrArg (fun φ ↦ CommRingCat.Hom.hom φ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
  change DualNumber.mapRingHom (RingHom.id _) a = a
  rw [DualNumber.mapRingHom_id]
  rfl

theorem Hom.dualNumbers_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).dualNumbers = f.dualNumbers ≫ g.dualNumbers := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a
  simp only [comp_base, Opens.map_comp_obj, eqToHom_refl, op_id, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply, comp_app]
  refine (congrArg (fun φ ↦ CommRingCat.Hom.hom φ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
  exact DFunLike.congr_fun (DualNumber.mapRingHom_comp (g.app U).hom (f.app (g ⁻¹ᵁ U)).hom) a

@[reassoc (attr := simp)]
theorem dualNumbersMul_comp_proj (X : Scheme.{u}) :
    X.dualNumbersMul ≫ X.dualNumbersProj = X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a
  simp only [Hom.comp_base, Opens.map_comp_obj, Hom.comp_app, eqToHom_refl, op_id,
    Category.assoc, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  refine (congrArg (fun φ ↦ CommRingCat.Hom.hom φ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
  change (TrivSqZeroExt.inl (TrivSqZeroExt.inl a) + TrivSqZeroExt.inr (TrivSqZeroExt.inr 0) :
    DualNumber (DualNumber Γ(X, U))) = TrivSqZeroExt.inl (TrivSqZeroExt.inl a)
  simp

/-! ### The thickening of an affine scheme -/

variable (R : CommRingCat.{u})

/-- The canonical morphism `(Spec R)[ε] ⟶ Spec R[ε]`, corresponding to the ring isomorphism
`R[ε] ≅ Γ(Spec R, 𝒪)[ε] = Γ((Spec R)[ε], 𝒪)`. It is an isomorphism. -/
noncomputable def dualNumbersToSpec : (Spec R).dualNumbers ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  (Spec R).dualNumbers.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom (Scheme.ΓSpecIso R).inv.hom))

/-- `(Spec R)[ε] ⟶ Spec R[ε]` is an isomorphism: both are the spectrum of `R[ε]`.

`ε` is nilpotent, so `Spec R[ε] → Spec R` is a homeomorphism, and the stalks of `(Spec R)[ε]` are
the localizations of `R[ε]`. -/
instance isIso_dualNumbersToSpec : IsIso (dualNumbersToSpec R) := by
  have : IsIso (Scheme.forgetToLocallyRingedSpace.map (Spec R).dualNumbers.toSpecΓ) :=
    isIso_dualNumbersLRS_toΓSpec (Spec R)
  have : IsIso (Spec R).dualNumbers.toSpecΓ :=
    isIso_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace
  have : IsIso (CommRingCat.ofHom (DualNumber.mapRingHom (Scheme.ΓSpecIso R).inv.hom)) :=
    (CommRingCat.dualNumber.mapIso (Scheme.ΓSpecIso R).symm).isIso_hom
  rw [dualNumbersToSpec]
  infer_instance

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` is compatible with the projections to `Spec R`. -/
theorem dualNumbersToSpec_comp_specMap :
    dualNumbersToSpec R ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom R R)) =
      (Spec R).dualNumbersProj := by
  have h := Scheme.toSpecΓ_naturality (Spec R).dualNumbersProj
  have h' : (Spec R).dualNumbersProj = (Spec R).dualNumbers.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (Spec R).dualNumbersProj.appTop) := by
    rw [Spec.map_comp, ← reassoc_of% h, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [h', dualNumbersToSpec, Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  change DualNumber.mapRingHom _ (TrivSqZeroExt.inl a) =
    (TrivSqZeroExt.inl ((Scheme.ΓSpecIso R).inv a) : DualNumber Γ(Spec R, ⊤))
  ext <;> simp

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` is compatible with the closed immersions `ε ↦ 0`. -/
theorem ι_comp_dualNumbersToSpec :
    (Spec R).dualNumbersι ≫ dualNumbersToSpec R =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  rw [dualNumbersToSpec, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  change (Scheme.ΓSpecIso R).hom (DualNumber.mapRingHom (Scheme.ΓSpecIso R).inv.hom x).fst = x.fst
  rw [DualNumber.fst_mapRingHom]
  exact Iso.inv_hom_id_apply _ _

end Scheme

end AlgebraicGeometry
