/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

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
- `AlgebraicGeometry.Scheme.dualNumbersScale`: the rescaling `X[ε] ⟶ X[ε]`, `ε ↦ rε`, by a global
  function `r`.
- `AlgebraicGeometry.Scheme.dualNumbersToSpec`: the isomorphism `(Spec R)[ε] ⟶ Spec R[ε]`.

## Implementation notes

The sheaf condition, the locality of the stalks, the local affineness of `X[ε]` and the locality
of the morphisms constructed here are not yet proved. They are the obligations of the next
milestone of the blueprint and are recorded as `sorry`.

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

/-- Rescaling `ε ↦ rε`: the ring endomorphism `a + εb ↦ a + ε rb` of `R[ε]`. -/
def scaleRingHom (r : R) : R[ε] →+* R[ε] where
  toFun x := inl x.fst + inr (r * x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp; ring

@[simp]
theorem fst_scaleRingHom (r : R) (x : R[ε]) : (scaleRingHom r x).fst = x.fst := by
  simp [scaleRingHom]

@[simp]
theorem snd_scaleRingHom (r : R) (x : R[ε]) : (scaleRingHom r x).snd = r * x.snd := by
  simp [scaleRingHom]

theorem mapRingHom_comp_scaleRingHom (f : R →+* S) (r : R) :
    (mapRingHom f).comp (scaleRingHom r) = (scaleRingHom (f r)).comp (mapRingHom f) := by
  ext x <;> simp

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

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

/-- The dual-number thickening `X[ε]` of a scheme `X`: the same underlying space with structure
sheaf `𝒪_X[ε] = 𝒪_X ⊕ ε𝒪_X`, the relative spectrum of the sheaf of algebras `𝒪_X[ε]`.
(blueprint: `sk-d-tangent`) -/
noncomputable def dualNumbers : Scheme.{u} where
  carrier := X.carrier
  presheaf := X.presheaf ⋙ CommRingCat.dualNumber
  IsSheaf := by sorry
  isLocalRing := by sorry
  local_affine := by sorry

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
  prop := by sorry

/-- The closed immersion `i : X ⟶ X[ε]`, `ε ↦ 0`: the identity on points and the augmentation
`𝒪_X[ε] → 𝒪_X` on functions. Its ideal is the square-zero ideal `ε𝒪_X`. -/
noncomputable def dualNumbersι : X ⟶ X.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberFst ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop := by sorry

@[reassoc (attr := simp)]
theorem dualNumbersι_comp_proj : X.dualNumbersι ≫ X.dualNumbersProj = 𝟙 X := by
  sorry

/-- The map `X[ε][δ] ⟶ X[η]`, `η ↦ εδ`: the identity on points, and on functions
`a + ηb ↦ a + εδb`. -/
noncomputable def dualNumbersMul : X.dualNumbers.dualNumbers ⟶ X.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberMul ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop := by sorry

/-- The rescaling `ε ↦ rε` of `𝒪_X[ε]` by a global function `r`, as a morphism of presheafed
spaces `X[ε] ⟶ X[ε]`. -/
noncomputable def dualNumbersScaleHom (r : Γ(X, ⊤)) :
    X.dualNumbers.toPresheafedSpace ⟶ X.dualNumbers.toPresheafedSpace where
  base := 𝟙 _
  c :=
    { app U := CommRingCat.ofHom
        (DualNumber.scaleRingHom (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op r))
      naturality U V f := by
        ext x
        change DualNumber.scaleRingHom _ (DualNumber.mapRingHom (X.presheaf.map f).hom x) =
          DualNumber.mapRingHom (X.presheaf.map f).hom (DualNumber.scaleRingHom _ x)
        rw [← RingHom.comp_apply, ← RingHom.comp_apply,
          DualNumber.mapRingHom_comp_scaleRingHom]
        congr 3
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl } ≫ (TopCat.Presheaf.Pushforward.id _).inv

theorem ι_comp_dualNumbersScaleHom (r : Γ(X, ⊤)) :
    X.dualNumbersι.toPshHom ≫ X.dualNumbersScaleHom r = X.dualNumbersι.toPshHom := by
  refine PresheafedSpace.ext _ _ rfl ?_
  ext U x
  simp only [Functor.comp_obj, Functor.op_obj, PresheafedSpace.comp_base, eqToHom_refl,
    Functor.whiskerRight_id', TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj,
    Opens.map_comp_obj, PresheafedSpace.comp_c_app, NatTrans.id_app, Category.comp_id,
    CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (DualNumber.scaleRingHom _ x).fst = x.fst
  exact DualNumber.fst_scaleRingHom _ _

/-- The rescaling `X[ε] ⟶ X[ε]`, `ε ↦ rε`, by a global function `r`: the identity on points and
`a + εb ↦ a + ε rb` on functions. It is a morphism of schemes since it fixes `X ⟶ X[ε]`. -/
noncomputable def dualNumbersScale (r : Γ(X, ⊤)) : X.dualNumbers ⟶ X.dualNumbers where
  toHom := X.dualNumbersScaleHom r
  prop y := by
    have h := PresheafedSpace.stalkMap.comp X.dualNumbersι.toPshHom (X.dualNumbersScaleHom r) y
    rw [PresheafedSpace.stalkMap.congr_hom _ _ (ι_comp_dualNumbersScaleHom X r),
      eqToHom_refl, Category.id_comp] at h
    have := X.dualNumbersι.prop y
    rw [h, CommRingCat.hom_comp] at this
    exact @isLocalHom_of_comp _ _ _ _ _ _ _ _ this

@[reassoc (attr := simp)]
theorem dualNumbersι_comp_dualNumbersScale (r : Γ(X, ⊤)) :
    X.dualNumbersι ≫ X.dualNumbersScale r = X.dualNumbersι :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (ι_comp_dualNumbersScaleHom X r))

@[reassoc (attr := simp)]
theorem dualNumbersScale_comp_proj (r : Γ(X, ⊤)) :
    X.dualNumbersScale r ≫ X.dualNumbersProj = X.dualNumbersProj := by
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (PresheafedSpace.ext _ _ rfl ?_))
  ext U x
  simp only [Functor.comp_obj, Functor.op_obj, eqToHom_refl, Functor.whiskerRight_id',
    TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj, NatTrans.id_app,
    Category.comp_id]
  change DualNumber.scaleRingHom _ (inl x) = inl x
  ext <;> simp

variable {X} {Y : Scheme.{u}}

/-- Functoriality of the thickening: `f[ε] : X[ε] ⟶ Y[ε]` for `f : X ⟶ Y`, acting on functions by
`a + εb ↦ f^♯(a) + εf^♯(b)`. -/
noncomputable def Hom.dualNumbers (f : X ⟶ Y) : X.dualNumbers ⟶ Y.dualNumbers where
  base := f.base
  c := Functor.whiskerRight f.c CommRingCat.dualNumber
  prop := by sorry

@[reassoc (attr := simp)]
theorem Hom.dualNumbers_comp_proj (f : X ⟶ Y) :
    f.dualNumbers ≫ Y.dualNumbersProj = X.dualNumbersProj ≫ f := by
  sorry

@[reassoc (attr := simp)]
theorem Hom.ι_comp_dualNumbers (f : X ⟶ Y) :
    X.dualNumbersι ≫ f.dualNumbers = f ≫ Y.dualNumbersι := by
  sorry

theorem Hom.dualNumbers_id : Hom.dualNumbers (𝟙 X) = 𝟙 X.dualNumbers := by
  sorry

theorem Hom.dualNumbers_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).dualNumbers = f.dualNumbers ≫ g.dualNumbers := by
  sorry

@[reassoc (attr := simp)]
theorem dualNumbersMul_comp_proj (X : Scheme.{u}) :
    X.dualNumbersMul ≫ X.dualNumbersProj = X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj := by
  sorry

/-! ### The thickening of an affine scheme -/

variable (R : CommRingCat.{u})

/-- The canonical morphism `(Spec R)[ε] ⟶ Spec R[ε]`, corresponding to the ring isomorphism
`R[ε] ≅ Γ(Spec R, 𝒪)[ε] = Γ((Spec R)[ε], 𝒪)`. It is an isomorphism. -/
noncomputable def dualNumbersToSpec : (Spec R).dualNumbers ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  (Spec R).dualNumbers.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom (Scheme.ΓSpecIso R).inv.hom))

/-- `(Spec R)[ε] ⟶ Spec R[ε]` is an isomorphism: both are the spectrum of `R[ε]`.

Proof sketch (not formalised): `ε` is nilpotent, so `Spec R[ε] → Spec R` is a homeomorphism, and
on principal opens `(R[ε])_f = R_f[ε]`, which is the structure sheaf of `(Spec R)[ε]`. -/
instance isIso_dualNumbersToSpec : IsIso (dualNumbersToSpec R) := by
  sorry

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` is compatible with the projections to `Spec R`. -/
theorem dualNumbersToSpec_comp_specMap :
    dualNumbersToSpec R ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom R R)) =
      (Spec R).dualNumbersProj := by
  sorry

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` is compatible with the closed immersions `ε ↦ 0`. -/
theorem ι_comp_dualNumbersToSpec :
    (Spec R).dualNumbersι ≫ dualNumbersToSpec R =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  sorry

end Scheme

end AlgebraicGeometry
