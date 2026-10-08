/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.Mathlib.Algebra.DualNumber

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
- `AlgebraicGeometry.Scheme.dualNumbersScale`: scaling the infinitesimal, `ε ↦ cε`, by a global
  section `c` of `𝒪_X`.
- `AlgebraicGeometry.Scheme.dualNumbersOver`, `AlgebraicGeometry.Scheme.dualNumbers₂Over`: the
  thickenings `S[ε]` and `S[ε][δ]` as schemes over `S`, with the morphisms above as morphisms over
  `S` (`dualNumbersιOver`, `dualNumbersScaleOver`, `dualNumbersMulOver`, ...).
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

open CategoryTheory MonoidalCategory TopologicalSpace TrivSqZeroExt

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

/-- Setting `δ = 0` in `a + εδ b` gives `a`. -/
theorem fstHom_comp_mulRingHom :
    (fstHom R[ε] R[ε] R[ε]).toRingHom.comp mulRingHom =
      (inlHom R R).comp (fstHom R R R).toRingHom := by
  ext x <;> simp [mulRingHom, algebraMap_eq_inl]

/-- Setting `ε = 0` in `a + εδ b` gives `a`. -/
theorem mapRingHom_fstHom_comp_mulRingHom :
    (mapRingHom (fstHom R R R).toRingHom).comp mulRingHom =
      (inlHom R R).comp (fstHom R R R).toRingHom := by
  ext x <;> simp [mulRingHom, algebraMap_eq_inl]

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

/-- Setting `δ = 0` in `η ↦ εδ`: the composite `X[ε] ⟶ X[ε][δ] ⟶ X[η]` factors through `X`. -/
@[reassoc]
theorem dualNumbersι_comp_dualNumbersMul (X : Scheme.{u}) :
    X.dualNumbers.dualNumbersι ≫ X.dualNumbersMul = X.dualNumbersProj ≫ X.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  rw [Subsingleton.elim (eqToHom _) (𝟙 _), CategoryTheory.op_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [dualNumbersProj, dualNumbersι, Hom.comp_base, dualNumbersMul, Opens.map_comp_obj,
    Hom.app, TopCat.Presheaf.comp_app, Functor.comp_obj, TopCat.Presheaf.pushforward_obj_obj,
    Functor.whiskerLeft_app, TopCat.Presheaf.Pushforward.id_inv_app, Category.comp_id,
    Functor.id_obj, Hom.comp_app]
  ext1
  exact DualNumber.fstHom_comp_mulRingHom

/-- Setting `ε = 0` in `η ↦ εδ`: the composite `X[δ] ⟶ X[ε][δ] ⟶ X[η]` factors through `X`. -/
@[reassoc]
theorem Hom.dualNumbers_dualNumbersι_comp_dualNumbersMul (X : Scheme.{u}) :
    X.dualNumbersι.dualNumbers ≫ X.dualNumbersMul = X.dualNumbersProj ≫ X.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  rw [Subsingleton.elim (eqToHom _) (𝟙 _), CategoryTheory.op_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [dualNumbersProj, dualNumbersι, Hom.comp_base, Hom.dualNumbers, dualNumbersMul,
    Opens.map_comp_obj, Hom.app, TopCat.Presheaf.comp_app, Functor.comp_obj,
    TopCat.Presheaf.pushforward_obj_obj, Functor.whiskerLeft_app,
    TopCat.Presheaf.Pushforward.id_inv_app, Category.comp_id, Functor.whiskerRight_app,
    Functor.id_obj, Hom.comp_app]
  ext1
  exact DualNumber.mapRingHom_fstHom_comp_mulRingHom

/-! ### Scaling the infinitesimal -/

variable (X) in
/-- Scaling the infinitesimal by a global section `c` of `𝒪_X`: the endomorphism `ε ↦ cε` of
`X[ε]`, the identity on points and `a + εb ↦ a + εcb` on functions. It is the scalar action of
`Γ(X, 𝒪_X)` on tangent vectors. -/
noncomputable def dualNumbersScale (c : Γ(X, ⊤)) : X.dualNumbers ⟶ X.dualNumbers where
  base := 𝟙 _
  c := { app := fun U ↦ CommRingCat.ofHom
            (DualNumber.scale (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op c)).toRingHom
         naturality := by sorry } ≫ (TopCat.Presheaf.Pushforward.id _).inv
  prop := by sorry

@[reassoc (attr := simp)]
theorem dualNumbersScale_comp_proj (c : Γ(X, ⊤)) :
    X.dualNumbersScale c ≫ X.dualNumbersProj = X.dualNumbersProj := by
  sorry

@[reassoc (attr := simp)]
theorem dualNumbersι_comp_scale (c : Γ(X, ⊤)) :
    X.dualNumbersι ≫ X.dualNumbersScale c = X.dualNumbersι := by
  sorry

@[simp]
theorem dualNumbersScale_one : X.dualNumbersScale 1 = 𝟙 _ := by
  sorry

theorem dualNumbersScale_mul (c d : Γ(X, ⊤)) :
    X.dualNumbersScale (c * d) = X.dualNumbersScale c ≫ X.dualNumbersScale d := by
  sorry

/-- Scaling by `0` is the composite `X[ε] ⟶ X ⟶ X[ε]`, `ε ↦ 0`. -/
theorem dualNumbersScale_zero : X.dualNumbersScale 0 = X.dualNumbersProj ≫ X.dualNumbersι := by
  sorry

/-! ### The thickening as a scheme over its base -/

section Over

variable (S : Scheme.{u})

/-- The thickening `S[ε]` as a scheme over `S`, through the projection `p : S[ε] ⟶ S`. -/
noncomputable def dualNumbersOver : Over S :=
  Over.mk S.dualNumbersProj

@[simp]
theorem dualNumbersOver_left : (dualNumbersOver S).left = S.dualNumbers :=
  rfl

@[simp]
theorem dualNumbersOver_hom : (dualNumbersOver S).hom = S.dualNumbersProj :=
  rfl

/-- The two-parameter thickening `S[ε][δ]` as a scheme over `S`. -/
noncomputable def dualNumbers₂Over : Over S :=
  Over.mk (S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj)

/-- The closed immersion `i : S ⟶ S[ε]`, `ε ↦ 0`, as a morphism over `S` from the terminal
object `S` of the schemes over `S`: the `S`-point `ε ↦ 0` of `S[ε]`. -/
noncomputable def dualNumbersιOver : 𝟙_ (Over S) ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersι S.dualNumbersι_comp_proj

@[simp]
theorem dualNumbersιOver_left : (dualNumbersιOver S).left = S.dualNumbersι :=
  rfl

/-- The projection `S[ε][δ] ⟶ S[ε]` forgetting `δ`, as a morphism over `S`. -/
noncomputable def dualNumbersProjεOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbers.dualNumbersProj

/-- The projection `S[ε][δ] ⟶ S[δ]` forgetting `ε`, as a morphism over `S`. -/
noncomputable def dualNumbersProjδOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersProj.dualNumbers (by sorry)

/-- The closed immersion `S[ε] ⟶ S[ε][δ]`, `δ ↦ 0`, as a morphism over `S`. -/
noncomputable def dualNumbersιεOver : dualNumbersOver S ⟶ dualNumbers₂Over S :=
  Over.homMk S.dualNumbers.dualNumbersι (by sorry)

/-- The closed immersion `S[δ] ⟶ S[ε][δ]`, `ε ↦ 0`, as a morphism over `S`. -/
noncomputable def dualNumbersιδOver : dualNumbersOver S ⟶ dualNumbers₂Over S :=
  Over.homMk S.dualNumbersι.dualNumbers (by sorry)

/-- The map `S[ε][δ] ⟶ S[η]`, `η ↦ εδ`, as a morphism over `S`. -/
noncomputable def dualNumbersMulOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersMul (by sorry)

/-- Setting `δ = 0` in `η ↦ εδ` factors through the `S`-point `ε ↦ 0` of `S[η]`. -/
@[reassoc]
theorem dualNumbersιεOver_comp_dualNumbersMulOver :
    dualNumbersιεOver S ≫ dualNumbersMulOver S =
      CartesianMonoidalCategory.toUnit (dualNumbersOver S) ≫ dualNumbersιOver S := by
  ext1
  simpa [dualNumbersιεOver, dualNumbersMulOver, Over.toUnit_left] using
    S.dualNumbersι_comp_dualNumbersMul

/-- Setting `ε = 0` in `η ↦ εδ` factors through the `S`-point `ε ↦ 0` of `S[η]`. -/
@[reassoc]
theorem dualNumbersιδOver_comp_dualNumbersMulOver :
    dualNumbersιδOver S ≫ dualNumbersMulOver S =
      CartesianMonoidalCategory.toUnit (dualNumbersOver S) ≫ dualNumbersιOver S := by
  ext1
  simpa [dualNumbersιδOver, dualNumbersMulOver, Over.toUnit_left] using
    Hom.dualNumbers_dualNumbersι_comp_dualNumbersMul S

/-- Scaling the infinitesimal by a global section `c` of `𝒪_S`, as an endomorphism of `S[ε]`
over `S`. -/
noncomputable def dualNumbersScaleOver (c : Γ(S, ⊤)) : dualNumbersOver S ⟶ dualNumbersOver S :=
  Over.homMk (S.dualNumbersScale c) (S.dualNumbersScale_comp_proj c)

@[simp]
theorem dualNumbersScaleOver_left (c : Γ(S, ⊤)) :
    (dualNumbersScaleOver S c).left = S.dualNumbersScale c :=
  rfl

@[reassoc (attr := simp)]
theorem dualNumbersιOver_comp_scaleOver (c : Γ(S, ⊤)) :
    dualNumbersιOver S ≫ dualNumbersScaleOver S c = dualNumbersιOver S := by
  ext : 1
  simp

@[simp]
theorem dualNumbersScaleOver_one : dualNumbersScaleOver S 1 = 𝟙 _ := by
  ext : 1
  simp

theorem dualNumbersScaleOver_mul (c d : Γ(S, ⊤)) :
    dualNumbersScaleOver S (c * d) = dualNumbersScaleOver S c ≫ dualNumbersScaleOver S d := by
  ext : 1
  simp [dualNumbersScale_mul]

/-- Scaling by `0` factors through the `S`-point `ε ↦ 0` of `S[ε]`. -/
theorem dualNumbersScaleOver_zero :
    dualNumbersScaleOver S 0 =
      CartesianMonoidalCategory.toUnit (dualNumbersOver S) ≫ dualNumbersιOver S := by
  ext : 1
  simp [dualNumbersScale_zero, Over.toUnit_left]

end Over

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
