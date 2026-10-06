/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.AffineScheme
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

/-- The ring homomorphism `R[η] → R[ε][δ]`, `a + ηb ↦ a + εδ b`, recording the mixed infinitesimal
term of the two-parameter dual numbers `R[ε][δ] = R[ε, δ]/(ε², δ²)`. -/
def mulRingHom : R[ε] →+* (R[ε])[ε] where
  toFun x := inl (inl x.fst) + inr (inr x.snd)
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

/-- The map `R[η] → R[ε][δ]`, `η ↦ εδ`, as an `R`-algebra homomorphism. -/
def mulAlgHom : R[ε] →ₐ[R] (R[ε])[ε] :=
  { mulRingHom with
    commutes' := fun r ↦ by ext <;> simp [mulRingHom, algebraMap_eq_inl'] }

/-- The inclusion `R[δ] → R[ε][δ]`, `a + δb ↦ a + δb`, as an `R`-algebra homomorphism. -/
def mapInlAlgHom : R[ε] →ₐ[R] (R[ε])[ε] :=
  { mapRingHom (inlHom R R) with
    commutes' := fun r ↦ by ext <;> simp [mapRingHom, algebraMap_eq_inl'] }

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

/-! ### The two-parameter thickening of an affine scheme -/

/-- On global sections, `(Spec R)[ε] ⟶ Spec R[ε]` is `R[ε] ≅ Γ(Spec R, ⊤)[ε]`. -/
theorem dualNumbersToSpec_appTop :
    (dualNumbersToSpec R).appTop = (ΓSpecIso (CommRingCat.dualNumber.obj R)).hom ≫
      CommRingCat.dualNumber.map (Scheme.ΓSpecIso R).inv := by
  simp [dualNumbersToSpec]
  rfl

variable {X Y : Scheme.{u}} in
theorem Hom.dualNumbers_appTop (f : X ⟶ Y) :
    f.dualNumbers.appTop = CommRingCat.dualNumber.map f.appTop :=
  rfl

theorem dualNumbersMul_appTop (X : Scheme.{u}) :
    X.dualNumbersMul.appTop = CommRingCat.dualNumberMul.app Γ(X, ⊤) := by
  simp [dualNumbersMul, Scheme.Hom.appTop, Scheme.Hom.app]

variable {R} {S : CommRingCat.{u}} in
/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` is natural in `R`. -/
theorem specMap_dualNumbers_comp_dualNumbersToSpec (φ : R ⟶ S) :
    (Spec.map φ).dualNumbers ≫ dualNumbersToSpec R =
      dualNumbersToSpec S ≫ Spec.map (CommRingCat.dualNumber.map φ) := by
  refine ext_of_isAffine ?_
  simp only [Scheme.Hom.comp_appTop, dualNumbersToSpec_appTop, Hom.dualNumbers_appTop,
    Category.assoc, ← Functor.map_comp]
  erw [ΓSpecIso_naturality_assoc, ← ΓSpecIso_inv_naturality, Functor.map_comp]

/-- The canonical morphism `(Spec R)[ε][δ] ⟶ Spec R[ε][δ]`, built from `(Spec R)[ε] ≅ Spec R[ε]`
twice. It is an isomorphism. -/
noncomputable def dualNumbers₂ToSpec :
    (Spec R).dualNumbers.dualNumbers ⟶ Spec (.of (DualNumber (DualNumber R))) :=
  (dualNumbersToSpec R).dualNumbers ≫ dualNumbersToSpec (.of (DualNumber R))

/-- Through `(Spec R)[ε][δ] ≅ Spec R[ε][δ]`, the map `η ↦ εδ` is `Spec` of `R[η] → R[ε][δ]`. -/
theorem dualNumbersMul_comp_dualNumbersToSpec :
    (Spec R).dualNumbersMul ≫ dualNumbersToSpec R =
      dualNumbers₂ToSpec R ≫ Spec.map (CommRingCat.dualNumberMul.app R) := by
  refine ext_of_isAffine ?_
  simp only [dualNumbers₂ToSpec, Scheme.Hom.comp_appTop, dualNumbersToSpec_appTop,
    Hom.dualNumbers_appTop, dualNumbersMul_appTop, Category.assoc]
  erw [dualNumbersToSpec_appTop]
  simp only [Category.assoc]
  erw [ΓSpecIso_naturality_assoc]
  congr 1
  rw [← Functor.map_comp]
  erw [Iso.inv_hom_id_assoc]
  exact CommRingCat.dualNumberMul.naturality _

/-- `(Spec R)[ε][δ] ⟶ Spec R[ε][δ]` is an isomorphism, by functoriality of the thickening. -/
instance isIso_dualNumbers₂ToSpec : IsIso (dualNumbers₂ToSpec R) := by
  have : IsIso (dualNumbersToSpec R).dualNumbers :=
    ⟨(inv (dualNumbersToSpec R)).dualNumbers, by
      rw [← Hom.dualNumbers_comp, IsIso.hom_inv_id, Hom.dualNumbers_id], by
      rw [← Hom.dualNumbers_comp, IsIso.inv_hom_id, Hom.dualNumbers_id]⟩
  unfold dualNumbers₂ToSpec
  infer_instance

/-- Through `(Spec R)[ε][δ] ≅ Spec R[ε][δ]`, forgetting `δ` is `Spec` of `R[ε] → R[ε][δ]`. -/
theorem dualNumbersProj_comp_dualNumbersToSpec :
    (Spec R).dualNumbers.dualNumbersProj ≫ dualNumbersToSpec R =
      dualNumbers₂ToSpec R ≫
        Spec.map (CommRingCat.ofHom (inlHom (DualNumber R) (DualNumber R))) := by
  rw [dualNumbers₂ToSpec, Category.assoc, dualNumbersToSpec_comp_specMap]
  exact (Hom.dualNumbers_comp_proj _).symm

/-- Through `(Spec R)[ε][δ] ≅ Spec R[ε][δ]`, forgetting `ε` is `Spec` of `R[δ] → R[ε][δ]`. -/
theorem dualNumbers_dualNumbersProj_comp_dualNumbersToSpec :
    (Spec R).dualNumbersProj.dualNumbers ≫ dualNumbersToSpec R =
      dualNumbers₂ToSpec R ≫
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom (inlHom R R))) := by
  rw [← dualNumbersToSpec_comp_specMap, Hom.dualNumbers_comp, Category.assoc,
    specMap_dualNumbers_comp_dualNumbersToSpec
      (CommRingCat.ofHom (inlHom R R) : R ⟶ .of (DualNumber R)),
    dualNumbers₂ToSpec, Category.assoc]
  rfl

/-- `(Spec R)[ε][δ] ⟶ Spec R[ε][δ]` is a morphism over `Spec R`. -/
theorem dualNumbers₂ToSpec_comp_specMap :
    dualNumbers₂ToSpec R ≫ Spec.map (CommRingCat.ofHom (inlHom R R) ≫
      CommRingCat.ofHom (inlHom (DualNumber R) (DualNumber R))) =
      (Spec R).dualNumbers.dualNumbersProj ≫ (Spec R).dualNumbersProj := by
  rw [Spec.map_comp, ← Category.assoc, ← dualNumbersProj_comp_dualNumbersToSpec,
    Category.assoc, dualNumbersToSpec_comp_specMap]

end Scheme

end AlgebraicGeometry
