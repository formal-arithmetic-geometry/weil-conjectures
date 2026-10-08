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
public import WeilConjectures.Mathlib.RingTheory.DualNumber

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

open CategoryTheory Limits MonoidalCategory TopologicalSpace TrivSqZeroExt Opposite

/-! ### Dual numbers as a functor on commutative rings -/

namespace DualNumber

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A ring homomorphism `f : R → S` induces `R[ε] → S[ε]`, `a + εb ↦ f(a) + εf(b)`. -/
def mapRingHom (f : R →+* S) : R[ε] →+* S[ε] where
  toFun x := inl (f x.fst) + inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp]
theorem fst_mapRingHom (f : R →+* S) (x : R[ε]) : (mapRingHom f x).fst = f x.fst := by
  simp [mapRingHom]

@[simp]
theorem snd_mapRingHom (f : R →+* S) (x : R[ε]) : (mapRingHom f x).snd = f x.snd := by
  simp [mapRingHom]

theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[ε] := by
  ext x <;> simp

theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  ext x <;> simp

theorem mapRingHom_comp_inlHom (f : R →+* S) :
    (mapRingHom f).comp (inlHom R R) = (inlHom S S).comp f := by
  ext x <;> simp

theorem fstHom_comp_mapRingHom (f : R →+* S) :
    (fstHom S S S).toRingHom.comp (mapRingHom f) = f.comp (fstHom R R R).toRingHom :=
  RingHom.ext fun x ↦ by simp

/-- The ring homomorphism `R[η] → R[ε][δ]`, `a + ηb ↦ a + εδ b`, recording the mixed infinitesimal
term of the two-parameter dual numbers `R[ε][δ] = R[ε, δ]/(ε², δ²)`. -/
def mulRingHom : R[ε] →+* (R[ε])[ε] where
  toFun x := inl (inl x.fst) + inr (inr x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [mul_comm]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp]
theorem fst_mulRingHom (x : R[ε]) : (mulRingHom x).fst = inl x.fst := by
  simp [mulRingHom]

@[simp]
theorem snd_mulRingHom (x : R[ε]) : (mulRingHom x).snd = inr x.snd := by
  simp [mulRingHom]

theorem mapRingHom_mapRingHom_comp_mulRingHom (f : R →+* S) :
    (mapRingHom (mapRingHom f)).comp mulRingHom = mulRingHom.comp (mapRingHom f) := by
  ext x <;> simp

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
  naturality _ _ f := hom_ext (DualNumber.mapRingHom_comp_inlHom f.hom).symm

/-- The augmentation `R[ε] → R`, `ε ↦ 0`, naturally in `R`. -/
noncomputable def dualNumberFst : dualNumber ⟶ 𝟭 CommRingCat.{u} where
  app R := ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
  naturality _ _ f := hom_ext (DualNumber.fstHom_comp_mapRingHom f.hom)

/-- The map `R[η] → R[ε][δ]`, `η ↦ εδ`, naturally in `R`. -/
noncomputable def dualNumberMul : dualNumber ⟶ dualNumber ⋙ dualNumber where
  app _ := ofHom DualNumber.mulRingHom
  naturality _ _ f := hom_ext (DualNumber.mapRingHom_mapRingHom_comp_mulRingHom f.hom).symm

theorem fst_dualNumber_map {R S : CommRingCat.{u}} (f : R ⟶ S) (x : DualNumber R) :
    (dualNumber.map f x).fst = f x.fst :=
  DualNumber.fst_mapRingHom _ _

theorem snd_dualNumber_map {R S : CommRingCat.{u}} (f : R ⟶ S) (x : DualNumber R) :
    (dualNumber.map f x).snd = f x.snd :=
  DualNumber.snd_mapRingHom _ _

end CommRingCat

/-! ### Stalks of the dual-number thickening -/

namespace TopCat.Presheaf
variable {X : TopCat.{u}} (P : X.Presheaf CommRingCat.{u}) (x : X)

/-- The comparison map from the stalk of `P[ε]` to the dual numbers over the stalk of `P`. -/
noncomputable def stalkDualNumberHom :
    stalk (P ⋙ CommRingCat.dualNumber) x ⟶ CommRingCat.dualNumber.obj (P.stalk x) :=
  colimit.post ((OpenNhds.inclusion x).op ⋙ P) CommRingCat.dualNumber

@[reassoc]
theorem germ_stalkDualNumberHom (U : Opens X) (hx : x ∈ U) :
    germ (P ⋙ CommRingCat.dualNumber) U x hx ≫ P.stalkDualNumberHom x =
      CommRingCat.dualNumber.map (P.germ U x hx) :=
  colimit.ι_post ((OpenNhds.inclusion x).op ⋙ P) CommRingCat.dualNumber (op ⟨U, hx⟩)

theorem stalkDualNumberHom_germ (U : Opens X) (hx : x ∈ U) (g : DualNumber (P.obj (op U))) :
    P.stalkDualNumberHom x (germ (P ⋙ CommRingCat.dualNumber) U x hx g) =
      DualNumber.mapRingHom (P.germ U x hx).hom g :=
  congr($(P.germ_stalkDualNumberHom x U hx) g)

@[simp]
theorem fst_stalkDualNumberHom_germ (U : Opens X) (hx : x ∈ U) (g : DualNumber (P.obj (op U))) :
    (P.stalkDualNumberHom x (germ (P ⋙ CommRingCat.dualNumber) U x hx g)).fst =
      P.germ U x hx g.fst :=
  congr(TrivSqZeroExt.fst $(P.stalkDualNumberHom_germ x U hx g)).trans
    (DualNumber.fst_mapRingHom _ _)

@[simp]
theorem snd_stalkDualNumberHom_germ (U : Opens X) (hx : x ∈ U) (g : DualNumber (P.obj (op U))) :
    (P.stalkDualNumberHom x (germ (P ⋙ CommRingCat.dualNumber) U x hx g)).snd =
      P.germ U x hx g.snd :=
  congr(TrivSqZeroExt.snd $(P.stalkDualNumberHom_germ x U hx g)).trans
    (DualNumber.snd_mapRingHom _ _)

theorem bijective_stalkDualNumberHom : Function.Bijective (P.stalkDualNumberHom x) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun s hs ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨U, hxU, g, rfl⟩ := exists_germ_eq (P ⋙ CommRingCat.dualNumber) s
    have h₁ := congr(TrivSqZeroExt.fst $hs)
    have h₂ := congr(TrivSqZeroExt.snd $hs)
    erw [fst_stalkDualNumberHom_germ, fst_zero, ← map_zero (P.germ U x hxU).hom] at h₁
    erw [snd_stalkDualNumberHom_germ, snd_zero, ← map_zero (P.germ U x hxU).hom] at h₂
    obtain ⟨V₁, hxV₁, i₁, j₁, e₁⟩ := P.germ_eq x hxU hxU _ _ h₁
    obtain ⟨V₂, hxV₂, i₂, j₂, e₂⟩ := P.germ_eq x hxU hxU _ _ h₂
    rw [← map_zero (germ (P ⋙ CommRingCat.dualNumber) U x hxU).hom]
    refine germ_ext (P ⋙ CommRingCat.dualNumber) (V₁ ⊓ V₂) (by simp [hxV₁, hxV₂])
      (homOfLE (inf_le_left.trans i₁.le)) (homOfLE (inf_le_left.trans i₁.le)) ?_
    refine TrivSqZeroExt.ext ?_ ?_
    · have := congr(P.map (homOfLE inf_le_left : V₁ ⊓ V₂ ⟶ V₁).op $e₁)
      simp only [map_zero] at this
      refine (CommRingCat.fst_dualNumber_map _ _).trans
        (Eq.trans ?_ (CommRingCat.fst_dualNumber_map _ _).symm)
      refine (Eq.trans ?_ this).trans (map_zero _).symm
      rw [← CommRingCat.comp_apply, ← P.map_comp]
      rfl
    · have := congr(P.map (homOfLE inf_le_right : V₁ ⊓ V₂ ⟶ V₂).op $e₂)
      simp only [map_zero] at this
      refine (CommRingCat.snd_dualNumber_map _ _).trans
        (Eq.trans ?_ (CommRingCat.snd_dualNumber_map _ _).symm)
      refine (Eq.trans ?_ this).trans (map_zero _).symm
      rw [← CommRingCat.comp_apply, ← P.map_comp]
      rfl
  · obtain ⟨U₁, hxU₁, a, ha⟩ := P.exists_germ_eq t.fst
    obtain ⟨U₂, hxU₂, b, hb⟩ := P.exists_germ_eq t.snd
    refine ⟨germ (P ⋙ CommRingCat.dualNumber) (U₁ ⊓ U₂) x (by simp [hxU₁, hxU₂])
      ((P.map (homOfLE inf_le_left).op a, P.map (homOfLE inf_le_right).op b) :
        DualNumber (P.obj (op (U₁ ⊓ U₂)))), ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · erw [fst_stalkDualNumberHom_germ]
      simpa using ha
    · erw [snd_stalkDualNumberHom_germ]
      simpa using hb

instance : IsIso (P.stalkDualNumberHom x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (P.bijective_stalkDualNumberHom x)

variable {P} in
theorem IsSheaf.comp_dualNumber (h : P.IsSheaf) : IsSheaf (P ⋙ CommRingCat.dualNumber) := by
  rw [isSheaf_iff_isSheafUniqueGluing] at h ⊢
  intro ι U sf hsf
  have h₁ : IsCompatible P U fun i ↦ (sf i : DualNumber (P.obj (op (U i)))).fst := fun i j ↦
    (CommRingCat.fst_dualNumber_map _ _).symm.trans <|
      congr(TrivSqZeroExt.fst $(hsf i j)).trans (CommRingCat.fst_dualNumber_map _ _)
  have h₂ : IsCompatible P U fun i ↦ (sf i : DualNumber (P.obj (op (U i)))).snd := fun i j ↦
    (CommRingCat.snd_dualNumber_map _ _).symm.trans <|
      congr(TrivSqZeroExt.snd $(hsf i j)).trans (CommRingCat.snd_dualNumber_map _ _)
  obtain ⟨a, ha, ha'⟩ := h U _ h₁
  obtain ⟨b, hb, hb'⟩ := h U _ h₂
  refine ⟨((a, b) : DualNumber (P.obj (op (iSup U)))), fun i ↦ TrivSqZeroExt.ext ?_ ?_,
    fun s hs ↦ TrivSqZeroExt.ext (ha' _ fun i ↦ ?_) (hb' _ fun i ↦ ?_)⟩
  · exact (CommRingCat.fst_dualNumber_map _ _).trans (ha i)
  · exact (CommRingCat.snd_dualNumber_map _ _).trans (hb i)
  · exact (CommRingCat.fst_dualNumber_map _ _).symm.trans congr(TrivSqZeroExt.fst $(hs i))
  · exact (CommRingCat.snd_dualNumber_map _ _).symm.trans congr(TrivSqZeroExt.snd $(hs i))

end TopCat.Presheaf

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The dual-number thickening `X[ε]` of a locally ringed space `X`: the same underlying space,
with structure sheaf `𝒪_X[ε]`. Its stalks are the dual numbers over the stalks of `X`. -/
noncomputable def dualNumbers (X : LocallyRingedSpace.{u}) : LocallyRingedSpace.{u} where
  carrier := X.carrier
  presheaf := X.presheaf ⋙ CommRingCat.dualNumber
  IsSheaf := X.IsSheaf.comp_dualNumber
  isLocalRing x :=
    have : IsLocalRing (CommRingCat.dualNumber.obj (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalRing (DualNumber _))
    (X.presheaf.stalkDualNumberHom x).hom.domain_isLocalRing

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

/-- The dual-number thickening `X[ε]` of a scheme `X`: the same underlying space with structure
sheaf `𝒪_X[ε] = 𝒪_X ⊕ ε𝒪_X`, the relative spectrum of the sheaf of algebras `𝒪_X[ε]`.
(blueprint: `sk-d-tangent`) -/
noncomputable def dualNumbers : Scheme.{u} where
  __ := X.toLocallyRingedSpace.dualNumbers
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
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    obtain ⟨V, i, hxV, hV⟩ := RingedSpace.isUnit_res_of_isUnit_germ
      X.toLocallyRingedSpace.dualNumbers.toRingedSpace _ _ _ _ hs
    replace hV := isUnit_iff_isUnit_fst.mp hV
    erw [CommRingCat.fst_dualNumber_map] at hV
    have := (hV.map (X.presheaf.germ V x hxV).hom)
    erw [TopCat.Presheaf.germ_res_apply] at this
    exact this

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
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    obtain ⟨V, i, hxV, hV⟩ := RingedSpace.isUnit_res_of_isUnit_germ
      X.dualNumbers.dualNumbers.toRingedSpace _ _ _ _ hs
    replace hV := isUnit_iff_isUnit_fst.mp hV
    erw [CommRingCat.fst_dualNumber_map] at hV
    replace hV := isUnit_iff_isUnit_fst.mp hV
    erw [CommRingCat.fst_dualNumber_map] at hV
    have hV' : IsUnit (X.dualNumbers.presheaf.map i.op g) := by
      refine isUnit_iff_isUnit_fst.mpr ?_
      erw [CommRingCat.fst_dualNumber_map]
      convert hV using 2
      exact (congr(fst $(DualNumber.fst_mulRingHom g)).trans (fst_inl _ _)).symm
    have := (hV'.map (X.dualNumbers.presheaf.germ V x hxV).hom)
    erw [TopCat.Presheaf.germ_res_apply] at this
    exact this

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
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change (DualNumber.mulRingHom (inl a) : DualNumber (DualNumber Γ(X, U))) = inl (inl a)
  ext <;> simp

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
  Over.homMk S.dualNumbersMul S.dualNumbersMul_comp_proj

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
