/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Truncations of the reduction tower

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. For an object `K` of `D(J, R)` write `K_n = K ⊗ᴸ R/Iⁿ` for its
reductions (`DerivedCategory.derivedCompletionDiagram`) and `τ^{≤ m}`, `τ^{≥ m + 1}` for the
canonical truncations of `D(J, R)`. This file compares the levelwise truncations
`n ↦ τ^{≤ m} K_n`, `n ↦ τ^{≥ m + 1} K_n` of the reduction tower with the reduction towers of the
truncations `τ^{≤ m} K`, `τ^{≥ m + 1} K` (blueprint `prop-weil-pbc-levelwise-truncations`).

Reduction is a triangulated functor, so it sends the truncation triangle of `K` to a triangle
`(τ^{≤ m} K)_n ⟶ K_n ⟶ (τ^{≥ m + 1} K)_n ⟶`. Its first term always lies in degrees `≤ m`
(`DerivedCategory.isLE_derivedCompletionDiagram_obj`), but its third term only lies in degrees
`≥ m` (`DerivedCategory.isGE_derivedCompletionDiagram_obj`): its cohomology in degree `m` is the
`ϖⁿ`-torsion of `𝓗^{m + 1}(K)`, the Tor term of the Künneth spectral sequence. The
*Tor-compatibility condition* `DerivedCategory.IsTorCompatibleAt` asks that this term vanishes;
it holds when `ϖ` acts injectively on `𝓗^{m + 1}(K)`
(`DerivedCategory.isTorCompatibleAt_of_mono`). Under this condition the triangle is the
truncation triangle of `K_n`, so the levelwise truncations are the reductions of the truncations
(`DerivedCategory.exists_iso_derivedCompletionDiagram_truncLE`,
`DerivedCategory.exists_iso_derivedCompletionDiagram_truncGE`); in particular they are adic
towers.

Finally `DerivedCategory.derivedComplete_truncLE_of_isLE` shows that the truncation `τ^{≤ m} K` of
a derived complete object is derived complete as soon as the derived limit of its reduction tower
lies in degrees `≤ m` and reduces to it: this is how the integral truncations of
`thm-weil-pbc-integral-truncations` are identified with the derived limits of the levelwise
truncations.

## Implementation notes

The blueprint works in the derived category `D(Tow_A(T))` of towers, with `K_n` an object over
`P_n = A/Iⁿ⁺¹` and normalization isomorphisms `K_{n+1} ⊗ᴸ_{P_{n+1}} P_n ≅ K_n`. The project
models the reduction tower inside the single category `D(J, R)`, the reductions being
`K ⊗ᴸ_R R/Iⁿ` (`DerivedCategory.derivedCompletionDiagram`); a tower is adic when it is isomorphic
to the reduction tower of an object. In this model the Tor-compatibility condition (1) of the
blueprint, which asks that the Künneth Tor terms of `𝓗^q(K_{n+1})`, `q ≥ m + 1`, vanish, becomes
the vanishing of the Tor term `𝓗^m((τ^{≥ m + 1} K)_n) = 𝓗^{m + 1}(K)[ϖⁿ]`; it is exactly the
condition under which the reduced truncation triangle is a truncation triangle, which is how the
blueprint's proof uses condition (1).

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace CategoryTheory.Pretriangulated.IsHomotopyLimit

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A cone over a tower maps to a homotopy limit of the tower compatibly with the legs. The map
is not unique. -/
lemma exists_lift {F : ℕᵒᵖ ⥤ C} {c : Cone F} (hc : IsHomotopyLimit c) (s : Cone F) :
    ∃ φ : s.pt ⟶ c.pt, ∀ n : ℕ, φ ≫ c.π.app (op n) = s.π.app (op n) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  obtain ⟨φ, hφ⟩ := Triangle.coyoneda_exact₂ _ hT (Fan.IsLimit.lift hP fun n ↦ s.π.app (op n))
    (by
      change _ ≫ (𝟙 P.pt - towerShift hP) = 0
      rw [Preadditive.comp_sub, Category.comp_id, lift_comp_towerShift, sub_self])
  refine ⟨φ, fun n ↦ ?_⟩
  have := hφ =≫ P.proj n
  simp only [Fan.IsLimit.fac, Triangle.mk_mor₁, assoc] at this
  exact this.symm

end CategoryTheory.Pretriangulated.IsHomotopyLimit

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

local instance : IsIso (sheafTensorStructure J R).ε := (sheafTensorStructure J R).isIso_ε

set_option hygiene false in
/-- The derived category `D(J, R)`. -/
local notation "𝐃" => DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))

section Reduction

variable (J) in
/-- The reduction `K ↦ K ⊗ᴸ R/Iⁿ` as a triangulated functor of `K`. Its value at `K` is the
`n`-th term of `DerivedCategory.derivedCompletionDiagram J I K`. -/
noncomputable abbrev reductionFunctor (I : Ideal R) (n : ℕ) : 𝐃 ⥤ 𝐃 :=
  (curriedTensor 𝐃).flip.obj ((quotPowFunctor J I).obj (op n))

variable (J) in
/-- The morphism of reduction towers `K_n ⟶ K'_n` induced by a morphism `f : K ⟶ K'`. -/
noncomputable def derivedCompletionDiagramMap (I : Ideal R) {K K' : 𝐃} (f : K ⟶ K') :
    derivedCompletionDiagram J I K ⟶ derivedCompletionDiagram J I K' :=
  Functor.whiskerLeft (quotPowFunctor J I) ((curriedTensor 𝐃).map f)

lemma derivedCompletionDiagramMap_app (I : Ideal R) {K K' : 𝐃} (f : K ⟶ K') (n : ℕ) :
    (derivedCompletionDiagramMap J I f).app (op n) = (reductionFunctor J I n).map f :=
  rfl

@[simp]
lemma derivedCompletionDiagramMap_id (I : Ideal R) (K : 𝐃) :
    derivedCompletionDiagramMap J I (𝟙 K) = 𝟙 _ := by
  ext n
  exact (reductionFunctor J I (unop n)).map_id K

@[reassoc]
lemma derivedCompletionDiagramMap_comp (I : Ideal R) {K K' K'' : 𝐃} (f : K ⟶ K')
    (g : K' ⟶ K'') :
    derivedCompletionDiagramMap J I (f ≫ g) =
      derivedCompletionDiagramMap J I f ≫ derivedCompletionDiagramMap J I g := by
  ext n
  exact (reductionFunctor J I (unop n)).map_comp f g

/-- The reduction maps `K ⟶ K_n` are natural in `K`. -/
@[reassoc]
lemma derivedCompletionCone_π_naturality (I : Ideal R) {K K' : 𝐃} (f : K ⟶ K') (n : ℕ) :
    f ≫ (derivedCompletionCone J I K').π.app (op n) =
      (derivedCompletionCone J I K).π.app (op n) ≫ (derivedCompletionDiagramMap J I f).app (op n)
    := by
  change f ≫ (ρ_ K').inv ≫ K' ◁ _ = ((ρ_ K).inv ≫ K ◁ _) ≫ f ▷ _
  rw [rightUnitor_inv_naturality_assoc, assoc, whisker_exchange]

end Reduction

section Linear

variable (m : ℤ)

/-- The truncation `τ^{≤ m}` of `D(J, R)` is `R`-linear on morphisms. -/
lemma truncLE_map_smul {X Y : 𝐃} (r : R) (f : X ⟶ Y) :
    (TStructure.t.truncLE m).map (r • f) = r • (TStructure.t.truncLE m).map f :=
  TStructure.t.to_truncLE_obj_ext (by
    rw [(TStructure.t.truncLEι m).naturality, Linear.smul_comp,
      (TStructure.t.truncLEι m).naturality, Functor.id_map, Functor.id_map, Linear.comp_smul])

/-- The truncation `τ^{≥ m}` of `D(J, R)` is `R`-linear on morphisms. -/
lemma truncGE_map_smul {X Y : 𝐃} (r : R) (f : X ⟶ Y) :
    (TStructure.t.truncGE m).map (r • f) = r • (TStructure.t.truncGE m).map f :=
  TStructure.t.from_truncGE_obj_ext (by
    rw [← (TStructure.t.truncGEπ m).naturality, Linear.comp_smul,
      ← (TStructure.t.truncGEπ m).naturality, Functor.id_map, Functor.id_map, Linear.smul_comp])

/-- The truncations of an object on which `ϖ` acts invertibly are again such objects. -/
lemma smulInvertible_truncLE {ϖ : R} {X : 𝐃} (hX : smulInvertible J ϖ X) :
    smulInvertible J ϖ ((TStructure.t.truncLE m).obj X) := by
  have : IsIso (ϖ • 𝟙 X) := hX
  change IsIso (ϖ • 𝟙 _)
  rw [← CategoryTheory.Functor.map_id, ← truncLE_map_smul]
  infer_instance

/-- `ϖⁿ` acts by zero on the truncation `τ^{≤ m}` of an object killed by `ϖⁿ`. -/
lemma smul_id_truncLE_obj {r : R} {X : 𝐃} (hX : r • 𝟙 X = 0) :
    r • 𝟙 ((TStructure.t.truncLE m).obj X) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← truncLE_map_smul, hX, Functor.map_zero]

/-- `ϖⁿ` acts by zero on the truncation `τ^{≥ m}` of an object killed by `ϖⁿ`. -/
lemma smul_id_truncGE_obj {r : R} {X : 𝐃} (hX : r • 𝟙 X = 0) :
    r • 𝟙 ((TStructure.t.truncGE m).obj X) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← truncGE_map_smul, hX, Functor.map_zero]

end Linear

section TStructure

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

include hϖ hI in
/-- Reduction preserves the objects `≤ m`: `K_n` is the cone of `ϖⁿ : K ⟶ K`. -/
lemma isLE_derivedCompletionDiagram_obj (K : 𝐃) (m : ℤ) [TStructure.t.IsLE K m] (n : ℕ) :
    TStructure.t.IsLE ((derivedCompletionDiagram J I K).obj (op n)) m := by
  have hT := rot_of_distTriang _ (tensorQuotPowTriangle_distinguished hϖ hI K n)
  have h₁ : TStructure.t.IsLE (tensorQuotPowTriangle hϖ hI K n).obj₁ m :=
    TStructure.t.isLE_of_iso (unitIso K) m
  have h₃ : TStructure.t.IsLE ((tensorQuotPowTriangle hϖ hI K n).obj₁⟦(1 : ℤ)⟧) m :=
    have := TStructure.t.isLE_shift (tensorQuotPowTriangle hϖ hI K n).obj₁ m 1 (m - 1)
    TStructure.t.isLE_of_le _ (m - 1) m
  exact TStructure.t.isLE₂ _ hT m h₁ h₃

include hϖ hI in
/-- Reduction sends the objects `≥ m + 1` to objects `≥ m`: `K_n` is the cone of
`ϖⁿ : K ⟶ K`. -/
lemma isGE_derivedCompletionDiagram_obj (K : 𝐃) (m : ℤ) [TStructure.t.IsGE K (m + 1)]
    (n : ℕ) : TStructure.t.IsGE ((derivedCompletionDiagram J I K).obj (op n)) m := by
  have hT := rot_of_distTriang _ (tensorQuotPowTriangle_distinguished hϖ hI K n)
  have : TStructure.t.IsGE (tensorQuotPowTriangle hϖ hI K n).obj₁ (m + 1) :=
    TStructure.t.isGE_of_iso (unitIso K) (m + 1)
  have : TStructure.t.IsGE (tensorQuotPowTriangle hϖ hI K n).obj₁ m :=
    TStructure.t.isGE_of_ge _ m (m + 1)
  have h₃ : TStructure.t.IsGE ((tensorQuotPowTriangle hϖ hI K n).obj₁⟦(1 : ℤ)⟧) m :=
    TStructure.t.isGE_shift (tensorQuotPowTriangle hϖ hI K n).obj₁ (m + 1) 1 m
  exact TStructure.t.isGE₂ _ hT m this h₃

variable (J I) in
/-- The *Tor-compatibility condition* of blueprint `prop-weil-pbc-levelwise-truncations` for an
object `K` of `D(J, R)` in degree `m`: for every `n`, the reduction `(τ^{≥ m + 1} K)_n` of the
truncation `τ^{≥ m + 1} K` still lies in degrees `≥ m + 1`.

The reduction `(τ^{≥ m + 1} K)_n` always lies in degrees `≥ m`
(`DerivedCategory.isGE_derivedCompletionDiagram_obj`), and for `I = (ϖ)` its cohomology in
degree `m` is the `ϖⁿ`-torsion of `𝓗^{m + 1}(K)`: it is the Tor term
`Tor₁(𝓗^{m + 1}(K), R/Iⁿ)` of the Künneth spectral sequence, which the blueprint's condition (1)
asks to vanish. The condition holds when `ϖ` acts injectively on `𝓗^{m + 1}(K)`
(`DerivedCategory.isTorCompatibleAt_of_mono`), for instance when `𝓗^{m + 1}(K)` is
`ϖ`-torsion free. It is exactly what makes the reduction of the truncation triangle of `K` a
truncation triangle of `K_n`. -/
def IsTorCompatibleAt (K : 𝐃) (m : ℤ) : Prop :=
  ∀ n : ℕ, TStructure.t.IsGE
    ((derivedCompletionDiagram J I ((TStructure.t.truncGE (m + 1)).obj K)).obj (op n)) (m + 1)

/-- Multiplication by `ϖⁿ` on `𝓗^q(K)` is injective if multiplication by `ϖ` is. -/
lemma mono_homologyFunctor_map_pow_smul {X : 𝐃} (q : ℤ)
    (h : Mono ((homologyFunctor _ q).map (ϖ • 𝟙 X))) (n : ℕ) :
    Mono ((homologyFunctor _ q).map (ϖ ^ n • 𝟙 X)) := by
  induction n with
  | zero =>
    rw [pow_zero, one_smul, CategoryTheory.Functor.map_id]
    infer_instance
  | succ n ih =>
    have e : ϖ ^ (n + 1) • 𝟙 X = (ϖ ^ n • 𝟙 X) ≫ (ϖ • 𝟙 X) := by
      rw [Linear.smul_comp, id_comp, smul_smul, pow_succ]
    rw [e, Functor.map_comp]
    exact mono_comp _ _

include hϖ hI in
/-- Blueprint `prop-weil-pbc-levelwise-truncations`, sufficient condition for the
Tor-compatibility: if `ϖ` acts injectively on `𝓗^{m + 1}(K)`, then `K` is Tor-compatible in
degree `m`. Indeed `𝓗^m((τ^{≥ m + 1} K)_n)` is the kernel of `ϖⁿ` on `𝓗^{m + 1}(K)`. -/
lemma isTorCompatibleAt_of_mono (K : 𝐃) (m : ℤ)
    (h : Mono ((homologyFunctor _ (m + 1)).map (ϖ • 𝟙 K))) : IsTorCompatibleAt J I K m := by
  intro n
  set Y := (TStructure.t.truncGE (m + 1)).obj K
  set T := tensorQuotPowTriangle hϖ hI Y n
  have hT : T ∈ distTriang _ := tensorQuotPowTriangle_distinguished hϖ hI Y n
  have hY : TStructure.t.IsGE ((derivedCompletionDiagram J I Y).obj (op n)) m :=
    isGE_derivedCompletionDiagram_obj hϖ hI Y m n
  -- `ϖ` acts injectively on `𝓗^{m + 1}(Y)`
  have hπ : IsIso ((homologyFunctor _ (m + 1)).map ((TStructure.t.truncGEπ (m + 1)).app K)) :=
    isIso_homologyFunctor_map_truncGEπ_app K (m + 1) (m + 1) le_rfl
  have hYϖ : Mono ((homologyFunctor _ (m + 1)).map (ϖ • 𝟙 Y)) := by
    have e : (TStructure.t.truncGEπ (m + 1)).app K ≫ (ϖ • 𝟙 Y) =
        (ϖ • 𝟙 K) ≫ (TStructure.t.truncGEπ (m + 1)).app K := by
      rw [Linear.comp_smul, Linear.smul_comp, comp_id, id_comp]
    have e' := (homologyFunctor _ (m + 1)).congr_map e
    rw [Functor.map_comp, Functor.map_comp] at e'
    have e'' : (homologyFunctor _ (m + 1)).map (ϖ • 𝟙 Y) = inv ((homologyFunctor _ (m + 1)).map
        ((TStructure.t.truncGEπ (m + 1)).app K)) ≫ (homologyFunctor _ (m + 1)).map (ϖ • 𝟙 K) ≫
          (homologyFunctor _ (m + 1)).map ((TStructure.t.truncGEπ (m + 1)).app K) := by
      rw [← e', IsIso.inv_hom_id_assoc]
    rw [e'']
    infer_instance
  -- the first map of `T` is `ϖⁿ`
  have hmor₁ : T.mor₁ = (unitIso Y).inv ≫ (ϖ ^ n • 𝟙 Y) ≫ (unitIso Y).hom := by
    change Y ◁ (quotPowTriangle J hϖ hI n).mor₁ = _
    rw [quotPowTriangle_mor₁, MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id,
      Linear.smul_comp, id_comp, Linear.comp_smul, Iso.inv_hom_id]
    rfl
  have hmono : Mono ((homologyFunctor _ (m + 1)).map T.mor₁) := by
    rw [hmor₁, Functor.map_comp, Functor.map_comp]
    have := mono_homologyFunctor_map_pow_smul (m + 1) hYϖ n
    infer_instance
  -- the connecting map `𝓗^m(Y_n) ⟶ 𝓗^{m + 1}(Y ⊗ R)` is a monomorphism and zero
  have hδ₀ : HomologySequence.δ T m (m + 1) = 0 := by
    rw [← cancel_mono ((homologyFunctor _ (m + 1)).map T.mor₁), zero_comp]
    exact HomologySequence.δ_comp T hT m (m + 1)
  have hY₂ : TStructure.t.IsGE T.obj₂ (m + 1) := TStructure.t.isGE_of_iso (unitIso Y) (m + 1)
  have hδ : Mono (HomologySequence.δ T m (m + 1)) :=
    (HomologySequence.exact₃ T hT m (m + 1)).mono_g
      ((isZero_of_isGE T.obj₂ (m + 1) m (by lia)).eq_of_src _ _)
  rw [hδ₀] at hδ
  have hZ : IsZero ((homologyFunctor _ m).obj T.obj₃) :=
    IsZero.of_mono_zero ((homologyFunctor _ m).obj T.obj₃)
    ((homologyFunctor _ (m + 1)).obj T.obj₁)
  refine (isGE_iff _ (m + 1)).2 fun i hi ↦ ?_
  rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp hi) with hi | rfl
  · exact isZero_of_isGE _ m i hi
  · exact hZ

include hϖ hI in
/-- Under the Tor-compatibility condition, the reduction of the truncation triangle of `K` at
level `n` is isomorphic to the truncation triangle of `K_n`, by an isomorphism which is the
identity of `K_n`. -/
private lemma exists_iso_mapTriangle_triangleLEGE {K : 𝐃} {m : ℤ}
    (hK : IsTorCompatibleAt J I K m) (n : ℕ) :
    ∃ e : (reductionFunctor J I n).mapTriangle.obj
        ((TStructure.t.triangleLEGE m (m + 1) rfl).obj K) ≅
      (TStructure.t.triangleLEGE m (m + 1) rfl).obj ((derivedCompletionDiagram J I K).obj (op n)),
      e.hom.hom₂ = 𝟙 _ := by
  have h₀ : TStructure.t.IsLE
      ((derivedCompletionDiagram J I ((TStructure.t.truncLE m).obj K)).obj (op n)) m :=
    isLE_derivedCompletionDiagram_obj hϖ hI _ m n
  exact TStructure.t.triangle_iso_exists ((reductionFunctor J I n).map_distinguished _
    (TStructure.t.triangleLEGE_distinguished m (m + 1) rfl K))
    (TStructure.t.triangleLEGE_distinguished m (m + 1) rfl _) (Iso.refl _) m (m + 1) h₀ (hK n)
    (TStructure.t.isLE_truncLE_obj _ m m le_rfl)
    (TStructure.t.isGE_truncGE_obj _ (m + 1) (m + 1) le_rfl)

include hϖ hI in
/-- Blueprint `prop-weil-pbc-levelwise-truncations` (i), for `τ^{≤ m}`: under the
Tor-compatibility condition, the levelwise truncation `n ↦ τ^{≤ m} K_n` of the reduction tower
of `K` is the reduction tower of `τ^{≤ m} K`, hence an adic tower: there is an isomorphism of
towers `(τ^{≤ m} K)_n ≅ τ^{≤ m} K_n`, compatible with the transition maps and identifying the
reduction of `τ^{≤ m} K ⟶ K` with `τ^{≤ m} K_n ⟶ K_n`. -/
theorem exists_iso_derivedCompletionDiagram_truncLE {K : 𝐃} {m : ℤ}
    (hK : IsTorCompatibleAt J I K m) :
    ∃ e : derivedCompletionDiagram J I ((TStructure.t.truncLE m).obj K) ≅
        derivedCompletionDiagram J I K ⋙ TStructure.t.truncLE m,
      ∀ n : ℕ, e.hom.app (op n) ≫ (TStructure.t.truncLEι m).app
          ((derivedCompletionDiagram J I K).obj (op n)) =
        (derivedCompletionDiagramMap J I ((TStructure.t.truncLEι m).app K)).app (op n) := by
  have hle (n : ℕᵒᵖ) : TStructure.t.IsLE
      ((derivedCompletionDiagram J I ((TStructure.t.truncLE m).obj K)).obj n) m :=
    isLE_derivedCompletionDiagram_obj hϖ hI _ m n.unop
  let a (n : ℕᵒᵖ) := TStructure.t.liftTruncLE
    ((derivedCompletionDiagramMap J I ((TStructure.t.truncLEι m).app K)).app n) m
  have ha (n : ℕᵒᵖ) : IsIso (a n) := by
    obtain ⟨e, he⟩ := exists_iso_mapTriangle_triangleLEGE hϖ hI hK n.unop
    have h₁ := e.hom.comm₁
    rw [he, comp_id] at h₁
    have : a n = e.hom.hom₁ := TStructure.t.to_truncLE_obj_ext (by
      rw [TStructure.t.liftTruncLE_ι]
      exact h₁)
    rw [this]
    infer_instance
  refine ⟨NatIso.ofComponents (fun n ↦ asIso (a n)) (fun {n n'} φ ↦ ?_),
    fun n ↦ TStructure.t.liftTruncLE_ι _ _⟩
  apply TStructure.t.to_truncLE_obj_ext
  simp only [asIso_hom, Functor.comp_map, assoc, a]
  erw [TStructure.t.liftTruncLE_ι, (TStructure.t.truncLEι m).naturality,
    TStructure.t.liftTruncLE_ι_assoc]
  exact (derivedCompletionDiagramMap J I ((TStructure.t.truncLEι m).app K)).naturality φ

include hϖ hI in
/-- Blueprint `prop-weil-pbc-levelwise-truncations` (i), for `τ^{≥ m + 1}`: under the
Tor-compatibility condition, the levelwise truncation `n ↦ τ^{≥ m + 1} K_n` of the reduction
tower of `K` is the reduction tower of `τ^{≥ m + 1} K`, hence an adic tower: there is an
isomorphism of towers `(τ^{≥ m + 1} K)_n ≅ τ^{≥ m + 1} K_n`, compatible with the transition maps
and identifying the reduction of `K ⟶ τ^{≥ m + 1} K` with `K_n ⟶ τ^{≥ m + 1} K_n`. -/
theorem exists_iso_derivedCompletionDiagram_truncGE {K : 𝐃} {m : ℤ}
    (hK : IsTorCompatibleAt J I K m) :
    ∃ e : derivedCompletionDiagram J I ((TStructure.t.truncGE (m + 1)).obj K) ≅
        derivedCompletionDiagram J I K ⋙ TStructure.t.truncGE (m + 1),
      ∀ n : ℕ, (TStructure.t.truncGEπ (m + 1)).app
          ((derivedCompletionDiagram J I K).obj (op n)) ≫ e.inv.app (op n) =
        (derivedCompletionDiagramMap J I ((TStructure.t.truncGEπ (m + 1)).app K)).app (op n) := by
  have hge (n : ℕᵒᵖ) : TStructure.t.IsGE
      ((derivedCompletionDiagram J I ((TStructure.t.truncGE (m + 1)).obj K)).obj n) (m + 1) :=
    hK n.unop
  let b (n : ℕᵒᵖ) := TStructure.t.descTruncGE
    ((derivedCompletionDiagramMap J I ((TStructure.t.truncGEπ (m + 1)).app K)).app n) (m + 1)
  have hb (n : ℕᵒᵖ) : IsIso (b n) := by
    obtain ⟨e, he⟩ := exists_iso_mapTriangle_triangleLEGE hϖ hI hK n.unop
    have he' : e.inv.hom₂ = 𝟙 _ := by
      rw [← cancel_epi e.hom.hom₂, ← comp_hom₂, e.hom_inv_id, he]
      simp
    have h₂ := e.inv.comm₂
    rw [he', id_comp] at h₂
    have : b n = e.inv.hom₃ := TStructure.t.from_truncGE_obj_ext (by
      rw [TStructure.t.π_descTruncGE]
      exact h₂.symm)
    rw [this]
    infer_instance
  refine ⟨(NatIso.ofComponents (fun n ↦ asIso (b n)) (fun {n n'} φ ↦ ?_)).symm,
    fun n ↦ TStructure.t.π_descTruncGE _ _⟩
  apply TStructure.t.from_truncGE_obj_ext
  simp only [asIso_hom, Functor.comp_map, b]
  erw [← (TStructure.t.truncGEπ (m + 1)).naturality_assoc, TStructure.t.π_descTruncGE,
    TStructure.t.π_descTruncGE_assoc]
  exact (derivedCompletionDiagramMap J I ((TStructure.t.truncGEπ (m + 1)).app K)).naturality φ

/-- Blueprint `prop-weil-pbc-levelwise-truncations` (iii), for `τ^{≤ m}`: the levelwise
truncation `τ^{≤ m} K_n` has the cohomology of `K_n` in degrees `≤ m`, through
`τ^{≤ m} K_n ⟶ K_n`, and none above. This holds without the Tor-compatibility condition. -/
lemma homologyFunctor_truncLE_derivedCompletionDiagram_obj (K : 𝐃) (m : ℤ) (n : ℕ) (i : ℤ) :
    (i ≤ m → IsIso ((homologyFunctor _ i).map ((TStructure.t.truncLEι m).app
      ((derivedCompletionDiagram J I K).obj (op n))))) ∧
    (m < i → IsZero ((homologyFunctor _ i).obj
      ((TStructure.t.truncLE m).obj ((derivedCompletionDiagram J I K).obj (op n))))) :=
  ⟨fun hi ↦ isIso_homologyFunctor_map_truncLTι_app _ (m + 1) i (by lia),
    fun hi ↦ isZero_of_isLE _ m i hi⟩

/-- Blueprint `prop-weil-pbc-levelwise-truncations` (iii), for `τ^{≥ m + 1}`: the levelwise
truncation `τ^{≥ m + 1} K_n` has the cohomology of `K_n` in degrees `≥ m + 1`, through
`K_n ⟶ τ^{≥ m + 1} K_n`, and none below. This holds without the Tor-compatibility
condition. -/
lemma homologyFunctor_truncGE_derivedCompletionDiagram_obj (K : 𝐃) (m : ℤ) (n : ℕ) (i : ℤ) :
    (m + 1 ≤ i → IsIso ((homologyFunctor _ i).map ((TStructure.t.truncGEπ (m + 1)).app
      ((derivedCompletionDiagram J I K).obj (op n))))) ∧
    (i ≤ m → IsZero ((homologyFunctor _ i).obj
      ((TStructure.t.truncGE (m + 1)).obj ((derivedCompletionDiagram J I K).obj (op n))))) :=
  ⟨fun hi ↦ isIso_homologyFunctor_map_truncGEπ_app _ (m + 1) i hi,
    fun hi ↦ isZero_of_isGE _ (m + 1) i (by lia)⟩

end TStructure

section Complete

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

include hϖ hI in
/-- An object whose first reduction vanishes is one on which `ϖ` acts invertibly. -/
lemma smulInvertible_of_isZero_derivedCompletionDiagram_obj_one {D : 𝐃}
    (hD : IsZero ((derivedCompletionDiagram J I D).obj (op 1))) : smulInvertible J ϖ D := by
  have h₁ : IsIso (tensorQuotPowTriangle hϖ hI D 1).mor₁ :=
    (Triangle.isZero₃_iff_isIso₁ _ (tensorQuotPowTriangle_distinguished hϖ hI D 1)).1 hD
  have hmor₁ : (tensorQuotPowTriangle hϖ hI D 1).mor₁ =
      (unitIso D).inv ≫ (ϖ • 𝟙 D) ≫ (unitIso D).hom := by
    change D ◁ (quotPowTriangle J hϖ hI 1).mor₁ = _
    rw [quotPowTriangle_mor₁, MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id,
      Linear.smul_comp, id_comp, Linear.comp_smul, Iso.inv_hom_id, pow_one]
    rfl
  have e : ϖ • 𝟙 D = (unitIso D).hom ≫ (tensorQuotPowTriangle hϖ hI D 1).mor₁ ≫
      (unitIso D).inv := by
    rw [hmor₁]
    simp
  change IsIso (ϖ • 𝟙 D)
  rw [e]
  infer_instance

include hϖ hI in
/-- The truncation `τ^{≤ m} K` of a derived complete object `K` is derived complete as soon as
it maps to a derived complete object `Q` lying in degrees `≤ m` by a morphism which is an
isomorphism on the first reductions. This applies to `Q` the derived limit of the reduction
tower of `τ^{≤ m} K`, when it lies in degrees `≤ m` (blueprint
`thm-weil-pbc-integral-truncations`).

The cone `D` of `φ` is `≤ m` and `ϖ` acts invertibly on it, so its connecting map to
`(τ^{≤ m} K)⟦1⟧` vanishes (it factors through `τ^{≥ m + 1} K`, as `K⟦1⟧` is derived complete);
then `D` is a retract of the derived complete `Q`, hence zero. -/
theorem derivedComplete_truncLE_of_isLE {K : 𝐃} (hK : derivedComplete J I K) {m : ℤ} {Q : 𝐃}
    (hQ : derivedComplete J I Q) [TStructure.t.IsLE Q m]
    (φ : (TStructure.t.truncLE m).obj K ⟶ Q)
    (hφ : IsIso ((derivedCompletionDiagramMap J I φ).app (op 1))) :
    derivedComplete J I ((TStructure.t.truncLE m).obj K) := by
  have := isTriangulated_derivedComplete (J := J) hϖ hI
  have hϖI := mem_of_eq_span hI
  obtain ⟨D, g, δ, hT⟩ := distinguished_cocone_triangle φ
  have hDinv : smulInvertible J ϖ D := smulInvertible_of_isZero_derivedCompletionDiagram_obj_one
    hϖ hI ((Triangle.isZero₃_iff_isIso₁ _ ((reductionFunctor J I 1).map_distinguished _ hT)).2 hφ)
  have hDle : TStructure.t.IsLE D m := by
    have : TStructure.t.IsLE (((TStructure.t.truncLE m).obj K)⟦(1 : ℤ)⟧) m :=
      have := TStructure.t.isLE_shift ((TStructure.t.truncLE m).obj K) m 1 (m - 1)
      TStructure.t.isLE_of_le _ (m - 1) m
    exact TStructure.t.isLE₂ _ (rot_of_distTriang _ hT) m (inferInstanceAs (TStructure.t.IsLE Q m))
      this
  have hδ : δ = 0 := by
    have hK₁ : derivedComplete J I (K⟦(1 : ℤ)⟧) := (derivedComplete J I).le_shift 1 K hK
    have h₀ : δ ≫ ((TStructure.t.truncLEι m).app K)⟦(1 : ℤ)⟧' = 0 :=
      rightOrthogonal_of_derivedComplete hϖI hK₁ _ hDinv
    obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₃ _
      (rot_of_distTriang _ (TStructure.t.triangleLEGE_distinguished m (m + 1) rfl K)) δ (by
        change δ ≫ (-((TStructure.t.truncLEι m).app K)⟦(1 : ℤ)⟧') = 0
        rw [Preadditive.comp_neg, h₀, neg_zero])
    have hg₀ : g' = 0 := TStructure.t.zero_of_isLE_of_isGE g' m (m + 1) (by lia) hDle
      (TStructure.t.isGE_truncGE_obj _ (m + 1) (m + 1) le_rfl)
    rw [hg', hg₀, zero_comp]
  obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₃ _ hT (𝟙 D) (by
    change 𝟙 D ≫ δ = 0
    rw [id_comp, hδ])
  have hs₀ : s = 0 := rightOrthogonal_of_derivedComplete hϖI hQ s hDinv
  have hDz : IsZero D := by
    rw [IsZero.iff_id_eq_zero, hs, hs₀, zero_comp]
  have : IsIso φ := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hDz
  rw [derivedComplete_iff_rightOrthogonal hϖ hI] at hQ ⊢
  intro Z f hZ
  rw [← cancel_mono φ, zero_comp]
  exact hQ _ hZ

include hϖ hI in
/-- If `K` and its truncation `τ^{≤ m} K` are derived complete, so is `τ^{≥ m + 1} K`: derived
complete objects form a triangulated subcategory. -/
lemma derivedComplete_truncGE {K : 𝐃} (hK : derivedComplete J I K) {m : ℤ}
    (hm : derivedComplete J I ((TStructure.t.truncLE m).obj K)) :
    derivedComplete J I ((TStructure.t.truncGE (m + 1)).obj K) := by
  have := isTriangulated_derivedComplete (J := J) hϖ hI
  have : (derivedComplete J I).IsClosedUnderIsomorphisms := by
    rw [derivedComplete_eq_rightOrthogonal hϖ hI]
    infer_instance
  exact (derivedComplete J I).ext_of_isTriangulatedClosed₂ _
    (rot_of_distTriang _ (TStructure.t.triangleLEGE_distinguished m (m + 1) rfl K)) hK
    ((derivedComplete J I).le_shift 1 _ hm)

end Complete

end DerivedCategory
