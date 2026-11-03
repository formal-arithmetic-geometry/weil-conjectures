/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Realization of bounded dual pairings

Source: the bounded perfect dual argument in the internal-Hom stability proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v w u t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{v} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [MonoidalClosed A] [BraidedCategory A]
  {B : Type t} [Category.{w} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B] [BraidedCategory B]
  [HasDerivedCategory.{w} B] [Abelian.HasFunctorialFlatResolution B]

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
local instance : HasColimitsOfSize.{0, 0} B := hasColimitsOfSizeShrink B

private theorem derived_pairing (K L : CochainComplex B ℤ)
    (a b c d : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [L.IsStrictlyGE c] [L.IsStrictlyLE d]
    (hK : ∀ n : ℤ, IsDualizable (K.X n))
    (hL : ∀ n : ℤ, IsDualizable (L.X n)) [ExactPairing K L] :
    Nonempty (ExactPairing (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)) := by
  let H := HomotopyCategory.quotient B (.up ℤ)
  let X : (HomotopyCategory.quasiIso B (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj K, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat K a b (fun n ↦ (hK n).flat))⟩
  let Y : (HomotopyCategory.quasiIso B (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj L, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat L c d (fun n ↦ (hL n).flat))⟩
  let : ExactPairing ((ObjectProperty.ι _).obj X) ((ObjectProperty.ι _).obj Y) :=
    ExactPairing.map H K L
  let : ExactPairing X Y := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) X Y
  let := Functor.Monoidal.ofLaxMonoidal (DerivedCategory.kFlatQh B)
  let : ExactPairing ((DerivedCategory.kFlatQh B).obj X)
      ((DerivedCategory.kFlatQh B).obj Y) := ExactPairing.map (DerivedCategory.kFlatQh B) X Y
  exact ⟨exactPairingCongr (X' := (DerivedCategory.kFlatQh B).obj X)
    (Y' := (DerivedCategory.kFlatQh B).obj Y)
    ((DerivedCategory.quotientCompQhIso B).app K).symm
    ((DerivedCategory.quotientCompQhIso B).app L).symm⟩

/-- An additive strong monoidal realization preserving small coproducts carries a
bounded complex and its chosen termwise dual to an exact pairing after localization.
Source: current blueprint, internal-Hom stability proof, paragraph 2, perfect duality
(blueprint: lem-sfb-realized-bounded-dual-pairing).

Proof: The signed termwise dual has the reversed bounds and its terms are dualizable.
Realization preserves zero objects and dualizable objects, and its monoidal functor
on complexes preserves the chain-level evaluation and coevaluation. Both realized
complexes are bounded complexes of flat objects, hence K-flat. Map the exact pairing
through the monoidal homotopy quotient, lift it to the full K-flat subcategory, and
map through the strong monoidal restriction of the derived quotient. The quotient
comparison isomorphisms identify its objects with the specified derived images.
This argument uses actual pairing maps and both triangle identities, including for
zero complexes and empty degree intervals. -/
theorem realized_bounded_dual_pairing (G : A ⥤ B) [G.Additive] [G.Monoidal]
    [PreservesColimitsOfSize.{0, 0} G] (F : CochainComplex A ℤ)
    (a b : ℤ) [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ n : ℤ, HasRightDual (F.X n)] :
    Nonempty (ExactPairing
      (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj F))
      (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj F.rightDual))) := by
  let K : CochainComplex B ℤ := (G.mapHomologicalComplex (.up ℤ)).obj F
  let L : CochainComplex B ℤ := (G.mapHomologicalComplex (.up ℤ)).obj F.rightDual
  have hK (n : ℤ) : IsDualizable (K.X n) :=
    (show IsDualizable (F.X n) from ⟨inferInstance⟩).map G
  have hL (n : ℤ) : IsDualizable (L.X n) :=
    (show IsDualizable (F.rightDual.X n) from
      ⟨{ rightDual := F.X (-n),
         exact := (BraidedCategory.exactPairing_swap (F.X (-n)) (F.X (-n))ᘁ :) }⟩).map G
  have : K.IsStrictlyGE a := (K.isStrictlyGE_iff a).mpr
    (fun n hn ↦ G.map_isZero (F.isZero_of_isStrictlyGE a n hn))
  have : K.IsStrictlyLE b := (K.isStrictlyLE_iff b).mpr
    (fun n hn ↦ G.map_isZero (F.isZero_of_isStrictlyLE b n hn))
  have : L.IsStrictlyGE (-b) := (L.isStrictlyGE_iff (-b)).mpr
    (fun n hn ↦ G.map_isZero (F.rightDual.isZero_of_isStrictlyGE (-b) n hn))
  have : L.IsStrictlyLE (-a) := (L.isStrictlyLE_iff (-a)).mpr
    (fun n hn ↦ G.map_isZero (F.rightDual.isZero_of_isStrictlyLE (-a) n hn))
  have (j : ℤ) : PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G := inferInstance
  let : (G.mapHomologicalComplex (.up ℤ)).Monoidal := Functor.mapCochainComplexMonoidal G
  let := CochainComplex.exactPairingRightDual F a b
  let := ExactPairing.map (G.mapHomologicalComplex (.up ℤ)) F F.rightDual
  exact derived_pairing K L a b (-b) (-a) hK hL

end CochainComplex
