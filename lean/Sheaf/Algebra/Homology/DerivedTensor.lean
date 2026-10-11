/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.Single

/-!
# Derived tensor product on the small pro-etale site

Source: the Weil conjectures blueprint, `def-weil-derived-tensor`, order 663;
Stacks Project, Cohomology on Sites, Tags 06YN, 06YS and 06YU
(blueprint: def-weil-derived-tensor).

The constant sheaf is formed in commutative rings before forgetting to rings,
so the recorded K-flat predicate and sheaf tensor product apply directly.
-/

universe w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{w}) (A : Type w) [CommRing A]

set_option hygiene false in
set_option quotPrecheck false in
local notation "𝓡" =>
  (constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
    (CommRingCat.of (ULift.{w + 1, w} A))
set_option hygiene false in
set_option quotPrecheck false in
local notation "𝓢" =>
  (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj 𝓡

/-- Derived tensor with a chosen K-flat resolution `f : P ⟶ K₁`.

The K-flat condition is the existing `CochainComplex.IsKFlat` for the constant
sheaf of commutative rings.
The representative is the total complex with degree `n` term `⨁ p + q = n, Pᵖ ⊗ K₂ᵠ`
and differential `d_P ⊗ 1 + (-1)^p 1 ⊗ d_K₂`, mapped into the derived category.
No independence-of-resolution theorem is asserted here.

Source: blueprint `def-weil-derived-tensor`, order 663; Stacks Project, Tags 06YN,
06YS and 06YU (blueprint: def-weil-derived-tensor). -/
noncomputable def derivedTensor
    (K₁ K₂ P : CochainComplex (SheafOfModules.{w + 1} 𝓢) ℤ)
    (_f : P ⟶ K₁) (_hf : QuasiIso _f)
    (_hP : CochainComplex.IsKFlat.{w + 1, w} (R := 𝓡) P) :
    proEtaleDerivedCategory Y A :=
  letI := SheafOfModules.monoidalCategory 𝓡
  letI := HasDerivedCategory.standard (SheafOfModules.{w + 1} 𝓢)
  DerivedCategory.Q.obj (CochainComplex.mapBifunctor P K₂ (curriedTensor _))

/-- Derived tensor with the constant ring `B` along a ring map `φ : A →+* B`.

The constant ring sheaf `B_Y`, as a module over itself, is restricted along the
constant-sheaf image of `φ` and placed in degree zero. Applying `derivedTensor`
uses exactly the same chosen K-flat resolution of `K₁`.

Source: blueprint `def-weil-derived-tensor`, order 663, last sentence;
Stacks Project, Tag 06YU (blueprint: def-weil-derived-tensor). -/
noncomputable def derivedTensorRing
    (B : Type w) [CommRing B] (φ : A →+* B)
    (K₁ P : CochainComplex (SheafOfModules.{w + 1} 𝓢) ℤ)
    (f : P ⟶ K₁) (hf : QuasiIso f)
    (hP : CochainComplex.IsKFlat.{w + 1, w} (R := 𝓡) P) :
    proEtaleDerivedCategory Y A :=
  let RB := (constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
    (CommRingCat.of (ULift.{w + 1, w} B))
  let SB := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj RB
  let α : 𝓢 ⟶ SB := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).map
      ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).map
        (CommRingCat.ofHom (RingHom.ulift φ)))
  let M := (SheafOfModules.restrictScalars.{w + 1} α).obj (SheafOfModules.unit SB)
  derivedTensor Y A K₁ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) P f hf hP

end AlgebraicGeometry.Scheme
