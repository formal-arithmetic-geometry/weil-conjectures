/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.DeligneLaumon.CondensedCoefficientUnit

/-! # Relative dualizing complex

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sp-dualizing/_section.md, node sk-def-sp-dualizing, order 1811
(blueprint: sk-def-sp-dualizing).

For the standing smooth morphism and an admissible condensed coefficient, this is the
value of the exceptional inverse image `f^!` of `exceptionalInverseImage_exists`
(sk-prop-sf-existence, sk-thm-existence) at the coefficient unit `Λ_Y`, the regular
module over `Λ_Y = p_Y^* Λ` in degree zero.  The right adjoint is unique up to unique
counit-compatible isomorphism (det-sp-unique-right-adjoint), so the object does not
depend on the adjoint selected from the existence statement.

The node's last sentence (for finite coefficients `ω_{f,A}` may be computed on the
étale site) is the content of sk-prop-sp-et-proet and of its stated part
det-sp-et-proet-adjunction-transfer (`etaleProEtaleAdjunctionTransfer`), evaluated at
the unit; it is not restated here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The coefficient unit `Λ_X`, the regular module over `Λ_X = p_X^* Λ` placed in degree
zero, is bounded constructible.

Proof (node sk-def-sp-dualizing, step 1): its only cohomology is the regular module in
degree zero; the one-stratum stratification `X` with the one-generator, zero-relation
constant local model `Λ(*)` makes that module constructible (sk-def-sfb-constructible,
sk-def-sfb-pulled-back-coefficients).  This covers the empty scheme and the zero ring.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-def-sp-dualizing/
_section.md, node sk-def-sp-dualizing, first paragraph (blueprint: sk-def-sp-dualizing).
-/
theorem coefficientUnit_boundedConstructible
    (X : Scheme.{u}) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X
      ((DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj Λ X))) := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  exact (constantModelBoundedConstructible Λ X).prop_of_iso
    (DerivedCategory.singleFunctorObjUnitIso _).symm (condensedCoefficientUnit_mem Λ X).1

/-- The coefficient unit `Λ_X` in degree zero has finite Tor amplitude, namely `[0, 0]`.

Proof (node sk-def-sp-dualizing, step 1): the derived tensor of the regular module with
any module sheaf `M` placed in degree zero is `M` in degree zero.  This covers the empty
scheme and the zero ring.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-def-sp-dualizing/
_section.md, node sk-def-sp-dualizing, first paragraph (blueprint: sk-def-sp-dualizing).
-/
theorem coefficientUnit_finiteTor
    (X : Scheme.{u}) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      ((DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj Λ X))) := by
  refine ⟨0, 0, ?_⟩
  intro N
  let e := tensorIso (DerivedCategory.singleFunctorObjUnitIso _) (Iso.refl
    ((DerivedCategory.singleFunctor _ 0).obj N)) ≪≫ λ_ _
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm 0,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm 0⟩

/-- The relative dualizing complex `ω_{f,Λ} = f^!_Λ Λ_Y ∈ Dctf(X, Λ)` of a smooth
morphism `f : X → Y` of the standing schemes and an admissible coefficient `Λ`.

Construction (node sk-def-sp-dualizing):
1. The coefficient unit `Λ_Y` is the regular module over `Λ_Y = p_Y^* Λ` in degree zero;
   it lies in `Dctf(Y, Λ)` (`coefficientUnit_boundedConstructible`,
   `coefficientUnit_finiteTor`), hence in `Loc(Dctf(Y, Λ))`.  The value of the right
   adjoint `f^!` of `Rf_!` on `Loc(Dctf)` supplied by `exceptionalInverseImage_exists`
   (sk-prop-sf-existence, sk-thm-existence (3)) at this unit is `ω_{f,Λ}`; clause (4)
   of sk-thm-existence places it in `Dctf(X, Λ)`.  The adjoint is unique up to unique
   counit-compatible isomorphism (det-sp-unique-right-adjoint).
2. For finite `A` the étale computation of `ω_{f,A}` is the identification of the
   transported étale right adjoint with `f^!|_{Dctf}` of sk-prop-sp-et-proet
   (det-sp-et-proet-adjunction-transfer), evaluated at `A_Y`.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-def-sp-dualizing/
_section.md, node sk-def-sp-dualizing (blueprint: sk-def-sp-dualizing).
-/
noncomputable def relativeDualizingComplex
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : BaseFieldFiniteCD ℓ k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [Smooth f.left]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ConstantModelConstructibleFiniteTor Λ X.left := by
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  letI : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let Hex := exceptionalInverseImage_exists (Λ := Λ) ℓ k hcd f hΛ
  let hX := Classical.choose Hex
  let e1 := Classical.choose_spec Hex
  let hY := Classical.choose e1
  let e2 := Classical.choose_spec e1
  let hSX := Classical.choose e2
  let e3 := Classical.choose_spec e2
  let hSY := Classical.choose e3
  let e4 := Classical.choose_spec e3
  let h := Classical.choose e4
  let e5 := Classical.choose_spec e4
  let sX := Classical.choose e5
  let e6 := Classical.choose_spec e5
  let sY := Classical.choose e6
  let e7 := Classical.choose_spec e6
  letI := hX
  letI := hY
  letI := sX
  letI := sY
  let H := @e7
  let hGE := H.2.2.2.2.2.2.1
  let G := Classical.choose hGE
  let eG := Classical.choose_spec hGE
  let hsG := Classical.choose eG
  let eGs := Classical.choose_spec eG
  letI := hsG
  let hGdata := @eGs
  let hGpres := hGdata.2.2
  let C := Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
    (condensedRingObj Λ Y.left)
  let U := (DerivedCategory.singleFunctor C 0).obj
    (Mod.regular (condensedRingObj Λ Y.left))
  have hU : (constantModelBoundedConstructible Λ Y.left ⊓
      DerivedCategory.finiteTorAmplitude C) U :=
    ⟨coefficientUnit_boundedConstructible Y.left Λ,
      coefficientUnit_finiteTor Y.left Λ⟩
  let N : (localizingClosureProEtale Λ Y.left).FullSubcategory :=
    ⟨U, hSY U hU⟩
  exact ⟨(G.obj N).obj, hGpres N hU⟩

end AlgebraicGeometry.ProEtale.CondensedRing
