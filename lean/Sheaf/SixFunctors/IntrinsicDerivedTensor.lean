module
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.Algebra.Homology.KFlatResolutionGeneral
public import Sheaf.AlgebraicGeometry.ProEtaleOperations

/-!
# Intrinsic derived tensor on constant-coefficient pro-etale modules

Source: Stacks Project, Cohomology on Sites, Tags 06YN, 06YS and 06YU
(blueprint: def-weil-derived-tensor).
-/
@[expose] public section
set_option autoImplicit false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The derived tensor product on the intrinsic constant-coefficient pro-etale derived
category, formed from the canonical chosen representative and its K-flat resolution.
Source: Stacks Project, Cohomology on Sites, Tags 06YN, 06YS and 06YU
(blueprint: def-weil-derived-tensor). -/
noncomputable def proEtaleDerivedTensor (Y : Scheme.{t}) (A : Type t) [CommRing A]
    (K L : proEtaleDerivedCategory Y A) : proEtaleDerivedCategory Y A := by
  let K₀ : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ :=
    DerivedCategory.Q.objPreimage K
  let L₀ : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ :=
    DerivedCategory.Q.objPreimage L
  let e := CochainComplex.exists_isKFlatResolutionGeneral K₀
  let P := Classical.choose e
  let f := Classical.choose (Classical.choose_spec e)
  let hf := (Classical.choose_spec (Classical.choose_spec e)).2.2.1
  let hP := (Classical.choose_spec (Classical.choose_spec e)).1
  exact derivedTensor Y A K₀ L₀ P f hf hP

/-- Derived tensor with a constant ring B along a ring map A → B, regarded as an
A-module object by restriction of scalars. Source: Stacks Project, Cohomology on Sites,
Tag 06YU (blueprint: def-weil-derived-tensor). -/
noncomputable def proEtaleDerivedTensorRing (Y : Scheme.{t}) (A : Type t) [CommRing A]
    (B : Type t) [CommRing B] (φ : A →+* B)
    (K : proEtaleDerivedCategory Y A) : proEtaleDerivedCategory Y A := by
  let RA := (constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1, t} A))
  let RB := (constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1, t} B))
  let SA := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj RA
  let SB := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj RB
  let α : SA ⟶ SB :=
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      ((constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (RingHom.ulift φ)))
  let M := (SheafOfModules.restrictScalars.{t + 1} α).obj (SheafOfModules.unit SB)
  exact proEtaleDerivedTensor Y A K
    ((DerivedCategory.singleFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y A)) 0).obj M)

end AlgebraicGeometry.Scheme
