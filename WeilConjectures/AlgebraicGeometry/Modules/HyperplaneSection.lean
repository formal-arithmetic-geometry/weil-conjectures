module

public import WeilConjectures.AlgebraicGeometry.Modules.Vanishing
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial

@[expose] public section

universe v₁ u₁ u

open CategoryTheory MonoidalCategory Opposite TensorProduct TopologicalSpace
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- The forgetful functor from sheaves of `R`-modules to presheaves of modules over the
underlying presheaf of rings of `R`, spelled so that the monoidal structure on presheaves of
modules is found by instance resolution. This is the right adjoint of
`SheafOfModules.sheafification`. -/
noncomputable abbrev forgetRestrict :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)

/-- The forgetful functor to presheaves of modules is lax monoidal, being right adjoint to the
monoidal sheafification functor. -/
noncomputable instance : (forgetRestrict (R := R)).LaxMonoidal :=
  Adjunction.rightAdjointLaxMonoidal (F := sheafification R) (G := forgetRestrict)
    (PresheafOfModules.sheafificationAdjunction (𝟙 _))

variable (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))

set_option maxHeartbeats 1000000 in
-- unfolding the lax monoidal structure of the right adjoint is expensive
/-- **The comparison morphism `SheafOfModules.tensorPresheafHom` is the tensorator of the lax
monoidal forgetful functor** to presheaves of modules. All its coherences are therefore those of
a lax monoidal functor. -/
theorem mu_eq_tensorPresheafHom : μ (forgetRestrict (R := R)) F G = tensorPresheafHom F G := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ]
  rfl

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The unit global section of the tensor unit of `X.Modules` over an open subset `U`, the
section corresponding to `1 : Γ(X, U)`. -/
noncomputable def unitSection (X : Scheme.{u}) (U : X.Opens) : Γ(𝟙_ X.Modules, U) :=
  ((ε (SheafOfModules.forgetRestrict (R := X.sheaf))).app (op U)).hom (1 : Γ(X, U))

end AlgebraicGeometry.Scheme.Modules
