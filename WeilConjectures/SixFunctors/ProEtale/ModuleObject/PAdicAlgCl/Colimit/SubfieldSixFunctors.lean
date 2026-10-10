/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Colimit.CoefficientHom

/-!

# The six functors on module objects over `E_X`, for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`), with the topology restricted from `ℚ̄_ℓ`. The coefficient
ring object `E_X = C(-, E)` on a scheme `X` is the ring object `A_X(E)` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap`, and the six
functors on module objects over `E_X` are those of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension`, for the topological ring
`T = E`. The topology of `E` is not an instance (`ℓ` cannot be recovered from `E`), so this file
records these functors with the topology `PadicAlgCl.normedFieldOfAlgebra ℓ E` installed, in the
namespace `AlgebraicGeometry.ProEtale.PadicSubfieldRing`, with scoped notations carrying `ℓ`
and `E`:

* `(f)_*⟦ℓ, E⟧`, the pushforward `f_*`, is `ProEtale.ContinuousMapRing.lowerStar E f`;
* `(f)^*⟦ℓ, E⟧`, the pullback `f^*`, is `ProEtale.ContinuousMapRing.upperStar E f`;
* `(j)_!open⟦ℓ, E⟧`, the extension by zero along an open immersion `j`, is
  `ProEtale.ContinuousMapRing.openImmersionLowerShriek E j`;
* `R(f)_!⟦ℓ, E⟧`, the derived lower shriek along `f` with a compactification, is
  `ProEtale.ContinuousMapRing.rightDerivedLowerShriek E f`;

together with the mate `α_f : f^* E_Y ⟶ E_X` of the coefficient morphism
`η_f : E_Y ⟶ f_* E_X` of `ProEtale.padicSubfieldPushforwardHom`
(`ProEtale.padicSubfieldPullbackHom`), the adjunctions `f^* ⊣ f_*`, `j_! ⊣ j^*` and their derived
versions, and the exactness properties, all transported from the finite-extension files. Nothing
is new here: the point is to have the functors for `E ≤ F` and for `E ⊆ ℚ̄_ℓ` in a form in which
their compatibility with the extension of scalars can be stated in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Colimit.Compatibility`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicSubfieldRing

open Scheme PadicAlgCl ContinuousMapRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### Pushforward and pullback -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteIntermediateField ℓ)

/-- The pushforward `f_* : Mod_{E_X} ⥤ Mod_{E_Y}` on module objects over the coefficient ring
object `E_X = C(-, E)` of a finite subextension `E`: the pushforward
`ProEtale.ContinuousMapRing.lowerStar` for `T = E` with the topology restricted from `ℚ̄_ℓ`,
`mapMod(f_*)` followed by restriction of scalars along `η_f : E_Y ⟶ f_* E_X`. -/
noncomputable def lowerStar :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.lowerStar E f

@[inherit_doc lowerStar]
scoped notation "(" f ")_*⟦" ℓ ", " E "⟧" => lowerStar ℓ f E

/-- The pushforward on module objects over `E_X` is `mapMod(f_*)` followed by the restriction
of scalars along the coefficient morphism `η_f : E_Y ⟶ f_* E_X`. -/
lemma lowerStar_eq :
    (f)_*⟦ℓ, E⟧ = (f)_*[Ab.{u + 1}].mapMod ⋙ Mod.comap (padicSubfieldPushforwardHom ℓ f E) := rfl

instance lowerStar_additive : (f)_*⟦ℓ, E⟧.Additive :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.lowerStar_additive E f

instance preservesFiniteLimits_lowerStar : PreservesFiniteLimits (f)_*⟦ℓ, E⟧ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.preservesFiniteLimits_lowerStar E f

/-- The mate `α_f : f^* E_Y ⟶ E_X` of the coefficient morphism `η_f : E_Y ⟶ f_* E_X`, a morphism
of ring objects. -/
noncomputable def padicSubfieldPullbackHom :
    (f)^*[Ab.{u + 1}].obj (padicSubfieldRingObj Y ℓ E) ⟶ padicSubfieldRingObj X ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapPullbackHom E f

instance isMonHom_padicSubfieldPullbackHom : IsMonHom (padicSubfieldPullbackHom ℓ f E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  isMonHom_continuousMapPullbackHom E f

/-- `α_f` is `f^* η_f` followed by the counit of `f^* ⊣ f_*`. -/
lemma padicSubfieldPullbackHom_eq :
    padicSubfieldPullbackHom ℓ f E = (f)^*[Ab.{u + 1}].map (padicSubfieldPushforwardHom ℓ f E) ≫
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counitAlgHom
        (padicSubfieldRingObj X ℓ E) := rfl

/-- The pullback `f^* : Mod_{E_Y} ⥤ Mod_{E_X}` on module objects over `E_X`: the pullback
`ProEtale.ContinuousMapRing.upperStar` for `T = E`, `mapMod(f^*)` followed by extension of
scalars along `α_f`. -/
noncomputable def upperStar :
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.upperStar E f

@[inherit_doc upperStar]
scoped notation "(" f ")^*⟦" ℓ ", " E "⟧" => upperStar ℓ f E

lemma upperStar_eq :
    (f)^*⟦ℓ, E⟧ = (f)^*[Ab.{u + 1}].mapMod ⋙ Mod.extendScalars (padicSubfieldPullbackHom ℓ f E) :=
  rfl

instance upperStar_additive : (f)^*⟦ℓ, E⟧.Additive :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.upperStar_additive E f

instance preservesFiniteColimits_upperStar : PreservesFiniteColimits (f)^*⟦ℓ, E⟧ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.preservesFiniteColimits_upperStar E f

/-- The adjunction `f^* ⊣ f_*` on module objects over `E_X`. -/
noncomputable def upperStarLowerStarAdjunction : (f)^*⟦ℓ, E⟧ ⊣ (f)_*⟦ℓ, E⟧ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.upperStarLowerStarAdjunction E f

instance : (f)_*⟦ℓ, E⟧.IsRightAdjoint := (upperStarLowerStarAdjunction ℓ f E).isRightAdjoint

instance : (f)^*⟦ℓ, E⟧.IsLeftAdjoint := (upperStarLowerStarAdjunction ℓ f E).isLeftAdjoint

instance preservesKFlatQuasiIso_upperStar : (f)^*⟦ℓ, E⟧.PreservesKFlatQuasiIso :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.preservesKFlatQuasiIso_upperStar E f

/-- The derived adjunction `Lf^* ⊣ Rf_*` on module objects over `E_X`. -/
noncomputable def derivedUpperStarLowerStarAdjunction : L((f)^*⟦ℓ, E⟧) ⊣ R((f)_*⟦ℓ, E⟧) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.derivedUpperStarLowerStarAdjunction E f

instance : L((f)^*⟦ℓ, E⟧).IsLeftAdjoint := (derivedUpperStarLowerStarAdjunction ℓ f E).isLeftAdjoint

instance : R((f)_*⟦ℓ, E⟧).IsRightAdjoint :=
  (derivedUpperStarLowerStarAdjunction ℓ f E).isRightAdjoint

end UpperLowerStar

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (E : FiniteIntermediateField ℓ)

/-- The extension by zero `j_! : Mod_{E_U} ⥤ Mod_{E_X}` along an open immersion `j : U ⟶ X` on
module objects over `E_X`: `ProEtale.ContinuousMapRing.openImmersionLowerShriek` for `T = E`,
the restriction of scalars along `α_j` followed by the linear extension by zero. -/
noncomputable def openImmersionLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (padicSubfieldRingObj U ℓ E) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.openImmersionLowerShriek E j

@[inherit_doc openImmersionLowerShriek]
scoped notation "(" j ")_!open⟦" ℓ ", " E "⟧" => openImmersionLowerShriek ℓ j E

lemma openImmersionLowerShriek_eq :
    (j)_!open⟦ℓ, E⟧ = Mod.comap (padicSubfieldPullbackHom ℓ j E) ⋙
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
        (padicSubfieldRingObj X ℓ E) := rfl

instance openImmersionLowerShriek_additive : (j)_!open⟦ℓ, E⟧.Additive :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.openImmersionLowerShriek_additive E j

instance preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open⟦ℓ, E⟧ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.preservesFiniteLimits_openImmersionLowerShriek E j

instance preservesFiniteColimits_openImmersionLowerShriek :
    PreservesFiniteColimits (j)_!open⟦ℓ, E⟧ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.preservesFiniteColimits_openImmersionLowerShriek E j

/-- For an open immersion `j`, the mate `α_j : j^* E_X ⟶ E_U` is an isomorphism. -/
instance isIso_padicSubfieldPullbackHom_of_isOpenImmersion :
    IsIso (padicSubfieldPullbackHom ℓ j E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  isIso_continuousMapPullbackHom_of_isOpenImmersion E j

instance preservesFiniteLimits_upperStar_of_isOpenImmersion :
    PreservesFiniteLimits (j)^*⟦ℓ, E⟧ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.preservesFiniteLimits_upperStar_of_isOpenImmersion E j

/-- The adjunction `j_! ⊣ j^*` on module objects over `E_X`, for an open immersion `j`. -/
noncomputable def openImmersionLowerShriekUpperStarAdjunction :
    (j)_!open⟦ℓ, E⟧ ⊣ (j)^*⟦ℓ, E⟧ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.openImmersionLowerShriekUpperStarAdjunction E j

/-- The derived adjunction `Dj_! ⊣ Dj^*` between the levelwise functors induced by the exact
functors `j_!` and `j^*` on module objects over `E_X`. -/
noncomputable def derivedOpenImmersionLowerShriekUpperStarAdjunction :
    D((j)_!open⟦ℓ, E⟧) ⊣ D((j)^*⟦ℓ, E⟧) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.derivedOpenImmersionLowerShriekUpperStarAdjunction E j

end OpenImmersion

/-! ### Derived lower shriek -/

section LowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (E : FiniteIntermediateField ℓ)

/-- The derived lower shriek `Rf_! : D(Mod_{E_X}) ⥤ D(Mod_{E_Y})` on module objects over `E_X`,
for the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`:
`ProEtale.ContinuousMapRing.rightDerivedLowerShriek` for `T = E`, that is `Di_! ⋙ Rg_*`. -/
noncomputable def rightDerivedLowerShriek :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (padicSubfieldRingObj Y ℓ E)) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ContinuousMapRing.rightDerivedLowerShriek E f

@[inherit_doc rightDerivedLowerShriek]
scoped notation "R(" f ")_!⟦" ℓ ", " E "⟧" => rightDerivedLowerShriek ℓ f E

/-- The derived lower shriek on module objects over `E_X` is `Di_! ⋙ Rg_*` for the chosen
compactification `X ⟶[i] Z ⟶[g] Y` of `f`. -/
lemma rightDerivedLowerShriek_eq :
    R(f)_!⟦ℓ, E⟧ = D(((HasCompactification.compactification f).i)_!open⟦ℓ, E⟧) ⋙
      R(((HasCompactification.compactification f).g)_*⟦ℓ, E⟧) := rfl

end LowerShriek

end AlgebraicGeometry.ProEtale.PadicSubfieldRing
