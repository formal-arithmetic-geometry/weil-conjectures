/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Pushforward and pullback in the two models of finite coefficients

Let `T` be a finite discrete commutative ring and `f : X ⟶ Y` a morphism of schemes. The
equivalence `ProEtale.finiteCoefficientModEquivalence` between module objects over
`Λ_X = p_X^* T̲` and sheaves of `T`-modules on `X_proét` commutes with the pushforward `f_*` and
with the pullback `f^*`:

* the pushforward `(f)_*⟦T̲⟧` of module objects has underlying abelian sheaf `f_* M`, with
  `Λ_Y` acting through `η_f : Λ_Y ⟶ f_* Λ_X`; the pushforward of sheaves of `T`-modules has the
  same underlying abelian sheaf, and the actions of `t ∈ T` agree, since `η_f` sends the constant
  global section `t` of `Λ_Y` to the pushforward of the constant global section `t` of `Λ_X`
  (`ProEtale.finiteCoefficientModEquivalenceLowerStarIso`);
* the pullbacks are the left adjoints of the pushforwards, so they correspond as well
  (`ProEtale.finiteCoefficientModEquivalenceUpperStarIso`).

## Main definitions

- `CategoryTheory.Sheaf.isoOfForget₂Iso`: an isomorphism of the underlying abelian sheaves of
  two sheaves of `T`-modules which is `T`-linear on sections is an isomorphism of sheaves of
  `T`-modules.
- `ProEtale.finiteCoefficientModEquivalenceLowerStarIso`: `f_*` commutes with
  `finiteCoefficientModEquivalence`.
- `ProEtale.finiteCoefficientModEquivalenceUpperStarIso`: `f^*` commutes with
  `finiteCoefficientModEquivalence`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C} {T : Type (u + 1)}
  [Ring T]

/-- An isomorphism `e` of the underlying abelian sheaves of two sheaves of `T`-modules which is
`T`-linear on sections is an isomorphism of sheaves of `T`-modules. -/
noncomputable def isoOfForget₂Iso {F G : Sheaf J (ModuleCat.{u + 1} T)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj G)
    (he : ∀ (U : Cᵒᵖ) (t : T) (x : F.obj.obj U),
      e.hom.hom.app U (t • x) =
        @HSMul.hSMul T (G.obj.obj U) (G.obj.obj U) _ t (e.hom.hom.app U x)) :
    F ≅ G :=
  sorry

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The pushforward commutes with `finiteCoefficientModEquivalence`**: the pushforward of
module objects over `T̲` corresponds to the pushforward of sheaves of `T`-modules. Both have
underlying abelian sheaf `f_* M`; the actions of `t ∈ T` agree since `η_f` sends the constant
section `t` of `Λ_Y` to the pushforward of the constant section `t` of `Λ_X`. -/
noncomputable def finiteCoefficientModEquivalenceLowerStarIso :
    (f)_*⟦Profinite.continuousMapRingObj T⟧ ⋙ (finiteCoefficientModEquivalence Y T).functor ≅
      (finiteCoefficientModEquivalence X T).functor ⋙
        (f)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  sorry

/-- **The pullback commutes with `finiteCoefficientModEquivalence`**: the pullback of module
objects over `T̲` corresponds to the pullback of sheaves of `T`-modules. Both are left adjoint
to the pushforwards, which correspond by `finiteCoefficientModEquivalenceLowerStarIso`. -/
noncomputable def finiteCoefficientModEquivalenceUpperStarIso :
    (f)^*⟦Profinite.continuousMapRingObj T⟧ ⋙ (finiteCoefficientModEquivalence X T).functor ≅
      (finiteCoefficientModEquivalence Y T).functor ⋙
        (f)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  sorry

end AlgebraicGeometry.ProEtale
