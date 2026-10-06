/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.Functor
public import WeilConjectures.CategoryTheory.RingObjects.Functor
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal

/-!

# Pullback of module objects on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category (for instance
`ModuleCat ℤ`, i.e. abelian groups) and `X` a scheme. Sheaves on `X_proét` with values in `A`
form a closed symmetric monoidal abelian category `Sheaf (Scheme.ProEt.topology X) A`, so for a
ring object `R` in it (a sheaf of rings on `X_proét`) we have the abelian category of
`R`-module objects, i.e. sheaves of `R`-modules.

For a morphism of schemes `g : Z ⟶ X`, the pullback `g^*` of pro-étale sheaves is strongly
monoidal (`ProEtale.upperStarMonoidal`). Its oplax monoidal structure comes from the adjunction
`g^* ⊣ g_*` and the lax monoidal structure of `g_*`; that its comparison maps are isomorphisms
(`g^*` commutes with tensor products, both being sheafifications of their presheaf versions) is
not formalized and is `sorry`ed (`ProEtale.isIso_η_upperStar`, `ProEtale.isIso_δ_upperStar`).

Hence `g^*` sends the ring object `R` to the ring object `g^* R`, `R`-modules to
`g^* R`-modules (`ProEtale.modPullback`), and global sections of `R` to global sections of
`g^* R` by a ring homomorphism (`ProEtale.ΓPullback`).

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]


/-- Tensoring with a pro-étale sheaf is right exact, since the tensor product is closed. -/
instance preservesFiniteColimits_tensorLeft {Y : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    PreservesFiniteColimits (tensorLeft F) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
variable {Z X : Scheme.{u}} (g : Z ⟶ X)

/-- The oplax monoidal structure on the pullback `g^*` of pro-étale sheaves, from the
adjunction `g^* ⊣ g_*` and the lax monoidal structure of `g_*`. -/
@[instance_reducible]
noncomputable def upperStarOplaxMonoidal : (ProEtale.upperStar A g).OplaxMonoidal :=
  (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal

attribute [local instance] upperStarOplaxMonoidal

/-- The pullback of pro-étale sheaves preserves the unit. -/
instance isIso_η_upperStar : IsIso (Functor.OplaxMonoidal.η (ProEtale.upperStar A g)) :=
  sorry

/-- The pullback of pro-étale sheaves commutes with tensor products. -/
instance isIso_δ_upperStar (F G : Sheaf (Scheme.ProEt.topology X) A) :
    IsIso (Functor.OplaxMonoidal.δ (ProEtale.upperStar A g) F G) :=
  sorry

/-- The pullback of pro-étale sheaves is strongly monoidal. -/
noncomputable instance upperStarMonoidal : (ProEtale.upperStar A g).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

variable {A} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- The pullback of a module object over `R` along `g`, a module object over `g^* R`. -/
noncomputable abbrev modPullback :
    Mod (Sheaf (Scheme.ProEt.topology X) A) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) A) ((ProEtale.upperStar A g).obj R) :=
  (ProEtale.upperStar A g).mapMod R

/-- The ring homomorphism on global sections induced by the pullback along `g`. -/
noncomputable abbrev ΓPullback : Γ R →+* Γ ((ProEtale.upperStar A g).obj R) :=
  Γ.mapFunctor (ProEtale.upperStar A g)

end AlgebraicGeometry.ProEtale
