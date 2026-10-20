/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import Sheaf.CategoryTheory.KInjectiveTotalDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange

/-!
# Unbounded proper/open BaseChange

Source: Stacks Project, Tags 0F7F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- BaseChange for families normalized on sheaves and on every K-injective representative.
Source: Stacks Project, Tags 0F7F.
(blueprint: lem-amb-unbounded-proper-open-base-change).

Proof:
Choose a K-injective J and a resolution rho:k!J -> I. For the base-changed square
choose resolutions j:d*J -> J1 and t:a*I -> I1. Both k1!j and the composite of t, a*rho,
and the extension-zero base-change inverse are quasi-isomorphisms. The K-injective Hom
bijection produces v:k1!J1 -> I1 compatible up to homotopy with these maps; two-out-of-three
makes v a quasi-isomorphism. Before resolutions, include the two sheaf cube paths into
the common direct image. The support comparison pullback formula and ordinary mate
pasting give the same restriction of each section, hence equality by monicity. The
specified extension-zero base-change maps restrict to the same open-unit identities, so
these are precisely the normalized maps in the statement. Compose this sheaf cube with
p1*v and k1!j. Naturality of theta1 and of ordinary exchange, and the defining homotopy
of v, identify its two paths with the representative formulas for the two derived paths.
Use the unbounded module-exchange representative theorem for the exact adjunction mate.
Every functor preserves the homotopies termwise. Localization therefore gives the claimed
identity for QJ, and naturality transports it to all derived inputs. No exchange map is
cancelled and inverse image need not preserve K-injectives.
-/
theorem unboundedProperOpenBaseChange_of_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))
    (hθ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F))
    (hΓ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((k)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        D((i)_!open[ModuleCat.{u + 1} A]).map
            (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((r)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (θ k r p i sq).hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) =
        (Γ k r p i sq).hom.app (DerivedCategory.Q.obj J) ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom)) :
    (∀ {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian U₁] [IsNoetherian V₁] [IsNoetherian W₁] [IsNoetherian Z₁]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
        (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
        (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
        (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
        (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
        (K : DerivedCategoryModule A U),
        D((b)^*[ModuleCat.{u + 1} A]).map ((Γ k r p i sq).hom.app K) ≫
            (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₁)_*[ModuleCat.{u + 1} A]).map
              ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
                (ModuleCat.{u + 1} A) sk).inv.app K) =
          (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) si).inv.app
                (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((i₁)_!open[ModuleCat.{u + 1} A]).map
              ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app K) ≫
            (Γ k₁ r₁ p₁ i₁ sq₁).hom.app (D((d)^*[ModuleCat.{u + 1} A]).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
