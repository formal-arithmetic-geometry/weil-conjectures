/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.AbelianDerivedGlobalExtPullback
import WeilConjectures.AlgebraicGeometry.StrictLocalDerivedGlobalExchange

/-! # Strict-local exchange with abelian coefficients

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

/-- The geometric calculation of exchange for abelian sheaves, before any comparison
with cohomology computed in a category of modules. -/
theorem Etale.exists_addEquiv_strictLocal_abelian_total_exchange
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (φ : A →+* B) [IsLocalHom φ]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of B))
    (g' : X' ⟶ X) (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let g := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let S := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let T := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    let t := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
    ∃ (a₁ : ((t.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S) ≃+ Sheaf.H G q)
      (a₂ : ((t.sheafFiber (A := AddCommGrpCat.{u + 1})).obj T) ≃+
        Sheaf.H ((g')^*[AddCommGrpCat.{u + 1}].obj G) q),
      ∀ x, a₂ (((t.sheafFiber (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        Etale.cohomologyMap g' G q (a₁ x) := by
  obtain ⟨c₁, c₂, hc⟩ := Etale.exists_addEquiv_strictLocal_derivedGlobal_exchange
    φ f f' g' sq ((DerivedCategory.Plus.singleFunctor _ 0).obj G) (q : ℤ)
  obtain ⟨b₁, b₂, hb⟩ := Etale.exists_addEquiv_derivedGlobal_ext_pullback g' G q
  refine ⟨c₁.trans b₁, c₂.trans b₂, ?_⟩
  intro x
  change b₂ (c₂ _) = Etale.cohomologyMap g' G q (b₁ (c₁ x))
  rw [hc]
  exact hb (c₁ x)

end AlgebraicGeometry
