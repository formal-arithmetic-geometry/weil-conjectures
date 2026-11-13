/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange
import WeilConjectures.AlgebraicGeometry.ModuleAbelianStalkExchange

/-!
# Exchange on total-space cohomology over strictly henselian bases

 This comparison involves total spaces, not closed fibres.

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Higher-direct-image stalk exchange over strict local bases is total-space pullback. -/
theorem Etale.exists_addEquiv_strictLocal_totalCohomology_exchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (φ : A →+* B) [IsLocalHom φ]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of B))
    (g' : X' ⟶ X) (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    ∃ (a₁ : ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ (Spec.map (CommRingCat.ofHom φ)) f q).obj F) ≃+
        Sheaf.H ((sheafCompose _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
      (a₂ : ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((g')^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q),
      ∀ x, a₂ ((((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap g'
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
          q (a₁ x) := by
  obtain ⟨b₁, b₂, hb⟩ := Etale.exists_addEquiv_module_abelian_stalk_exchange
    Λ f f' g' (Spec.map (CommRingCat.ofHom φ)) sq
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) F q
  obtain ⟨a₁, a₂, ha⟩ := Etale.exists_addEquiv_strictLocal_abelian_total_exchange
    φ f f' g' sq
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q
  refine ⟨b₁.trans a₁, b₂.trans a₂, ?_⟩
  intro x
  change a₂ (b₂ _) = Etale.cohomologyMap g' _ q (a₁ (b₁ x))
  rw [hb x]
  exact ha (b₁ x)

end AlgebraicGeometry
