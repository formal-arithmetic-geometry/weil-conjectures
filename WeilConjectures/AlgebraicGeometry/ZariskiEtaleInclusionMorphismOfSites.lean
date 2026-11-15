/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Sheaf
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleSheafLeftExact

/-!
# The inclusion of the Zariski site into the small étale site

Source: Stacks Project, Sites, Tags 00X6 and 00X5.

## Main statements

* `zariski_to_etale_is_morphism` records the inclusion functor, its continuity,
  preservation of finite limits, and exact sheaf inverse image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- The inclusion of the Zariski site into the small étale site is a morphism of sites: there is
a continuous, cover-preserving, finite-limit-preserving functor `i` lifting `X.restrictFunctor`
and sending `⊤` to a terminal object, whose sheaf pushforward has an exact left adjoint `L`.

Stacks Project, Sites, Tags 00X6 and 00X5.
-/
theorem zariski_to_etale_is_morphism (X : Scheme.{u}) :
    ∃ (i : X.Opens ⥤ X.Etale),
      (i ⋙ Scheme.Etale.forget X = X.restrictFunctor) ∧
      CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i ∧
      PreservesFiniteLimits i ∧
      Nonempty (IsTerminal (i.obj ⊤)) ∧
      ∃ (_ : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology),
        ∃ (L : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)) ⥤
            Sheaf X.smallEtaleTopology (Type (max (u + 1) v))),
          Nonempty (L ⊣ i.sheafPushforwardContinuous (Type (max (u + 1) v))
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) ∧
          PreservesFiniteLimits L ∧ PreservesFiniteColimits L := by
  obtain ⟨i, hi_forget, hi_cover, hi_limits, hi_terminal, hcont⟩ :=
    zariski_to_etale_core X
  obtain ⟨hcontinuous, hflat⟩ := hcont
  let : RepresentablyFlat i := hflat
  let L := i.sheafPullback (Type (max (u + 1) v))
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  have hLlim : PreservesFiniteLimits L := zariski_to_etale_sheaf_left_exact X i hcontinuous
  have : L.IsLeftAdjoint :=
    (i.sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).isLeftAdjoint
  have hLcolim : PreservesFiniteColimits L := inferInstance
  exact ⟨i, hi_forget, hi_cover, hi_limits, hi_terminal,
    ⟨hcontinuous, L, ⟨i.sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology⟩, hLlim, hLcolim⟩⟩

end AlgebraicGeometry
