/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoodsPointwise

/-!
# Étaleness along a closed subscheme from its infinitesimal neighbourhoods

Source: More on Morphisms, Lemma 0A43 (part (2)).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Given a finite type morphism between locally Noetherian schemes and a closed subscheme
of the target, if every infinitesimal base change is étale, then the morphism is étale
on an open neighbourhood of the inverse image of the closed subscheme (Stacks, Tag 0A43). -/
theorem etale_on_open_of_etale_infinitesimal_neighbourhoods
    {X S Z : Scheme.{u}} (g : X ⟶ S) (i : Z ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsClosedImmersion i] (J : S.IdealSheafData) (hJ : J = i.ker)
    (h_etale : ∀ n : ℕ,
      Etale (pullback.snd g ((J ^ (n + 1)).subschemeι))) :
    ∃ W : X.Opens,
      (g : X → S) ⁻¹' Set.range (i : Z → S) ⊆ (W : Set X) ∧ Etale (W.ι ≫ g) := by
  classical
  let I := {x : X // (g : X → S) x ∈ Set.range (i : Z → S)}
  choose U hU hEU using fun x : I =>
    etale_infinitesimal_pointwise g i J hJ h_etale x.1 x.2
  let W : X.Opens := ⨆ x : I, U x
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    let y' : I := ⟨x, hx⟩
    exact (le_iSup U y') (hU y')
  · apply IsZariskiLocalAtSource.of_openCover (Scheme.Opens.iSupOpenCover U)
    intro x
    simpa [W, Scheme.Opens.iSupOpenCover] using hEU x

end AlgebraicGeometry
