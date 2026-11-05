/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTrace
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisCoverTrace
public import WeilConjectures.CategoryTheory.Adjunction.ConjugateCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceLowerStar
set_option linter.privateModule false  -- prune: only private declarations remain

/-!
# The Galois action of a covering on sections

For weakly étale `s : Y' ⟶ Y` and `g : Y ⟶ X`, the unit transport
`g_* g^* ⟶ (s ≫ g)_* (s ≫ g)^*` of abelian pro-étale sheaves (the unit of `s^* ⊣ s_*` followed
by the composition isomorphisms) is computed on sections: through the identifications
`g^* ≅ j_g^*` with the restrictions along the localization functors, it is the restriction along
`V ×_X Y' ⟶ V ×_X Y` (`AlgebraicGeometry.ProEtale.baseChangeTransport`).

## Main results

- `AlgebraicGeometry.ProEtale.localizationUnitTransport_eq`: the unit transport for the
  restrictions `j^*` is the restriction along `baseChangeTransport`; the computation is carried
  out in the pro-étale sites, through the adjunctions `Over.map ⊣ Over.pullback` and the
  composition isomorphism `Over.pullbackComp`
  (`AlgebraicGeometry.ProEtale.map_unit_comp_pullbackComp_inv_comp_counit`).
- `AlgebraicGeometry.ProEtale.unitTransport_eq_baseChangeTransportSheafHom`: the same for the
  pullbacks `g^*`, by invariance of the unit transport under a change of left adjoints
  (`CategoryTheory.unitTransport_app_leftAdjointUniq`).
- `AlgebraicGeometry.ProEtale.galoisAction_eq_unitTransport`: the action of `σ` on `g_* g^* H`
  for a Galois covering is the unit transport along `ρ σ`, transported along `ρ σ ≫ g = g`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

universe u

/-- The underlying morphism of `MorphismProperty.Over.homMk`. -/
@[simp]
private lemma overHomMk_left' {X : Scheme.{u}} {A B : X.ProEt} (f : A.left ⟶ B.left)
    (w : f ≫ B.hom = A.hom) (hf : (⊤ : MorphismProperty Scheme.{u}) f) :
    (MorphismProperty.Over.homMk f w hf).left = f :=
  rfl

/-- The underlying morphism of a composite in the pro-étale site. -/
@[simp]
private lemma proEtComp_left' {X : Scheme.{u}} {A B C : X.ProEt} (f : A ⟶ B) (h : B ⟶ C) :
    (f ≫ h).left = f.left ≫ h.left :=
  rfl

end AlgebraicGeometry.ProEtale
