/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData

/-! # Ordinary square for flat-term quotient section pull transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The normalized ordinary section square is obtained by conjugating the
internal pullback scalar square through the two chosen ordinary section models.
The proof is the ordinary-generator calculation: the endpoint normalization
identities turn the conjugated map into the balanced section map, and naturality
of `pullComparison` supplies the displayed equation.
(blueprint: lem-sfb-quotient-section-pull-transport-kflat-ordinary). -/
theorem section_pull_transport_kflat_ordinary {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY) :
    ∃ e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E,
      ∀ M : Modules Λ Y,
        (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
            cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
            cX.model.E.map ((pullComparison Λ f).hom.app M) =
          (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
            (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
            e.hom.app ((equivalence Λ Y).functor.obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
