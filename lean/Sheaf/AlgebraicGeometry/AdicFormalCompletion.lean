/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Adic formal completions as ringed spaces

Source: Temkin, Non-embedded desingularization, §2.4.1
(blueprint: def-per-adic-formal-completion).

The colimit is taken in ringed spaces, not schemes. Its structure sheaf is the inverse
limit of the structure sheaves of the infinitesimal thickenings. We retain the original
scheme and ideal as a presentation, giving a fixed basis of completed affine charts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A presentation of the completion of a scheme along a quasi-coherent ideal.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
structure AdicFormalCompletion where
  scheme : Scheme.{u}
  ideal : scheme.IdealSheafData

namespace AdicFormalCompletion

/-- The infinitesimal thickenings, allowing a fixed additional closed subscheme.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def thickeningIdeals (C : AdicFormalCompletion.{u})
    (J : C.scheme.IdealSheafData) : ℕ ⥤ C.scheme.IdealSheafDataᵒᵖ :=
  Functor.ofSequence fun n ↦
    (homOfLE (sup_le_sup_right
      (pow_le_pow_right_of_le_one' (show C.ideal ≤ 1 from le_top)
        (Nat.le_succ (n + 1))) J)).op

/-- Infinitesimal thickenings as schemes over the ambient scheme.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def thickenings (C : AdicFormalCompletion.{u})
    (J : C.scheme.IdealSheafData) : ℕ ⥤ Over C.scheme :=
  C.thickeningIdeals J ⋙ Scheme.IdealSheafData.subschemeFunctor C.scheme

/-- The underlying ringed-space functor, retaining the actual structure sheaves.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
def ringedSpaceFunctor : Scheme.{u} ⥤ RingedSpace.{u, u} :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace

/-- The ringed-space diagram defining completion of the closed subscheme cut out by `J`.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def ringedDiagram (C : AdicFormalCompletion.{u})
    (J : C.scheme.IdealSheafData) : ℕ ⥤ RingedSpace.{u, u} :=
  C.thickenings J ⋙ Over.forget C.scheme ⋙ ringedSpaceFunctor

/-- The completed closed subspace: its affine rings are limits of `B/(I^n + J)`.
Source: Temkin §§2.4.1,2.4.9 (blueprint: def-per-adic-formal-completion). -/
noncomputable def closedSubspace (C : AdicFormalCompletion.{u})
    (J : C.scheme.IdealSheafData) : RingedSpace.{u, u} :=
  colimit (C.ringedDiagram J)

/-- The formal completion, with its completed structure sheaf.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def space (C : AdicFormalCompletion.{u}) : RingedSpace.{u, u} :=
  C.closedSubspace ⊥

/-- The canonical map of the formal completion to its ambient scheme.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def toScheme (C : AdicFormalCompletion.{u}) :
    C.space ⟶ C.scheme.toRingedSpace :=
  colimit.desc (C.ringedDiagram ⊥)
    (ringedSpaceFunctor.mapCocone ((Over.forgetCocone C.scheme).whisker (C.thickenings ⊥)))

/-- The completed ring on an original affine chart.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
abbrev chartRing (C : AdicFormalCompletion.{u}) (U : C.scheme.affineOpens) :=
  AdicCompletion (C.ideal.ideal U) Γ(C.scheme, U)

/-- Extension of a quasi-coherent ideal to a completed affine chart.
Source: Temkin §§2.4.1,2.4.9 (blueprint: def-per-adic-formal-completion). -/
noncomputable def extendedIdeal (C : AdicFormalCompletion.{u})
    (J : C.scheme.IdealSheafData) (U : C.scheme.affineOpens) : Ideal (C.chartRing U) :=
  (J.ideal U).map (algebraMap Γ(C.scheme, U) (C.chartRing U))

/-- The ideal of definition on a completed affine chart.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def chartIdeal (C : AdicFormalCompletion.{u}) (U : C.scheme.affineOpens) :
    Ideal (C.chartRing U) :=
  C.extendedIdeal C.ideal U

/-- The reduced closed fibre, with its actual reduced scheme structure.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def closedFibre (C : AdicFormalCompletion.{u}) : Scheme.{u} :=
  C.ideal.radical.subscheme

/-- Formal spectrum, constructed by its infinitesimal affine thickenings.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def formalSpectrum (A : CommRingCat.{u}) (J : Ideal A) : RingedSpace.{u, u} :=
  (AdicFormalCompletion.mk (Spec A) (Scheme.IdealSheafData.ofIdealTop
    (J.map (Scheme.ΓSpecIso A).inv.hom))).space

/-- The inverse image of an ambient open in the underlying formal completion.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def openChart (C : AdicFormalCompletion.{u}) (U : C.scheme.affineOpens) :
    Opens C.space :=
  (Opens.map C.toScheme.hom.base).obj U.1

/-- Restriction to an ambient affine chart, as an actual ringed space.
Source: Temkin §2.4.1 (blueprint: def-per-adic-formal-completion). -/
noncomputable def chartSpace (C : AdicFormalCompletion.{u}) (U : C.scheme.affineOpens) :
    RingedSpace.{u, u} :=
  C.space.restrict (C.openChart U).isOpenEmbedding

end AdicFormalCompletion
end AlgebraicGeometry

namespace AlgebraicGeometry.AdicFormalCompletion

/-- A Noetherian adic formal space has a finite cover by complete Noetherian formal spectra.
Source: Temkin §2.4 (blueprint: def-per-adic-formal-completion). -/
def IsNoetherianFormalSpace (F : RingedSpace.{u, u}) : Prop :=
  ∃ (n : ℕ) (U : Fin n → Opens F) (A : Fin n → CommRingCat.{u})
    (K : ∀ i, Ideal (A i)), (⨆ i, U i) = ⊤ ∧
    ∀ i, IsNoetherianRing (A i) ∧ (K i).FG ∧ IsAdicComplete (K i) (A i) ∧
      Nonempty (F.restrict (U i).isOpenEmbedding ≅ formalSpectrum (A i) (K i))

end AlgebraicGeometry.AdicFormalCompletion
