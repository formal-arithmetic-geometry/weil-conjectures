/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Zariski restriction of algebraic-space modules to an étale scheme

Source: Stacks Project, Properties of Spaces, Tag 03G7; Descent, Tags 03DX and 03FH
(blueprint: def-trf-space-module-scheme-restriction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (F : AlgebraicSpace S) (T : F.EtaleSite)

/-- Open subschemes of an étale test scheme, viewed as schemes over the base.
Source: Stacks, Tags 03ED and 03G7
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeOpensOver : ((F.etaleForget).obj T).Opens ⥤ Over S :=
  ((F.etaleForget).obj T).restrictFunctor ⋙ Over.map T.obj.left.hom

/-- The map to the space on each open is the composite with the test-scheme map.
Source: Stacks, Tags 03ED and 03G7
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeOpensArrow : ((F.etaleForget).obj T).Opens ⥤
    CostructuredArrow yoneda F.obj.obj :=
  (schemeOpensOver F T).toCostructuredArrow yoneda F.obj.obj
    (fun U ↦ yoneda.map (Over.homMk U.ι) ≫ T.obj.hom)
    (by
      intro U V i
      simp only [← Category.assoc, ← Functor.map_comp]
      congr 2
      ext1
      exact Scheme.homOfLE_ι _ i.le)

/-- The open-subscheme composites are representable étale.
Source: Stacks, Tags 03ED and 03G7
(blueprint: def-trf-space-module-scheme-restriction).
Proof: the Yoneda map of an open immersion is representable étale: its base change
is the ordinary scheme pullback, an open immersion. Compose this map with the given
representable étale test map, using `isEtale_comp`. -/
theorem schemeOpensArrow_isEtale (U : ((F.etaleForget).obj T).Opens) :
    IsEtale ((schemeOpensArrow F T).obj U).hom := by
  sorry

/-- The inclusion of Zariski opens in the small étale site of the space.
Source: Stacks, Tags 03ED and 03G7
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeOpens : ((F.etaleForget).obj T).Opens ⥤ F.EtaleSite :=
  ObjectProperty.lift _ (schemeOpensArrow F T) (schemeOpensArrow_isEtale F T)

/-- Zariski-open restriction is continuous.
Source: Stacks, Tags 03ED, 03G7 and 03FH
(blueprint: def-trf-space-module-scheme-restriction).
Proof: an open cover of an open subscheme is jointly surjective and étale, hence
is a cover in the small étale site. Its intersections are the same scheme
intersections. The sheaf equalizers for these covers therefore restrict to the
Zariski sheaf equalizers. The generating-cover criterion gives continuity. -/
theorem schemeOpens_isContinuous :
    (schemeOpens F T).IsContinuous
      (Opens.grothendieckTopology ((F.etaleForget).obj T))
      F.etaleTopology := by
  sorry

/-- The structure-ring comparison is the canonical identification
`O_T(U) ≅ Γ(U.toScheme, O)` on every open, with the usual restrictions.
Source: Stacks, Tags 03G7 and 03FH
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeOpensRingHom : ((F.etaleForget).obj T).ringCatSheaf.obj ⟶
    (schemeOpens F T).op ⋙ F.structurePresheaf :=
  Functor.whiskerRight (((F.etaleForget).obj T).restrictFunctorΓ.inv)
    (forget₂ CommRingCat RingCat)

/-- Restriction of an algebraic-space module to the Zariski opens of an étale
scheme. Its sections over `U` are precisely the given module's sections at
`U.toScheme → T → F`; the scalar action uses the canonical ring comparison.
For line modules this is the ordinary invertible module in the Zariski/étale
comparison: the inverse comparison functor is restriction to open subschemes.
Source: Stacks, Tags 03DX and 03FH
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeRestriction : F.Modules ⥤ ((F.etaleForget).obj T).Modules :=
  haveI := schemeOpens_isContinuous F T
  SheafOfModules.pushforward (F := schemeOpens F T) ⟨schemeOpensRingHom F T⟩

end AlgebraicGeometry.AlgebraicSpace
