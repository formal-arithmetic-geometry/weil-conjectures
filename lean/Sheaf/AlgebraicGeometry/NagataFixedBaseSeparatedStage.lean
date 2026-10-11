/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Selected stage for fixed-base separatedness

Source: literature/blueprint/master/blueprint/sec-nagata-compactification/
`sk-prop-nagata-sketch-envelope/def-nagata-fixed-base-separated-stage.md`
(blueprint: def-nagata-fixed-base-separated-stage).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Under the hypotheses of the fixed-base separated-stage existence theorem, choose
one witness and retain its index component (blueprint: def-nagata-fixed-base-separated-stage).
Source: blueprint `sec-nagata-compactification/sk-prop-nagata-sketch-envelope/`
`def-nagata-fixed-base-separated-stage.md`, order 394; Stacks Project, Tag 01ZH.
The witness is supplied by `Scheme.exists_isSeparated_app_of_isLimit`; the selected
index is used by the subsequent eventual-separatedness specification.
-/
noncomputable def nagataSeparatedStage {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S)
    [∀ i, QuasiCompact (t.app i)] (i₀ : I)
    [IsSeparated (c.π.app i₀ ≫ t.app i₀)] : I :=
  Classical.choose (Scheme.exists_isSeparated_app_of_isLimit hc t i₀)

end AlgebraicGeometry
