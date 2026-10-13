/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.NagataFixedBaseSeparatedStage

/-!
# Separated finite-presentation envelope

Source: blueprint `sec-nagata-compactification/sk-prop-nagata-sketch-envelope/`
`def-nagata-finite-type-closed-in-fp.md`, order 396
(blueprint: def-nagata-finite-type-closed-in-fp).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The explicit pair `Env_fp(X/S) = (X_fp, i_fp)` for a separated finite-type morphism
with qcqs base. Form the finite-presentation approximation system `FP(X/S)`, choose an initial
index of its nonempty cofiltered index category, and apply `nagataSeparatedStage` to that
system, giving `α_sep`. The first component is the model `X_{α_sep}` as an `S`-scheme (its
structure morphism is the system's `p.app α_sep`), the second the cone projection
`i_{α_sep} : X ⟶ X_{α_sep}`.
Source: blueprint `sec-nagata-compactification/sk-prop-nagata-sketch-envelope/`
`def-nagata-finite-type-closed-in-fp.md`, order 396
(blueprint: def-nagata-finite-type-closed-in-fp). -/
noncomputable def nagataFinitePresentationEnvelope {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] : Σ Y : Over S, X ⟶ Y.left :=
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let F := Classical.choice (f.nonempty_finitePresentationApproximation)
  let i₀ : F.I := Classical.choice (IsCofiltered.nonempty (C := F.I))
  letI : IsSeparated (F.π.app i₀ ≫ F.p.app i₀) :=
    (F.w i₀).symm ▸ (inferInstance : IsSeparated f)
  let αsep : F.I := nagataSeparatedStage F.isLimit F.p i₀
  ⟨Over.mk (F.p.app αsep), F.π.app αsep⟩

end AlgebraicGeometry
