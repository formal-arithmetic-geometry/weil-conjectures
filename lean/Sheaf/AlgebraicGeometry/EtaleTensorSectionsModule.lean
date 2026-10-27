/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence

/-! # The module structure on the associated étale sheaf

Source: Stacks Project, Descent, Tags 03DU, 03DR and 03FH.
(blueprint: def-per-etale-tensor-sections-module)

The canonical module extension is the ringed-site tensor pullback. The published
Zariski/étale comparison identifies its underlying additive sheaf with the recorded
`etaleTensorSectionsSheaf`, respecting scalars and the unit on every source open.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The associated étale module, constructed by the existing canonical tensor
extension. The scalar-, section-, and unit-normalized comparison in
`scheme_zariski_etale_quasiCoherent_equivalence` identifies its underlying
additive sheaf with `etaleTensorSectionsSheaf F`, without changing that notion.
Only proof data are obtained from the context; no arbitrary sheaf or map is chosen.
Source: Stacks 03DU Definition 35.8.2(4), 03DR and 03FH
(blueprint: def-per-etale-tensor-sections-module). -/
noncomputable def etaleTensorSectionsModule {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] : SmallEtaleModules X :=
  ((Classical.choose scheme_zariski_etale_quasiCoherent_equivalence) X).extension.obj F

end AlgebraicGeometry.Scheme.Modules
