/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!
# Module lower shriek for a quasi-compact compactification

Source: blueprint main-20261015, sec-six-functors-basics,
sk-def-sfb-module-lower-shriek/def-sfb-module-compactification-lower-shriek.md
(blueprint: def-sfb-module-compactification-lower-shriek).

The compactification has a quasi-compact open immersion, as in the referenced Nagata
compactification datum. We specialize the existing module-object construction to that
recorded domain; the coefficient transport and both constituent functors are reused.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The lower shriek attached to a compactification with quasi-compact open immersion:
extension by zero along its open immersion followed by module pushforward along its proper
map. The latter includes restriction of scalars along the canonical coefficient morphism.
Source: blueprint main-20261015, def-sfb-module-compactification-lower-shriek, displayed formula,
and sk-def-nagata-sketch-data, compactification clause
(blueprint: def-sfb-module-compactification-lower-shriek). -/
noncomputable def quasiCompactificationLowerShriek
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification.QuasiCompactObjects f) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) :=
  compactificationLowerShriek Λ c.obj

end AlgebraicGeometry.ProEtale.CondensedRing
