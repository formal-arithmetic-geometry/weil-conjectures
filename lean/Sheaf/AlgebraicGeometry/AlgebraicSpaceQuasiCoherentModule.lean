/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Quasi-coherent modules on algebraic-space étale sites

Source: Stacks Project, Modules on Sites, Tag 03DL (local presentations);
Properties of Spaces, Tags 03ED, 03G9 and 03M0 (small étale sites and quasi-coherent modules)
(blueprint: def-trf-space-quasi-coherent-module).

The predicate is Mathlib's `SheafOfModules.IsQuasicoherent`, without a second definition.
The slice sheafification instances keep section and ring carriers in universe `u`,
although the site has objects in universe `u+1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Additive sheafification exists on every small étale slice in the section universe.
Source: Stacks Project, Properties of Spaces, Tag 03ED; Modules on Sites, Tag 03DL
(blueprint: def-trf-space-quasi-coherent-module).

Proof: for an étale scheme chart T → X, the localized site X_et/T is equivalent to
T_et: compose an étale T-scheme with T → X, and in the other direction retain the
scheme map to T. Both functors preserve the underlying jointly surjective étale
coverings. The affine étale basis of T has a u-small skeleton and u-small covering
refinements. The two additive plus constructions on this basis therefore have
u-small section groups and give additive sheafification. Transfer along the basis
and the slice equivalence gives the asserted weak sheafification. -/
@[instance] theorem etaleModuleOverHasWeakSheafify
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite) :
    HasWeakSheafify (X.etaleTopology.over T) AddCommGrpCat.{u} := by
  sorry

/-- Additive sheafification on every étale slice inverts exactly locally bijective maps.
Source: Stacks Project, Modules on Sites, Tag 03DL; Sites, sheafification
(blueprint: def-trf-space-quasi-coherent-module).

Proof: use the u-small affine étale basis of the chart scheme as in
etaleModuleOverHasWeakSheafify. A locally bijective map induces an isomorphism after
two plus constructions: local representatives give surjectivity and local equality
gives injectivity. Conversely, the sheafification units are locally bijective, so
an isomorphism of sheafifications implies local surjectivity and local injectivity
of the original map. Refinement and the equivalence with X_et/T transfer these
claims to the displayed slice topology. -/
@[instance] theorem etaleModuleOverWEqualsLocallyBijective
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite) :
    (X.etaleTopology.over T).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  sorry

/-- The full subcategory of modules locally presented by arbitrary coproducts of the ring.
Source: Stacks Project, Modules on Sites, Tag 03DL; Properties of Spaces, Tags 03G9 and 03M0
(blueprint: def-trf-space-quasi-coherent-module). -/
abbrev QCoh {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (SheafOfModules.isQuasicoherent X.structureSheaf).FullSubcategory

end AlgebraicGeometry.AlgebraicSpace
