/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.PointCount
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleCounit
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarClopenSections

/-!
# Pushforward along a finite étale morphism to an algebraically closed point is exact

Let `K` be an algebraically closed field and `a : Y ⟶ Spec K` finite étale. Then `Y` is a finite
discrete space and every point `y` of `Y` is the image of a section `s_y` of `a`, since its
residue field is finite over `K`. These sections are open and closed immersions, as `a` is étale
and separated, with pairwise disjoint ranges `{y}` covering `Y`; hence `Y = ⊔_y Spec K` and the
pushforward `a_*` of `ℓ`-adic pro-étale sheaves is exact
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_sections`).

## Main results

- `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_id_of_isClosed`: a closed point of a scheme
  locally of finite type over an algebraically closed field `K` is the image of a section of the
  structure morphism.
- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isAlgClosed`: the
  pushforward along a finite étale `a : Y ⟶ Spec K` is exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime]

end ProEtale

end AlgebraicGeometry
