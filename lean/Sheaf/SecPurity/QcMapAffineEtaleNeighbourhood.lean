/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.SeparatedEtaleChart

/-!
# Affine étale neighbourhood of a quasi-compact scheme map

Source: Stacks Project, `spaces-properties.tex`, Tag 0APL (proposition-sheaf-fpqc),
with local quasi-finiteness from `morphisms.tex`, Tag 03WS
(blueprint: lem-a1-qc-map-affine-etale-neighbourhood).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `C` be a quasi-compact `S`-scheme and `c : C ⟶ E` an `S`-map to an algebraic
space.  There is an affine `S`-scheme `U` with a representable étale map to `E` such
that the represented pullback over `C` is surjective, étale, separated, and locally
quasi-finite.  The `IsPullback` witness records that `V` is the scheme fibre product
`C ×ₑ U` and that `p` is its projection.

Source: Stacks Project, `spaces-properties.tex`, Tag 0APL, proposition-sheaf-fpqc;
local quasi-finiteness is Tag 03WS (blueprint: lem-a1-qc-map-affine-etale-neighbourhood).

Proof: choose an affine étale atlas of `E`, retain finitely many affine charts covering
`c(C)` by quasi-compactness, and let `U` be their finite affine coproduct.  The induced
map is representable étale and its pullback `V` is surjective.  An affine scheme is
separated, and the étale projection is locally quasi-finite by Tag 03WS.
-/
theorem exists_affine_etale_neighbourhood
    {S : Scheme.{u}} (E : AlgebraicSpace S) (C : Over S)
    [CompactSpace C.left] (c : yoneda.obj C ⟶ E.obj.obj) :
    ∃ (U : Over S) (u : yoneda.obj U ⟶ E.obj.obj),
      IsAffine U.left ∧
        IsEtale u ∧
          ∃ (V : Over S) (p : V ⟶ C) (q : yoneda.obj V ⟶ yoneda.obj U),
            IsPullback q (yoneda.map p) u c ∧
              Surjective p.left ∧
                Etale p.left ∧
                  IsSeparated p.left ∧ Scheme.Hom.IsLocallyQuasiFinite p.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
