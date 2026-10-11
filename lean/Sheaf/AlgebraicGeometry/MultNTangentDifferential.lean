/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
import Sheaf.AlgebraicGeometry.SchemeTangentSpace
import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-!
# Differential of multiplication by d

Source: literature/stacks-project/groupoids.tex, proof of lemma-group-scheme-addition-
 tangent-vectors
(blueprint: lem-sc-mult-n-tangent-differential).
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The differential of multiplication by `d` at the identity is scalar multiplication by `d`.
Source: literature/stacks-project/groupoids.tex, proof of lemma-group-scheme-addition-
 tangent-vectors
(blueprint: lem-sc-mult-n-tangent-differential).

Proof for stage 3:
1. By lem-sc-mult-n-homomorphism, `[d]` fixes the identity section. Hence it fixes the
   identity point and its induced residue-field map is an isomorphism (the identity is
   k-rational), supplying transport witnesses `hp` and `he`.
2. For `d = 1`, the inductive definition of lem-sc-mult-n-homomorphism and the unit axiom
   of def-sc-group-scheme
   identify `[1]` with the identity, whose tangent map is the identity.
3. Inductively, `[d+1] = m ∘ ([d], id)`. Functoriality in def-sc-scheme-tangent-space
   and the product identification reduce its differential to `(d • v, v)`. Then
   lem-sc-group-addition-tangent-differential gives `d • v + v = (d+1) • v`.
-/
theorem mult_n_tangent_differential (k : Type u) [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G] (d : ℕ)
    (hd : 1 ≤ d) :
    ∃ hp : (𝟙 G ^ d).left (GrpObj.onePoint G) = GrpObj.onePoint G,
    ∃ he : Function.Bijective
      (((𝟙 G ^ d).left.residueFieldMap (GrpObj.onePoint G)).hom),
      ∀ v : schemeTangentSpace k G.left G.hom (GrpObj.onePoint G),
        (hp ▸
          (schemeTangentMap k G.left G.left G.hom G.hom (𝟙 G ^ d).left
            (𝟙 G ^ d).w (GrpObj.onePoint G) he v)) = d • v := by
  sorry

end AlgebraicGeometry
