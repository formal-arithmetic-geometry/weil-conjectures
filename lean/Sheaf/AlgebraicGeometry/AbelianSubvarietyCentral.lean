/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity

/-!
# Abelian subvarieties are central

Source: Milne, Algebraic Groups, Corollary 8.13, p.151 and Definition 8.15;
Milne, Abelian Varieties, Theorem 1.1 (Rigidity), pp.8–9.
(blueprint: lem-sfb-abelian-subvariety-central)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- An abelian subvariety of a smooth connected separated finite-type group over an
algebraically closed field is central on points over every commutative algebra, and normal.

Source: Milne, Algebraic Groups, Corollary 8.13, p.151 and Definition 8.15.
(blueprint: lem-sfb-abelian-subvariety-central)

Proof: `lem-sc-abelian-variety-characterization` gives geometric integrality of `A`,
hence geometric connectedness and reducedness. Form the commutator morphism
`c : A ×_k G → G`, sending `(a,g)` to `i(a) g i(a)⁻¹ g⁻¹`, using the group scheme
operations (`def-sc-group-scheme`). Its restrictions to both identity axes are the
constant identity morphism. Apply `lem-sc-rigidity` (Milne, Abelian Varieties,
Theorem 1.1, pp.8–9) to the proper factor `A`, connected parameter `G`, separated
target `G`, and fibre at the identity of `G`. It gives `c = h ∘ pr₂`. Restricting to
`{e_A} × G` shows that `h`, and thus `c`, is the constant identity morphism.
Evaluate this morphism equality on every algebra's points and cancel inverses to
obtain `i(a) g = g i(a)`. Conjugation therefore fixes the image pointwise, so each
image subgroup is normal, exactly `def-sc-group-scheme-subgroup`.
-/
theorem abelianSubvariety_central {k : Type u} [Field k] [IsAlgClosed k]
    (G A : Over (Spec (.of k))) [GrpObj G] [GrpObj A]
    [Smooth G.hom] [ConnectedSpace G.left] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsAbelianVariety A]
    (i : A ⟶ G) [IsClosedSubgroupScheme i] :
    (∀ (B : Type u) [CommRing B] [Algebra k B]
      (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) ⟶ A)
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) ⟶ G),
      (a ≫ i) * g = g * (a ≫ i)) ∧ IsNormalSubgroupScheme i := by
  sorry

end AlgebraicGeometry
