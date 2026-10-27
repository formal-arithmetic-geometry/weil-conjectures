/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q51
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-! # Nilpotent group schemes

Source: Milne, Algebraic Groups (2017), Definition 6.34 and Remark 6.35, p.133
(blueprint: def-sfb-nilpotent-group-scheme).

Nilpotence means existence of a finite descending central series of closed normal
subgroup schemes. Commutators are tested on all commutative algebras, including
nonreduced ones. The series terms need not be smooth or connected.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A group scheme is nilpotent if it has a finite descending central series of
closed normal subgroup schemes. The first embedding is an isomorphism, the last
term is the trivial group scheme, and consecutive embeddings factor through one
another. The commutator condition is imposed on every algebra's points.
Source: Milne, Definition 6.34 and Remark 6.35, p.133
(blueprint: def-sfb-nilpotent-group-scheme). -/
def IsNilpotentGroupScheme {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : Prop :=
  ∃ (s : ℕ) (H : Fin (s + 1) → Grp (Over (Spec (.of k))))
    (i : ∀ j : Fin (s + 1), H j ⟶ G),
    (∀ j : Fin (s + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
      IsNormalSubgroupScheme (i j).hom.hom) ∧
    IsIso (i 0) ∧ Nonempty (H (Fin.last s) ≅ Grp.trivial _) ∧
    (∀ j : Fin s, ∃ l : H j.succ ⟶ H j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
    ∀ (j : Fin s) (A : Type u) [CommRing A] [Algebra k A]
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X)
      (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
        (H j.castSucc).X),
      ∃ z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (H j.succ).X,
        z ≫ (i j.succ).hom.hom =
          g * (h ≫ (i j.castSucc).hom.hom) * g⁻¹ * (h ≫ (i j.castSucc).hom.hom)⁻¹

end AlgebraicGeometry
