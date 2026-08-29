/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Complement

/-!
# Restriction along a decomposition into two disjoint opens is conservative

Let `j : U ⟶ X` and `k : W ⟶ X` be open immersions whose ranges are complementary opens of
`X`. This file proves that a morphism of sheaves on the small étale site of `X` which becomes
invertible after restricting along `j` and along `k` is itself invertible
(`AlgebraicGeometry.Etale.isIso_of_isCompl_of_isIso_openImmersionRestriction`).

The statement is proved objectwise. An étale `X`-scheme `V` is cut by the decomposition into
the two pieces `V ×_X U` and `V ×_X W`, and
`AlgebraicGeometry.Scheme.Etale.isIso_app_of_isIso_clopen` reduces invertibility at `V` to
invertibility at those two pieces. Each piece lies over the corresponding open
(`AlgebraicGeometry.Scheme.Etale.range_part_hom_base_subset`), so its structure morphism
factors through the corresponding open immersion, which identifies it with the image of an
étale `U`- resp. `W`-scheme under the localization functor
(`AlgebraicGeometry.Scheme.Etale.isoMapLiftOfRangeSubset`). The sections of a restricted sheaf
over an étale `U`-scheme are by definition the sections of the original sheaf over its image
(`AlgebraicGeometry.Etale.openImmersionRestriction_map_hom_app`), so invertibility of the
restricted morphism transports back along `CategoryTheory.NatTrans.isIso_app_of_iso`.

The comparison `j_! ⟶ j_*` for an open immersion `j` with clopen range, and its consequence
for a proper morphism, are deduced from this in
`WeilConjectures.SixFunctors.LowerShriek.Proper`.

## Main results

- `AlgebraicGeometry.Etale.isIso_app_of_isIso_openImmersionRestriction`: a morphism of sheaves
  whose restriction along `j` is invertible is invertible at every étale `X`-scheme mapping
  into the range of `j`.
- `AlgebraicGeometry.Etale.isIso_of_isCompl_of_isIso_openImmersionRestriction`: the
  conservativity statement for a decomposition of `X` into two complementary opens.
-/

@[expose] public section

universe u' u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U W X : Scheme.{u}} (j : U ⟶ X) (k : W ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
variable {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G')

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- **Invertibility of `j^* φ` gives invertibility of `φ` over the range of `j`.** If `V` is
an étale `X`-scheme mapping into the range of `j`, it lifts through `j`, and the lift
identifies `V` with the image of an étale `U`-scheme `V'` under the localization functor; the
sections of `j^* G` over `V'` are the sections of `G` over `V`.

```
         V.left                  G(V) ←───≅──── (j^* G)(V')
        ╱    │                     │                │
    V' ╱     │ V.hom           φ_V │                │ (j^* φ)_{V'}
      ↙      ↓                     ↓                ↓
     U ────→ X                  G'(V) ←──≅──── (j^* G')(V')
         j
```
-/
lemma Etale.isIso_app_of_isIso_openImmersionRestriction
    (h : IsIso ((Etale.openImmersionRestriction A j).map φ)) (V : X.Etale)
    (hV : Set.range V.hom.base ⊆ Set.range j.base) :
    IsIso (φ.hom.app (op V)) := by
  have h1 : IsIso (((Etale.openImmersionRestriction A j).map φ).hom.app
      (op (Scheme.Etale.liftOfRangeSubset j V hV))) := inferInstance
  rw [Etale.openImmersionRestriction_map_hom_app] at h1
  exact NatTrans.isIso_app_of_iso φ.hom (Scheme.Etale.isoMapLiftOfRangeSubset j V hV).op.symm

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- **The restrictions along a decomposition of `X` into two complementary opens are jointly
conservative.** A morphism of sheaves on the small étale site of `X` which becomes invertible
after restricting along `j` and along `k` is invertible.

Each étale `X`-scheme `V` is cut into the two pieces lying over the two opens, and each piece
maps into the range of the corresponding open immersion, where the previous lemma applies.

```
     V|_U ─────→ V ←───── V|_W
      │          │          │
      ↓          ↓          ↓
      U ───j───→ X ←───k─── W
```
-/
lemma Etale.isIso_of_isCompl_of_isIso_openImmersionRestriction
    (h : IsCompl j.opensRange k.opensRange)
    (hj : IsIso ((Etale.openImmersionRestriction A j).map φ))
    (hk : IsIso ((Etale.openImmersionRestriction A k).map φ)) :
    IsIso φ := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ A), NatTrans.isIso_iff_isIso_app]
  rintro ⟨V⟩
  refine Scheme.Etale.isIso_app_of_isIso_clopen V (disjoint_iff.mp h.disjoint)
    (codisjoint_iff.mp h.codisjoint) φ ?_
  rintro (_ | _)
  · exact Etale.isIso_app_of_isIso_openImmersionRestriction A j φ hj _
      (Scheme.Etale.range_part_hom_base_subset V j.opensRange)
  · exact Etale.isIso_app_of_isIso_openImmersionRestriction A k φ hk _
      (Scheme.Etale.range_part_hom_base_subset V k.opensRange)

end AlgebraicGeometry
