/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf

/-!
# Étale sheaves supported in low dimension

Let `B` be a scheme of finite type over a field `K` and `N` a torsion abelian étale sheaf on `B`
whose geometric stalks vanish at every point `y` with `trdeg_K κ(y) > a`. For a closed subset
`Z ⊆ B` with open complement `j_Z : B ∖ Z ⟶ B`, let `N_Z = ker(N ⟶ j_Z* j_Z^* N)` be the
subsheaf of sections supported in `Z`. Then `N` is the filtered union of the `N_Z` over the
closed `Z` of dimension at most `a` (`AlgebraicGeometry.Etale.exists_covering_supportedIn`,
blueprint `lem-sc-support-dimension-union`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- The ring homomorphism `K ⟶ κ(y)` from the ground field `K` of a `K`-scheme `B` (with
structure morphism `b`) to the residue field at a point `y` of `B`. -/
noncomputable def residueFieldHomOfOver {K : Type u} [Field K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) (y : B) : K →+* B.residueField y :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop ≫ B.presheaf.germ ⊤ y trivial ≫
    B.residue y).hom

/-- The transcendence degree `trdeg_K κ(y)` of the residue field at a point `y` of a `K`-scheme
`B` (with structure morphism `b`). -/
noncomputable def residueFieldTrdeg {K : Type u} [Field K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) (y : B) : Cardinal.{u} :=
  letI := (residueFieldHomOfOver b y).toAlgebra
  Algebra.trdeg K (B.residueField y)

end Scheme

namespace Etale

variable {B : Scheme.{u}}

/-- The subsheaf `N_Z = ker(N ⟶ j_* j^* N)` of sections of `N` supported in the closed
complement of an open `U` of `B`, where `j : U ⟶ B` is the inclusion. -/
noncomputable def supportedIn (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N)

/-- The inclusion `N_Z ⟶ N` of the sections supported in the complement of `U`. -/
noncomputable def supportedInι (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) : supportedIn N U ⟶ N :=
  kernel.ι _

/-- Blueprint `lem-sc-support-dimension-union`: A sheaf supported in low dimension is a filtered
union.

Let `B` be a scheme of finite type over a field `K` (structure morphism `b`), `a ≥ 0`, and `N` a
torsion abelian étale sheaf on `B` with zero geometric stalk at every point `y` with
`trdeg_K κ(y) > a`: for every separably closed field `Ω` and every geometric point
`s : Spec Ω ⟶ B` lying over such a `y`, `s^* N = 0`. For a closed `Z ⊆ B` with complement
`j_Z : B ∖ Z ⟶ B` let `N_Z = ker(N ⟶ j_Z* j_Z^* N)`. Then `N` is the union of the subsheaves
`N_Z` over the closed `Z` of dimension at most `a`: every section of `N` lies, locally on an
étale covering, in some `N_Z`. Since the `N_Z ⟶ N` are monomorphisms and the closed sets of
dimension at most `a` form a directed system under finite unions, this says that the canonical
map `colim_Z N_Z ⟶ N` is an isomorphism, which is the blueprint's formulation. -/
theorem exists_covering_supportedIn {K : Type u} [Field K] (b : B ⟶ Spec (.of K))
    [LocallyOfFiniteType b] [QuasiCompact b] (a : ℕ)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (hN : N.IsTorsion)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < Scheme.residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj N)) :
    ∀ (V : B.Etale) (s : N.obj.obj (Opposite.op V)), ∃ R ∈ B.smallEtaleTopology V,
      ∀ ⦃W : B.Etale⦄ (g : W ⟶ V), R g → ∃ (U : B.Opens)
        (_ : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a)
        (t : (supportedIn N U).obj.obj (Opposite.op W)),
          (supportedInι N U).hom.app _ t = N.obj.map g.op s :=
  sorry

end Etale

end AlgebraicGeometry
