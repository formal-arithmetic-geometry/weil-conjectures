/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.AlgebraicGeometry.PerfectThickClosure
import Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel
import Sheaf.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial

public import Sheaf.AlgebraicGeometry.PerfectHomLocalComparison
import Sheaf.AlgebraicGeometry.PerfectHomStageColimit

/-! # Exact geometric rows for the perfect Hom comparison
Source: Stacks Project, Tag 09RE, Mayer--Vietoris step, and Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-local-rows).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Construct exact rows with pinned central map and local neighboring maps.
This construction has no continuity hypotheses and asserts no isomorphisms.

Source: Stacks Project, Tag 09RE, Mayer--Vietoris induction step; Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-local-rows).

Proof: Pull U,V back along the open immersion t. Their union is Y, each is
quasi-compact, and their intersection is quasi-compact by quasi-separatedness.
Pull this cover back to every ring stage and to the limit. Restricted pullbacks
of P,Q are perfect by their local bounded finite locally free models and the
localizedPullback_perfectModel_iso comparison. Their shifts are perfect by
perfect_thick_closure. They have quasi-coherent cohomology by
schemeDerivedQCohProperty_of_isPerfect. Use the functorial K-injective-resolution
and short-exact-sequence boundary construction of the derived Mayer--Vietoris
triangle for Q at each stage and at the limit; do not independently choose
arbitrary distinguished triangles. Apply the represented homological
functor Hom(P,-). Derived open adjunction identifies the five terms as the
product on U,V in degree -1, the intersection in degree -1, the global Hom,
the product on U,V in degree zero, and the intersection in degree zero.
For every transition, the direct-image Mayer--Vietoris comparison applied to
Lh*Q, followed by naturality for Q → Rh*Lh*Q, gives all commuting squares,
including the boundary square. The counit-pinned derived pullback comparisons
identify the central transitions and limit maps with perfectStageMap and
perfectLimitMap. Explicitly, a stage arrow f is first composed with the
adjunction unit on Q. Its adjunct is pullback of f, followed by pullback of
that unit and the counit on the pulled-back Q. The triangle identity cancels
the latter two factors. Conjugating the resulting pullback of f by the fixed
composition comparisons gives exactly perfectStageMap; the same calculation
for a cocone leg gives perfectLimitMap. On local terms the direct-image
composition comparisons identify the units with the unit of the composite
adjunction, so the same cancellation gives the local pinning equations.
Take the filtered abelian-group colimit of these rows;
filtered colimits preserve exactness and their underlying sets are the set
colimits. The supplied H,d,ident give the same central set system, so uniqueness
of colimits supplies a. At the limit the central Hom identification supplies b.
Use perfect_hom_stage_colimit for the local Hom systems. The four neighboring
comparisons have precisely PerfectHomLocalComparison presentations on U,V and
their intersection, with the restricted perfect pairs
(and the degree -1 shifts); the two product terms use PerfectHomLocalMap.prod.
The adjunction and colimit identifications use PerfectHomLocalMap.equiv. This
proves the four locality assertions, without any appeal to continuity. Empty
opens have zero Hom groups and the same presentation and exactness argument. -/
theorem perfect_hom_mayerVietoris_local_rows
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (H : Set.Ici i ⥤ Type (max u w)) (d : Cocone H)
    (hd : IsColimit d)
    (ident : ∀ j : Set.Ici i, H.obj j ≃
      ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
       (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q))
    (htransition : ∀ (j k : Set.Ici i) (hjk : j ≤ k) (f : H.obj j),
      ident k (H.map (homOfLE hjk) f) =
        perfectStageMap R s j.property hjk (ident j f)) :
        ∃ (A B : ComposableArrows AddCommGrpCat.{max u w} 4) (φ : A ⟶ B)
          (a : d.pt ≃ A.obj' 2)
          (b : B.obj' 2 ≃
            ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
             (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
          A.Exact ∧ B.Exact ∧
          PerfectHomLocalMap R c i X s₀ U V (ComposableArrows.app' φ 0) ∧
          PerfectHomLocalMap R c i X s₀ U V (ComposableArrows.app' φ 1) ∧
          PerfectHomLocalMap R c i X s₀ U V (ComposableArrows.app' φ 3) ∧
          PerfectHomLocalMap R c i X s₀ U V (ComposableArrows.app' φ 4) ∧
          ∀ (j : Set.Ici i) (f : H.obj j),
            b ((ComposableArrows.app' φ 2) (a (d.ι.app j f))) =
              perfectLimitMap R c s j.property (ident j f) := by sorry

end AlgebraicGeometry
