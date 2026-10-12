/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
public import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison
import Sheaf.CategoryTheory.ColimitSites

/-! # Local surjective comparison with the stage presheaf colimit

Source: Stacks Project, Sites Tag 0A35 and Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-stage-presheaf-locally-surjective).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The comparison from the presheaf colimit to the limit push-pull sheaf
is locally surjective.

Source: Stacks Project, Sites Tag 0A35, equation-compute-pullback-to-limit,
and Étale Cohomology Tag 09YQ, via the affine-site colimit presentation.
(blueprint: lem-weil-pbc-sets-stage-presheaf-locally-surjective).

Proof: 1. Restrict the system to the cofinal upper tail of i₀. Apply the affine
   étale site colimit presentation to this tail. The base change of an affine
   test object W is affine, because the cone projection is affine. Transport
   the stage and limit inverse images through the full-affine restriction
   equivalences using the unit-compatible inverse-image comparison.
2. The construction in Sites 0A35, equation-compute-pullback-to-limit,
   represents a limit inverse-image section by stage inverse-image sections.
   Indeed inverse-image sections are locally represented by an original
   section of G and a map into its base change. The finite-presentation object
   and arrow descent clauses place these maps at stages. A covering that
   supplies these representatives has a finite affine refinement; descend
   that finite cover to a common stage using covering descent.
3. Overlaps of the local representatives agree at the limit. Descend the
   finite equations witnessing agreement to a later common stage, using the
   eventual-equality clause of the site presentation. The sheaf axiom at
   that stage glues the representatives. This is the existence part of
   0A35's section formula. The adjunction-unit and composition equations
   identify its map with etaleSetSectionComparison and hence, by the supplied
   component equations, with the leg of K.
4. Insert the resulting stage representative into the presheaf colimit
   using its coprojection. The presheaf colimit universal property says that
   its comparison image is the given limit section. Thus the image sieve is
   covering (indeed the argument gives a representative on W itself).
   Empty covers are allowed throughout; on an empty object the sheaf axiom
   gives the unique section, with no nonemptiness assumption on G. -/
theorem etaleSetStagePresheaf_locallySurjective
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1))) :
    let ρ := (Scheme.fullAffineEtaleInclusion (D.obj (op i₀))).sheafPushforwardContinuous
      (Type (u + 1)) (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
      (D.obj (op i₀)).smallEtaleTopology
    let A := fun j : Over (op i₀) ↦ ρ.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).sheafPushforwardContinuous
        (Type (u + 1)) ((D.obj (op i₀)).smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        ((D.obj j.left).smallGrothendieckTopology (P := @Etale) (Q := @Etale))).obj
          ((Scheme.etaleSetPullback (D.map j.hom)).obj G))
    let L := ρ.obj
      ((@Functor.sheafPushforwardContinuous _ _ _ _
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀)))
        (Type (u + 1)) _ ((D.obj (op i₀)).smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        (c.pt.smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        (Etale.isContinuous_overPullback (c.π.app (op i₀)))).obj
          ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G))
    ∀ (E : (Over (op i₀))ᵒᵖ ⥤
        Sheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀))) (Type (u + 1)))
      (K : Cocone E),
      (∀ j : Over (op i₀), E.obj (op j) = A j) → K.pt = L →
      (∀ (j k : Over (op i₀)) (a : k ⟶ j)
        (W : (D.obj (op i₀)).FullAffineEtale),
        Arrow.mk ((E.map a.op).hom.app (op W)) =
          Arrow.mk (etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
            ((D.map_comp a.left j.hom).symm.trans
              (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W.obj)) →
      (∀ (j : Over (op i₀)) (W : (D.obj (op i₀)).FullAffineEtale),
        Arrow.mk ((K.ι.app (op j)).hom.app (op W)) =
          Arrow.mk (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
            (c.π.app (op i₀)) (c.w j.hom) G W.obj)) →
      Presheaf.IsLocallySurjective
      (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
      (colimit.desc
        (E ⋙ sheafToPresheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
          (Type (u + 1)))
        ((sheafToPresheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
          (Type (u + 1))).mapCocone K)) := by sorry

end AlgebraicGeometry
