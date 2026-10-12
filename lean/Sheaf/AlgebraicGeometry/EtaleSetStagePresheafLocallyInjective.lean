/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
public import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Sites.LocallyInjective
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison
import Sheaf.CategoryTheory.ColimitSites
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Local injective comparison with the stage presheaf colimit

Source: Stacks Project, Sites Tag 0A35 and Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-stage-presheaf-locally-injective).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The comparison from the presheaf colimit to the limit push-pull sheaf
is locally injective.

Source: Stacks Project, Sites Tag 0A35, equation-compute-pullback-to-limit,
and Étale Cohomology Tag 09YQ, via the affine-site colimit presentation.
(blueprint: lem-weil-pbc-sets-stage-presheaf-locally-injective).

Proof: 1. Work on the cofinal upper tail of i₀. A section of the presheaf colimit
   on W is represented by a section of a stage push-pull sheaf on W; two such
   sections can be placed at one common stage by directedness. The supplied
   object and component equalities identify these representatives and their
   images with the canonical inverse-image section comparisons.
2. Use the affine-site colimit presentation and transport across full-affine
   restriction, preserving adjunction units. In the inverse-image description
   of Sites 0A35, equality of the two limit images is witnessed locally by
   equalities between representatives in the defining filtered colimits.
   Each witness uses finitely many objects, arrows and equations. The object,
   arrow and eventual-equality clauses of the site presentation descend these
   data together to a common later stage.
3. Coverings in the limit affine site have finite stage presentations. Descend
   the coverings witnessing equality, moving all their finitely many data to
   a common stage. The sheaf separatedness axiom there identifies the two
   descended sections. The filtered-colimit equality criterion identifies
   their images in the presheaf colimit. This is the equality part of 0A35's
   displayed section formula; its unit equation identifies the maps with the
   maps specified in the hypotheses.
4. On each test object the two presheaf sections therefore agree (in
   particular they agree on a covering sieve), which is local injectivity.
   The empty-object case uses the empty covering and the uniqueness of a
   sheaf section there; it requires no chosen section of G. -/
theorem etaleSetStagePresheaf_locallyInjective
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
      Presheaf.IsLocallyInjective
      (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
      (colimit.desc
        (E ⋙ sheafToPresheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
          (Type (u + 1)))
        ((sheafToPresheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
          (Type (u + 1))).mapCocone K)) := by sorry

end AlgebraicGeometry
