/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSheafComparison
public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite

/-! # Finite local stage representatives

Source: Stacks Project, Sites Tag 0A35 and Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-finite-local-stage-representatives).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A limit section has finitely many local representatives from one stage.
They are not asserted to be compatible at that stage.

Source: Stacks Project, Sites Tag 0A35, equation-compute-pullback-to-limit,
existence of local representatives; Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-finite-local-stage-representatives).

Proof: Restrict to the cofinal tail above i₀. The inverse image is left Kan extension
followed by sheafification, so locally t is the image of an original section of G,
restricted along an arrow to a base-changed original object. Refine both these
original objects and the representing objects to affine étale objects; restrict
the original sections along their affine open covers. The test object at the limit is affine (the
cone projections are affine),
hence quasi-compact; choose a finite subcover. Descend these finitely many objects,
arrows, and their commutative triangles to a common stage by finite-presentation
object and arrow descent. Covering descent makes their arrows a cover of the
base change of W at a possibly later stage. Apply the stage inverse-image unit to
the original sections and restrict along the descended arrows to obtain s.
The composition-unit equations show their images under β are the restrictions
of t. Only the individual local representatives have been descended here: no
matching equations between different representatives are descended. An empty
cover gives an empty family, so the statement also includes an empty test object. -/
theorem etaleSet_finiteLocalStageRepresentatives
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W : (D.obj (op i₀)).FullAffineEtale)
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj))) :
    let H := fun j : Over (op i₀) ↦ (Scheme.etaleSetPullback (D.map j.hom)).obj G
    let L := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
    let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let Y := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W.obj
    let e := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app W.obj
    let β := fun j : Over (op i₀) ↦
      etaleSetSheafComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G
    ∃ (j : Over (op i₀)) (n : ℕ) (V : Fin n → (D.obj j.left).Etale)
      (a : ∀ q, V q ⟶ Y j) (s : ∀ q, (H j).obj.obj (op (V q))),
      Sieve.ofArrows V a ∈ (D.obj j.left).smallEtaleTopology (Y j) ∧
      (∀ q, IsAffine (V q).left) ∧
      (∀ q, (β j).hom.app (op (V q)) (s q) =
        L.obj.map ((B j).map (a q) ≫ (e j).inv).op t) := by sorry

end AlgebraicGeometry
