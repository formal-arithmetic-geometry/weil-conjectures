/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Compactness.Compact
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale

/-!
# Étale locality of quasi-compact separated algebraic-space morphisms

Source: Stacks Project, `spaces-morphisms.tex`, Tags 03KG and 03KM
(blueprint: lem-trf-space-qc-separated-etale-local).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace AlgebraicSpace

variable {S : Scheme.{u}}

/-- The scheme-theoretic atlas condition used in quasi-compactness of a map of
presheaves on `(Sch/S)`.  The pair `(q,p)` is the map to the fibre product of
`g` with the affine test map `h`; its induced map to that fibre product is
required to be étale and surjective, and `U` is quasi-compact.
Source: Stacks, Spaces, Tag 03E3 (blueprint: lem-trf-space-qc-separated-etale-local). -/
def IsQuasiCompactPresheafMap {G F : (Over S)ᵒᵖ ⥤ Type u} (g : G ⟶ F) : Prop :=
  ∀ (Z : Over S) (_ : IsAffine Z.left) (h : yoneda.obj Z ⟶ F),
    ∃ (U : Over S) (p : U ⟶ Z) (q : yoneda.obj U ⟶ G)
      (hp : q ≫ g = yoneda.map p ≫ h),
      CompactSpace U.left ∧
        IsEtale (CategoryTheory.Limits.pullback.lift q (yoneda.map p) hp) ∧
        IsSurjective (CategoryTheory.Limits.pullback.lift q (yoneda.map p) hp)

/-- The diagonal of a presheaf morphism, viewed as a map to its presheaf fibre
product.  Source: Stacks, Spaces, Tag 03KM
(blueprint: lem-trf-space-qc-separated-etale-local). -/
noncomputable def diagonalPresheafMap {G F : (Over S)ᵒᵖ ⥤ Type u} (g : G ⟶ F) :
    G ⟶ CategoryTheory.Limits.pullback g g :=
  CategoryTheory.Limits.pullback.lift (𝟙 G) (𝟙 G) (by simp)

/-- A presheaf morphism has separated diagonal when every scheme test of its
diagonal is a closed immersion.  Source: Stacks, Spaces, Tag 03KM
(blueprint: lem-trf-space-qc-separated-etale-local). -/
def IsSeparatedPresheafMap {G F : (Over S)ᵒᵖ ⥤ Type u} (g : G ⟶ F) : Prop :=
  AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
    (diagonalPresheafMap g)

/-- An étale family of schemes over an algebraic space is jointly surjective on
all scheme tests.  Source: Stacks, Spaces, Tag 025Y and
Spaces-Morphisms, Tags 03KG and 03KM
(blueprint: lem-trf-space-qc-separated-etale-local). -/
def IsJointlySurjectiveEtaleFamily (Y : AlgebraicSpace S) (I : Type v)
    (Yᵢ : I → Over S) (a : ∀ i, yoneda.obj (Yᵢ i) ⟶ Y.obj.obj) : Prop :=
  (∀ i, IsEtale (a i)) ∧
    ∀ (T : Over S) (x : Y.obj.obj.obj (op T)),
      ∃ (i : I) (y : (yoneda.obj (Yᵢ i)).obj (op T)), (a i).app (op T) y = x

/-- Quasi-compactness and separation of algebraic-space morphisms are étale
local on the target.  Source: Stacks Project, `spaces-morphisms.tex`, Tags
03KG (lemma-quasi-compact-local) and 03KM (lemma-separated-local)
(blueprint: lem-trf-space-qc-separated-etale-local).

Proof: for the forward implication, base change of the quasi-compact atlas and
of the closed diagonal preserves the two properties.  For the converse, test
the diagonal on a scheme and descend its closed-immersion property along the
jointly surjective étale family, which is fpqc.  For quasi-compactness, refine
the induced cover over each affine test by finitely many affine étale opens,
apply the local hypotheses, and take the finite disjoint union of the resulting
quasi-compact atlases.  The finite union is a quasi-compact scheme and the
composition of the two étale covering families is again an étale covering.
The scheme-level base-change, fpqc descent, affine refinement, and covering
composition facts are supplied by the proof dependencies recorded in the DAG. -/
theorem quasiCompact_separated_etaleLocal
    (X Y : AlgebraicSpace S) (f : X ⟶ Y) (I : Type v)
    (Yᵢ : I → Over S) (a : ∀ i, yoneda.obj (Yᵢ i) ⟶ Y.obj.obj)
    (ha : IsJointlySurjectiveEtaleFamily Y I Yᵢ a) :
    (IsQuasiCompactPresheafMap f.hom.hom ∧ IsSeparatedPresheafMap f.hom.hom) ↔
      ∀ i, IsQuasiCompactPresheafMap
          (CategoryTheory.Limits.pullback.snd f.hom.hom (a i)) ∧
        IsSeparatedPresheafMap (CategoryTheory.Limits.pullback.snd f.hom.hom (a i)) := by
  sorry

end AlgebraicSpace

end AlgebraicGeometry
