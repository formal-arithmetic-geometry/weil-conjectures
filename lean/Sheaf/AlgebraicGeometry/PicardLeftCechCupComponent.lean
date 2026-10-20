/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardExternalCupLeftCechExact
public import Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction
import Sheaf.AlgebraicGeometry.PicardExternalCechCupComponent
import Sheaf.Algebra.Homology.TensorTotalExtensionCoordinates

/-! # A single extended external Cech cup component

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tags 01FD and 07MB.
(blueprint: lem-sc-picard-left-cech-cup-component).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Specify the external Alexander--Whitney coordinates before taking homology.
The source is the tensor total of the extended factors, as in the left Cech functor.
Source: Stacks, Tags 01FD, 07MB and 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-left-cech-cup-component). -/
def IsPicardLeftCechCupComponent
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (F : X.Modules) (G : Y.Modules)
    (c : (picardLeftTensorCechFunctor f g G).obj F ⟶
      (picardLeftProductCechFunctor f g G).obj F) : Prop :=
  ∀ (p q : ℕ)
    (a : ((picardScalarCechFunctor f (picardFiniteAffineOpens X)).obj F).X p)
    (b : ((picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G).X q)
    (y : Fin (p + q + 1) →
      X.affineCover.finiteSubcover.I₀ × Y.affineCover.finiteSubcover.I₀),
    TopCat.Presheaf.cechComplexFunctorXAddEquiv (picardProductAffineOpens f g)
      (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
      (p + q)
      ((((picardScalarCechFunctor (pullback.fst f g ≫ f)
        (picardProductAffineOpens f g)).obj (externalCupCoefficients f g F G)).extendXIso
          ComplexShape.embeddingUpNat (show ((p + q : ℕ) : ℤ) = (p + q : ℕ) from rfl)).hom
        (c.f ((p + q : ℕ) : ℤ)
          (HomologicalComplex.ιMapBifunctor
            (((picardScalarCechFunctor f (picardFiniteAffineOpens X)).obj F).extend
              ComplexShape.embeddingUpNat)
            (((picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G).extend
              ComplexShape.embeddingUpNat)
            (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
            (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by
              change (p : ℤ) + (q : ℤ) = ((p + q : ℕ) : ℤ)
              omega)
            (((((picardScalarCechFunctor f (picardFiniteAffineOpens X)).obj F).extendXIso
                ComplexShape.embeddingUpNat (show (p : ℤ) = (p : ℤ) from rfl)).inv a) ⊗ₜ[k]
              ((((picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G).extendXIso
                ComplexShape.embeddingUpNat (show (q : ℤ) = (q : ℤ) from rfl)).inv b))))) y =
      tmulSection
        (picardCechPullSection (pullback.fst f g) F
          (⨅ l, picardFiniteAffineOpens X (y (cupFront p q l)).1) _
          (picardProductCechFace f g (picardFiniteAffineOpens X)
            (picardFiniteAffineOpens Y) y (cupFront p q)).1
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv (picardFiniteAffineOpens X)
            (scalarPresheaf f F) p a (fun l ↦ (y (cupFront p q l)).1)))
        (picardCechPullSection (pullback.snd f g) G
          (⨅ l, picardFiniteAffineOpens Y (y (cupBack p q l)).2) _
          (picardProductCechFace f g (picardFiniteAffineOpens X)
            (picardFiniteAffineOpens Y) y (cupBack p q)).2
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv (picardFiniteAffineOpens Y)
            (scalarPresheaf g G) q b (fun l ↦ (y (cupBack p q l)).2)))

/-- Existence of one extended cup cochain map, without coefficient naturality.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tags 01FD and 07MB.
(blueprint: lem-sc-picard-left-cech-cup-component).

Proof: Take the natural-index Alexander--Whitney component of
picardExternalCechCupComponent_exists for the finite affine open families.
Its source is the total of the natural-index tensor bicomplex. Extend it by zero.
Identify this extended total with the total of the extended factors: on a
nonnegative bidegree use the two extension isomorphisms, and on a bidegree with
one negative index use the unique map from the zero tensor factor. The coproduct
universal property gives the comparison in each degree. These comparisons commute
with both differentials, since extension respects the factor differentials and
all components involving negative indices vanish. Compose the comparison with
the extended natural-index cup component. Its inclusion equation and the
extension isomorphisms give precisely the displayed coordinates. No naturality
in F is asserted. Empty covers and zero coefficients give zero pairings, and
p=q=0 is the ordinary pulled-back section tensor. -/
theorem picardLeftCechCupComponent_exists
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (F : X.Modules) (G : Y.Modules) :
    ∃ c : (picardLeftTensorCechFunctor f g G).obj F ⟶
      (picardLeftProductCechFunctor f g G).obj F,
      IsPicardLeftCechCupComponent f g F G c  := by
  obtain ⟨c, hc⟩ := picardExternalCechCupComponent_exists f g
    (picardFiniteAffineOpens X) (picardFiniteAffineOpens Y) F G
  obtain ⟨e, he⟩ := HomologicalComplex.tensorTotalExtend_coordinates
    ((picardScalarCechFunctor f (picardFiniteAffineOpens X)).obj F)
    ((picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G)
  refine ⟨e ≫ HomologicalComplex.extendMap c ComplexShape.embeddingUpNat, ?_⟩
  intro p q x y z
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  rw [HomologicalComplex.extendMap_f _ _
    (show ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ) from rfl)]
  simp only [ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply, he]
  exact hc p q x y z

end
end AlgebraicGeometry.Scheme.Modules
