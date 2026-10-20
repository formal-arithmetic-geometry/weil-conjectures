/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardExternalCupLeftCechExact
public import Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction
import Sheaf.AlgebraicGeometry.PicardLeftCechCupNaturality

/-! # Left external Cech cup specified on cochains

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tags 01FD and 07MB.
(blueprint: lem-sc-picard-left-cech-cup-construction).
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
(blueprint: lem-sc-picard-left-cech-cup-construction). -/
def IsPicardLeftCechCup
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules)
    (θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G) : Prop :=
  ∀ (F : X.Modules) (p q : ℕ)
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
        ((θ.app F).f ((p + q : ℕ) : ℤ)
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

/-- Construct the cochain cup naturally in the left coefficient, without comparisons.
Source: Stacks, Tags 01FD, 07MB and 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-left-cech-cup-construction).

Proof: In bidegree (p,q), pull the front-face section along the first projection
using its tensor-pullback unit and restrict to the product intersection. Do the
same with the back-face section and the second projection, and tensor the two
sections. The units and restrictions are k-linear because the projections lie
over Spec k; the section tensor is k-bilinear. The tensor universal property
therefore gives a linear map on each bidegree summand. The product universal
property gives its map to product-cover cochains, and the coproduct universal
property combines the bidegrees into each total degree. The alternating Cech
differential of the front/back expression has the Leibniz formula: the interior
terms cancel, leaving d(a) cup b plus (-1)^p a cup d(b). This is exactly the
tensor-total differential, so the components form a cochain map. In negative
bidegrees a factor is zero; take the unique zero map there. The extension
isomorphisms identify the nonnegative components with the displayed expression.
For every left coefficient morphism, naturality of the pullback unit, of
restrictions, and of section tensor proves the naturality square on each tuple
and pure tensor. These generate each summand and hence the total degree, proving
naturality on all modules. No quasi-coherence or affine diagonal is used.
Zero coefficients and empty schemes give zero sections; p=q=0 is the ordinary
pulled-back section tensor. Thus those cases obey the same formula. -/
theorem picardLeftCechCup_exists
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    ∃ θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G,
      IsPicardLeftCechCup f g G θ := by
  classical
  choose c hc using (fun F ↦ picardLeftCechCupComponent_exists f g F G)
  let θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G :=
    { app := c
      naturality := fun F H a ↦
        picardLeftCechCupComponent_naturality f g G a (c F) (c H) (hc F) (hc H) }
  refine ⟨θ, ?_⟩
  intro F
  exact hc F

end
end AlgebraicGeometry.Scheme.Modules
