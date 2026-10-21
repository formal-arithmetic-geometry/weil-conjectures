/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits

/-!
# Canonical geometric stalk comparison for signed total tensor complexes

Source: Stacks Project, sites-cohomology.tex, Tag 07A4,
lemma-pullback-tensor-product, final paragraph; sites-modules.tex, Tag 03EL,
lemma-tensor-product-pullback (blueprint: lem-sfb-etale-stalk-total-tensor-comparison).

The module-valued sheaf encoding is the constant-ring module equivalence already
used by the parent derived comparison. Tensor is the existing direct-sum total tensor.
The lifted point has the same pointed-neighbourhood colimit, by `uliftSheafFiberIso`.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme
variable {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
/-- Small coproducts used for totalization. Source: Stacks 07A4
(blueprint: lem-sfb-etale-stalk-total-tensor-comparison). -/
noncomputable instance etaleStalkTotalTensor_smallColimits :
    HasColimitsOfSize.{0, 0} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  @hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _ _
    (IsGrothendieckAbelian.hasColimits
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))

/-- The countable coproduct interface for the existing totalization coproducts.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-stalk-total-tensor-comparison). -/
noncomputable instance etaleStalkTotalTensor_countableCoproducts :
    HasCountableCoproducts (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) where
  out J := (etaleStalkTotalTensor_smallColimits (T := T) (A := A)).has_colimits_of_shape
    (Discrete J)

/-- The unique natural chain isomorphism from the stalk of the direct-sum total tensor
of two unbounded complexes to the total tensor of their stalks, normalized on every summand.
The ordinary comparison is the canonical `OplaxMonoidal.δ`, the inverse of the tensorator
whose pure-germ formula is `etale_stalk_tensor_unique`. Fixed-ring module sheaves are
modules over the constant ring sheaf by `constant_ring_module_sheaves`.

Source: Stacks Project, sites-cohomology.tex, Tag 07A4,
lemma-pullback-tensor-product, final paragraph; sites-modules.tex, Tag 03EL,
lemma-tensor-product-pullback (blueprint: lem-sfb-etale-stalk-total-tensor-comparison).

Proof, following the six steps of the node:
1. Restrict along constant sections. Local constancy makes fixed-ring bilinearity
balanced over the constant ring sheaf, by the sheaf tensor universal property
(def-pur-sheaf-tensor-product). Invert the ordinary tensor-stalk isomorphism of
lem-pod-etale-stalk-tensor-scalar; its inverse sends a tensor germ to the tensor of germs.
2. Use lem-weil-pbc-module-sheaves-colimits-forgetful and
lem-kun-stalks-commute-colimits to obtain module coproduct preservation. Stalks preserve
addition and negatives, as is checked on germs.
3. In degree n, compose the inverse coproduct comparison with the direct sum of the
ordinary tensor comparisons. Its inverse is specified by the inverse ordinary comparison
on each summand. The coproduct universal property (def-weil-pbc-category-colimit)
checks both inverse equations and the displayed normalization.
4. Check the chain equation on each source coprojection. The total differential
(def-pc-tensor-complex-sheaves) has the two terms d_C tensor 1 and
(-1)^p times 1 tensor d_D. Ordinary tensor naturality and additivity identify both terms
with the corresponding target differential. The source stalk coprojections jointly
determine maps, so this gives a chain map; its degreewise inverse is also a chain map.
5. Check both-variable naturality on each summand, where it is ordinary tensor
naturality for f^p and g^q. Joint determination gives equality of chain maps.
6. The normalization uniquely determines each degree map and hence the whole family.
Only the countable direct sums indexed by p+q=n are used; each differential has two
outgoing terms per summand. Thus unbounded complexes require no products or flatness. -/
theorem etale_stalk_total_tensor_comparison :
    ∃! θ : ∀ C D : CochainComplex
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor C D (curriedTensor _)) ≅
        CochainComplex.mapBifunctor
          ((((pointSmallEtale t).ulift.{u + 1}.sheafFiber
            (A := ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj C)
          ((((pointSmallEtale t).ulift.{u + 1}.sheafFiber
            (A := ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj D)
          (curriedTensor _),
      (∀ (C D : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
          (p q n : ℤ) (h : p + q = n),
        (pointSmallEtale t).ulift.{u + 1}.sheafFiber.map
            (CochainComplex.ιMapBifunctor C D (curriedTensor _) p q n h) ≫
            (θ C D).hom.f n =
          Functor.OplaxMonoidal.δ
              ((pointSmallEtale t).ulift.{u + 1}.sheafFiber
                (A := ModuleCat.{u + 1} A)) (C.X p) (D.X q) ≫
            CochainComplex.ιMapBifunctor
              ((((pointSmallEtale t).ulift.{u + 1}.sheafFiber
                (A := ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj C)
              ((((pointSmallEtale t).ulift.{u + 1}.sheafFiber
                (A := ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj D)
              (curriedTensor _) p q n h) ∧
      (∀ (C C' D D' : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
          (f : C ⟶ C') (g : D ⟶ D'),
        (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
            (A := ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ)) ≫
            (θ C' D').hom =
          (θ C D).hom ≫ HomologicalComplex.mapBifunctorMap
            ((((pointSmallEtale t).ulift.{u + 1}.sheafFiber
              (A := ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).map f)
            ((((pointSmallEtale t).ulift.{u + 1}.sheafFiber
              (A := ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).map g)
            (curriedTensor _) (.up ℤ)) := by
  sorry

end AlgebraicGeometry.Scheme
