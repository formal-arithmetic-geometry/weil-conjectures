/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Sheaf.Paper.EtaleFlatKFlatResolution
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Geometric étale stalks and unbounded derived tensor products

The canonical stage-2 statement was revalidated by group NL against the current
`newtargets-dag` interface; all mathematical clauses below are unchanged.

Source: Stacks Project, `sites-cohomology.tex`, Tag 0DEN, clause (1), and Tags 06YS,
06YT, 06YU and 07A4 (blueprint: lem-sfb-etale-derived-tensor-stalk).

## Main statements

* `AlgebraicGeometry.Etale.exists_derivedTensor_stalk_iso`: the natural isomorphism,
  normalized by the ordinary total-complex stalk comparison.
* The three auxiliary instances expose existing additive and coproduct structures.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The existing additive structure on the geometric module-stalk functor, exposed for
termwise passage to complexes and derived categories. This is precisely the structure
`Point.sheafFiber_additive`, obtained from the skyscraper adjunction.
Source: Stacks Project, Tag 04EQ
(blueprint: lem-sfb-etale-derived-tensor-stalk). -/
noncomputable instance moduleSheafFiber_additive
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).Additive :=
  (pointSmallEtale t).sheafFiber_additive

/-- Small colimits in the module-valued étale sheaf category, obtained by the existing
universe-shrinking construction. These are the coproducts used by total tensor complexes.
Source: Stacks Project, Tag 0DEN, direct sums in its proof
(blueprint: lem-sfb-etale-derived-tensor-stalk). -/
noncomputable instance moduleSheaf_hasSmallColimits
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    IsGrothendieckAbelian.hasColimits _
  exact hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _

/-- Countable coproducts of module-valued étale sheaves, extracted from their small
colimits. Source: Stacks Project, Tag 0DEN, the total tensor coproducts in its proof
(blueprint: lem-sfb-etale-derived-tensor-stalk). -/
noncomputable instance moduleSheaf_hasCountableCoproducts
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasCountableCoproducts (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) where
  out J := (moduleSheaf_hasSmallColimits A T).has_colimits_of_shape (Discrete J)

/-- Geometric stalks commute canonically with the unbounded K-flat derived tensor, naturally
in both arguments. The equation specifies the comparison by the ordinary total-complex
stalk comparison and the localization counits; thus the existential isomorphism is the
canonical comparison, rather than an unspecified isomorphism between objects.
Source: Stacks Project, Tag 0DEN, clause (1), Tags 06YS, 06YT, 06YU and 07A4
(blueprint: lem-sfb-etale-derived-tensor-stalk).

Proof.
1. Exact geometric stalks preserve acyclic complexes and quasi-isomorphisms. The stalk
of a constant module is that module: compute the constant presheaf colimit over pointed
étale neighbourhoods and use invariance of stalks under sheafification. Constant sheaves
of acyclic module complexes are acyclic by exact module-presheaf sheafification.
These are prop-weil-pbc-geometric-stalks-exact, def-kun-constant-sheaf,
lem-weil-pbc-sheafification-geometric-stalk and
lem-weil-pbc-site-r-module-presheaf-sheafification-exact.
2. Stalks commute with coproducts and ordinary tensor. Apply these comparisons to every
summand with p + q = n in the direct-sum total complex. Naturality identifies both
terms of its differential, including the sign (-1)^p, giving the canonical natural
isomorphism of total tensor complexes used in the displayed localization square.
Use lem-kun-stalks-commute-colimits, lem-pod-etale-stalk-tensor-scalar and
def-pc-tensor-complex-sheaves.
3. For a K-flat sheaf complex P and any acyclic ordinary module complex E, its constant
sheaf complex is acyclic. Hence P tensor the constant complex is acyclic; its stalk is
SP tensor E and is acyclic. Thus SP is K-flat, without any boundedness assumption
(def-pc-kflat-complex and def-pc-module-kflat-complex).
4. Choose K-flat resolutions P and Q of representatives of the two derived objects.
Use lem-kun-flat-resolution-existence; their stalks remain K-flat resolutions by
steps 1 and 3. Localizing the comparison
of step 2 identifies the two derived tensors, both computed by these resolutions
(def-kun-derived-tensor and def-weil-abstract-derived-category).
5. Chain-map naturality survives localization. Changing either K-flat representative
along a quasi-isomorphism preserves the tensors and their stalks; independence of the
K-flat construction (lem-kun-derived-tensor-well-defined) gives the natural isomorphism
of bifunctors. Its defining square is
the equation below, first on K-flat representatives and then on all representatives
by the localization counits. No finiteness, Tor-amplitude or boundedness is used. -/
theorem exists_derivedTensor_stalk_iso
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃ e : ∀ K L : DerivedCategoryModule A T,
      (pointSmallEtale t).sheafFiber.mapDerivedCategory.obj
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj L) ≅
        (pointSmallEtale t).sheafFiber.mapDerivedCategory.obj K ⊗
          (pointSmallEtale t).sheafFiber.mapDerivedCategory.obj L,
      (∀ (K K' L L' : DerivedCategoryModule A T) (f : K ⟶ K') (g : L ⟶ L'),
        (pointSmallEtale t).sheafFiber.mapDerivedCategory.map
            (((derivedTensor (ModuleCat.{u + 1} A) T).map f).app L ≫
              ((derivedTensor (ModuleCat.{u + 1} A) T).obj K').map g) ≫
            (e K' L').hom =
          (e K L).hom ≫
            ((pointSmallEtale t).sheafFiber.mapDerivedCategory.map f ⊗ₘ
              (pointSmallEtale t).sheafFiber.mapDerivedCategory.map g)) ∧
      ∀ P Q : HomotopyCategory
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ),
        (e (_root_.DerivedCategory.Qh.obj P) (_root_.DerivedCategory.Qh.obj Q)).hom ≫
          ((pointSmallEtale t).sheafFiber.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ
            (pointSmallEtale t).sheafFiber.mapDerivedCategoryFactorsh.hom.app Q) ≫
          Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh (C := ModuleCat.{u + 1} A))
            (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A) |>.mapHomotopyCategory
              (ComplexShape.up ℤ)).obj P)
            (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A) |>.mapHomotopyCategory
              (ComplexShape.up ℤ)).obj Q) =
        (pointSmallEtale t).sheafFiber.mapDerivedCategory.map
          (Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh
            (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) P Q) ≫
          (pointSmallEtale t).sheafFiber.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
          (_root_.DerivedCategory.Qh (C := ModuleCat.{u + 1} A)).map
            (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
              ((pointSmallEtale t).sheafFiber)).app P).app Q) := by
  sorry

end AlgebraicGeometry.Etale
