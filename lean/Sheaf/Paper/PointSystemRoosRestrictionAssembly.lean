/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.PointSystemRoosTransportData

import Sheaf.Paper.PointRestrictionWholeRoosSquare

/-! The strict restriction square for projection-normalized point-system comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.pointReductionModuleDerived
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemRoos

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] roosF

/-- Actual restriction on both coordinates of the point-system Roos cone.

Source: blueprint integral-model proof (3), restriction steps 5--7;
lem-trf-point-restriction-whole-roos-square; Stacks Tag 0941.
(blueprint: lem-trf-point-system-roos-restriction-assembly).

Proof: obtain the strict whole-Roos restriction square. Its cone comparisons and the
specified products.kappaT and products.kappaF agree after each product projection in
both cone coordinates. For sections this follows from the product projection law and
the two diagonal equations. For inverse image evaluate at each site object and use
its product projection law; the coefficient-system identification keeps the same
section carriers. Product and biproduct extensionality prove equality of the actual
chain maps. The sigma_sections law identifies the ambient restriction transformation
termwise with the one in that square. Substitute these equalities and cancel the
inverse sections comparison to obtain restriction_cone. Finally chainTransport has
its specified restriction components. Its product map has the same components by
Pi.map_π. The section carrier equality of coefficientSequenceRestriction supplies the
witness x_n in restriction_products; apply the component HEq to that witness.
No equality of derived maps is inferred from levelwise evaluation. -/
theorem point_system_roos_restriction_assembly (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    (models : Models D l E) (products : Products D l E r)
    (comparisons : Comparisons D l E r)
    (hproducts : ProductLaws D l E r products)
    (hcomparisons : ComparisonLaws D l E r models products comparisons) :
  (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
        (products.kappaT M).inv ≫ comparisons.sigma.app (roosF.obj ((X D l E).obj M)) ≫
          ((T D l E).mapHomologicalComplex (.up ℤ)).map (products.kappaF M).hom ≫
          (products.kappaT (((G D l E r).mapHomologicalComplex (.up ℤ)).obj M)).hom =
        roosF.map ((PointSystemTransport.chainTransport D l E hl r hr).app M)) ∧
  -- restriction_products
  (∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ) (x : (roosP ((Z D l E).obj M)).X i),
        ∃ xₙ : (M.X i).val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))),
          HEq (((Pi.π (fun n : ℕ ↦ ((Z D l E).obj M).asFunctor.obj (op n)) n).f i) x) xₙ ∧
          HEq (((roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M) ≫
          Pi.π (fun n : ℕ ↦ ((Z' D l E r).obj M).asFunctor.obj (op n)) n).f i) x)
          ((M.X i).val.map
            (Prod.mkHom (𝟙 n)
              (pointRestrictionArrow (PointSystemTransport.pointPower D r).hom)).op
            xₙ)) := by sorry

end WeilConjectures.PointSystemRoos
