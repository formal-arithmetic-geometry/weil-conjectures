/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # Short exact presentations of the single-module union comparison

Source: Stacks Project, Tags 08BV, 08FE, 08HY and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The three canonical comparisons are obtained from a morphism of short exact
complexes, after identifying their localized vertices. No comparison is asserted
invertible. The coefficients need not be quasi-coherent or relatively flat, and
there is no compactness assumption on the two opens.

Source: Stacks Project, Tags 08BV (the injective restriction-difference sequence),
08FE (restriction of direct image), 08HY (the base-change map), and 0DJ9
(the relative Mayer--Vietoris induction diagram); Tags 013N--013O for cylinders.
(blueprint: new-pc-standard-single-union-ses-presentation).

Proof:
Work on W = U union V and on its base change W_A. Resolve N[0] and its ordinary
pullback in degree zero by K-injective complexes with injective terms. The opens
induced by U,V cover W, and their inverse images cover W_A. Apply
schemeKInjective_mayerVietoris_presentation to these covers. Sheaf gluing gives
exactness at the first two terms of each restriction-difference sequence;
flasqueness of injectives gives surjectivity at the overlap. Thus the rows are
short exact without compactness or quasi-coherent direct-image assumptions.
Apply derived direct image to the rows and derived pullback to the source row.
Use diagram resolutions to represent these derived functors and the comparison
on complexes. Transpose the ordinary pullback map under the derived adjunction.
Naturality of the restriction units makes the first square commute; subtraction
of the two restriction squares gives the second square. The degreewise identity
schemeMVUnderivedOpenCounit_square makes this a comparison of the cover diagrams.
Use the functorial mapping cylinder of the first differential to obtain a strict
morphism of short exact rows: for a chain map t:C -> D, the row
C -> D direct-sum Cone(id C) -> Cone(t) is degreewise split exact, and its
contractible summand disappears after localization. Homotopy-commuting squares
are made strict by their specified homotopies in this cylinder construction.
The cone comparison from the cover rows identifies the third term with the
derived direct image on the overlap. This produces P,P' and m as in the statement.
Transport the localized vertices by direct-image composition and exact open
restriction. Additivity gives the two biproduct comparisons. Tensor pullback
along an open inclusion is exact restriction, so these coefficient restrictions
are the literal tensorPullbackObj terms displayed here. Expand the canonical
base-change comparison as the mate of the pulled-back direct-image counit.
The composite-counit identity and the adjunction triangle identities identify
the union and overlap components with standardSingleBaseChangeMap, and the
middle component with the biproduct of the two member maps. These give the three
conjugacy equations. The cylinder step is before forming any boundary map;
no distinguishedness or connecting-square assertion is assumed in this lemma.
For an empty open the corresponding complexes are zero; identical or contained
opens give split restriction rows. The construction applies unchanged to zero
coefficients. The existential witnesses here do not define library data. -/
theorem standardSingle_union_ses_presentation
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings A.toRingedSpace)) ℤ))
      (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ a.left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ aU.left ⊞ aV.left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ aUV.left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ aU.right ⊞ aV.right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ aUV.right),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
      DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ aUV.hom := by sorry

end AlgebraicGeometry
