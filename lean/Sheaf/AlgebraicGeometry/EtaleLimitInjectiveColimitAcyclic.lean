/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.CategoryTheory.SiteInjectiveCechAcyclic
import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.CategoryTheory.ColimitSiteSections
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-! # Etale replacement: construction and vanishing

Source: Stacks Project, Tags 0EXZ, 09YP, 09YN and 09YQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- A compatible injective coefficient system has an acyclic pulled-back colimit.
Source: Stacks Project, Tags 09YP and 09YQ, Cech acyclicity argument using 09YN.
(blueprint: lem-weil-pbc-etale-limit-injective-colimit-acyclic).

Proof: The limit and its projection morphisms are qcqs with affine projections.
Restrict to the cofinal finite qcqs etale covers. Descend each finite affine cover,
its maps and its finitely many objects to a common stage using the affine etale site
colimit presentation. Every iterated fibre product in its Cech nerve is qcqs and has
an inverse presentation with affine transitions. Degree-zero section continuity,
including eventual equality, identifies sections of the colimit sheaf on each such
object with the filtered colimit of the stage sections. The canonical units in this
comparison commute with restrictions. Finite products commute with filtered group
colimits, so the entire Cech complex is the filtered colimit of the stage complexes.
The stage coefficient sheaves are injective, hence their positive Cech cohomology
vanishes. Exact filtered group colimits preserve this vanishing. The Cech criterion
on the cofinal finite qcqs covers gives positive object cohomology vanishing. Apply
it to the terminal etale object and degree n+1 to obtain global vanishing.
No higher-degree continuity is used. Empty schemes, the zero system, degree zero
and a singleton index satisfy the same argument.
-/
theorem etale_limit_injective_colimit_acyclic
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (hinj : ∀ i : I, Injective (F i)) (n : ℕ) :
    Subsingleton (Sheaf.H L.pt (n + 1)) := by sorry

end AlgebraicGeometry.Etale
