/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenRestrictionData
public import Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisExtRestrictionMap
/-! # Bijectivity of Ext restriction from a represented open

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}

/-- Restriction from the free sheaf on an open, before and after base change, is bijective.
Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
(blueprint: lem-pc-open-restriction-ext-bijective)

Proof: Exact extension by zero is left adjoint to exact restriction. The free
abelian sheaf represented by W is extension by zero of the free sheaf represented
by the top open of W: both represent sections on W, by the free/forgetful and
sheafification adjunctions. The derived adjunction identifies Ext from this
ambient free sheaf to F with Ext from its restriction to the restriction of F.
The restriction map is this adjunction bijection, not an unspecified isomorphism:
the unit on the represented free sheaf is the identity under its canonical
identification. Precomposition and postcomposition by any object isomorphisms
e and d preserve bijectivity. This proves the first assertion in every degree.
For the second assertion the base-changed inclusion k is again an open immersion,
and inverse image carries the free sheaf represented by W to the free sheaf
represented by its preimage open. That preimage is precisely the image of k,
by the cartesian scheme square. Apply the same exact extension/restriction
adjunction on X_S, then the arbitrary object isomorphisms e' and d'. Empty opens
and zero coefficients give zero Ext groups, so bijectivity still holds; the top
open gives the restriction equivalence. No flatness or quasi-coherence is used.
-/
theorem H.openRestrictionExt_bijective
    (f : X ⟶ Spec (.of R)) (M : X.Modules) (W : X.Opens)
    (e : (invImage W.ι).obj (H.openFreeSheaf W) ≅
      H.openFreeSheaf (⊤ : W.toScheme.Opens))
    (d : (invImage W.ι).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ≅
      (SheafOfModules.toSheaf W.toScheme.ringCatSheaf).obj ((pullback W.ι).obj M))
    (e' : (invImage (H.openBaseChangeInclusion (S := S) f W)).obj
      ((invImage (baseChangeFst (S := S) f)).obj (H.openFreeSheaf W)) ≅
      (invImage (baseChangeFst (S := S) (W.ι ≫ f))).obj
        (H.openFreeSheaf (⊤ : W.toScheme.Opens)))
    (d' : (invImage (H.openBaseChangeInclusion (S := S) f W)).obj
      ((SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
        (baseChangedModule (S := S) f M)) ≅
      (SheafOfModules.toSheaf (baseChangedScheme (S := S) (W.ι ≫ f)).ringCatSheaf).obj
        (baseChangedModule (S := S) (W.ι ≫ f) ((pullback W.ι).obj M))) :
    (∀ n, Function.Bijective (Ext.restrictAddHom (invImage W.ι) e d n)) ∧
      (∀ n, Function.Bijective
        (Ext.restrictAddHom
          (invImage (H.openBaseChangeInclusion (S := S) f W)) e' d' n)) := by sorry

end AlgebraicGeometry.Scheme.Modules
