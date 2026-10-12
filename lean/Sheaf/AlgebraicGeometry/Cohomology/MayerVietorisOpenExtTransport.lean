/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex
import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroExact
/-! # Ext transport from an open subscheme to its ambient scheme

Source: Stacks Project, Tags 00A7, 01AK, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
/-- Derived open-extension adjunction transports the two Ext presentations.
Source: Stacks Project, Tags 00A7 (open-extension adjunction), 01AK (exactness),
04J0 (localization of morphisms of ringed sites), and Section 01F7.
(blueprint: lem-pc-open-free-ext-transport)

Proof: Write j for the open immersion W.ι and p for the base-change projection.
Extension by zero j_! on abelian sheaves is exact and left adjoint to exact
restriction j^*. The free abelian sheaf on W is j_! of the constant integer
sheaf on W; the free sheaf on the top open of W is that constant integer sheaf.
The resulting derived adjunction, in the reverse direction, gives t. The
restriction of the abelian sheaf of M identifies canonically with the abelian
sheaf of the module pullback j^*M. Naturality of this adjunction in coefficients
identifies postcomposition by the restricted scalar with postcomposition by the
ambient scalar, proving the first equation.

The square obtained by base changing j along p is cartesian, and its upper
left scheme is the base change of W over Spec R. Base change of extension by
zero is extension by zero of inverse image: both sides are the free abelian
sheaf represented by the preimage open. The cartesian open-subscheme
isomorphism and composition of module pullbacks identify the restricted
coefficient sheaf with the underlying sheaf of the displayed module on the
base change of W. The same derived open-extension adjunction gives t'. Its
coefficient naturality identifies S-scalars and proves the second equation.

The unit defining the coefficient morphism on W is the restriction of the
ambient unit, under the cartesian coefficient identification. Naturality of
derived adjunction with respect to exact inverse image and this coefficient
morphism now gives the third equation. This can be checked on resolutions:
apply the restriction/extension adjunction to each term and the canonical
comparison of the restricted inverse-image resolutions; the squares commute
by the adjunction unit identities, and passing to cohomology preserves them.
No flatness is needed. For an empty open, both Ext groups are zero, and all
three equations hold; zero coefficients behave in the same way.
-/
theorem H.openFreeExtTransport (f : X ⟶ Spec (.of R)) (M : X.Modules) (W : X.Opens) :
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    let G := invImage (baseChangeFst (S := S) f)
    let N := (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
      (baseChangedModule (S := S) f M)
    let φ := coeff (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M)
    let ρ := (scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let τ := (scalarRep (baseChangedModule (S := S) f M)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    let MW := (pullback W.ι).obj M
    let FW := (SheafOfModules.toSheaf W.toScheme.ringCatSheaf).obj MW
    let GW := invImage (baseChangeFst (S := S) (W.ι ≫ f))
    let NW := (SheafOfModules.toSheaf
      (baseChangedScheme (S := S) (W.ι ≫ f)).ringCatSheaf).obj
      (baseChangedModule (S := S) (W.ι ≫ f) MW)
    let φW := coeff (baseChangeFst (S := S) (W.ι ≫ f))
      (baseChangeUnit (S := S) (W.ι ≫ f) MW)
    let ρW := (scalarRep MW).comp
      (((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom)
    let τW := (scalarRep (baseChangedModule (S := S) (W.ι ≫ f) MW)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) (W.ι ≫ f)).appTop).hom)
    ∃ (t : ∀ n, Ext (H.openFreeSheaf (⊤ : W.toScheme.Opens)) FW n ≃+
        Ext (H.openFreeSheaf W) F n)
      (t' : ∀ n, Ext (GW.obj (H.openFreeSheaf (⊤ : W.toScheme.Opens))) NW n ≃+
        Ext (G.obj (H.openFreeSheaf W)) N n),
      (∀ n a x, t n (x.comp (Ext.mk₀ (ρW a)) (add_zero n)) =
        (t n x).comp (Ext.mk₀ (ρ a)) (add_zero n)) ∧
      (∀ n a x, t' n (x.comp (Ext.mk₀ (τW a)) (add_zero n)) =
        (t' n x).comp (Ext.mk₀ (τ a)) (add_zero n)) ∧
      (∀ n x, t' n ((x.mapExactFunctor GW).comp (Ext.mk₀ φW) (add_zero n)) =
        ((t n x).mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) := by sorry

end AlgebraicGeometry.Scheme.Modules
