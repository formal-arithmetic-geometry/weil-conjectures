/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OrderedCechDegreewiseProjection
import Sheaf.AlgebraicGeometry.SignedCechExtension
import Sheaf.AlgebraicGeometry.OrderedCechModuleCoordinates

/-! # Differential compatibility of degreewise signed projection

Source: Stacks Project, Tags 01FK and 01FM.
(blueprint: lem-pc-ordered-cech-degreewise-projection-differential)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The degreewise signed formula commutes with the Čech differential.
Source: Stacks 01FK, signed extension is a cochain map; 01FM, the map cπ.
(blueprint: lem-pc-ordered-cech-degreewise-projection-differential).

Proof: Forget to abelian presheaves and evaluate on an open B and a full tuple y.
Apply hd to identify the differential of D with the usual alternating face sum.
Explicitly its y-coordinate in degree p+1 is the sum over j : Fin (p+2) of
(-1)^j times the restriction of the degree-p coordinate at y composed with
j.succAbove. On B take the family i ↦ W₀ ⟨i⟩ ⊓ B and coefficient presheaf
M.presheaf. Its tuple intersection is canonically isomorphic to the chosen
product (product W₀(y l)) times B: both are the infimum of the same opens.
Use these canonical restriction isomorphisms to form the sectionwise cochains;
the face arrows and index-permutation arrows agree under them by uniqueness.
For an injective y there is exactly one permutation making its entries increasing;
it is Tuple.sort applied to the underlying Fin r tuple. Thus the filtered sum in
IsOrderedCechNaturalProjection is the signed extension of the ordered restriction.
For a noninjective y the filter is empty, so the value is zero. The product-to-
intersection maps identify the chosen full products with the intersections; every
restriction composite agrees by uniqueness of arrows of opens. Apply
signedCechExtension_differential to the resulting sectionwise cochains. Its ordered
coordinates agree with the ordered coordinates of the differential of the original
cochain, because each face of an increasing tuple is increasing and the signed
extension is the identity there (signedCechExtension_increasing). Therefore d(cπs)
= cπ(ds). Use hd again and the injectivity of e followed by all product coordinates
to conclude equality of module-sheaf morphisms. When r = 0 or the degree exceeds r,
there are no increasing tuples and the same equality has both sides zero. -/
theorem orderedCech_degreewise_projection_comm {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (Q : ∀ p : ℕ, D.X p ⟶ D.X p)
    (hQ : IsOrderedCechNaturalProjection M W₀ D e Q) (p : ℕ) :
    Q p ≫ D.d p (p + 1) = D.d p (p + 1) ≫ Q (p + 1) := by sorry

end AlgebraicGeometry.Scheme.Modules
