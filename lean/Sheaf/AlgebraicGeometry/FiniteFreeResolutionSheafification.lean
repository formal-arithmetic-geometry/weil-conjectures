/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! # Sheafifying a prescribed finite free resolution

Source: Stacks Project, Algebra, Tag 00LP; Schemes, Tag 01HV;
Modules, Tag 01AG (blueprint: lem-sc-finite-free-resolution-sheafification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Sheafification of an already specified exact finite free resolution, followed by transport
along an affine chart and the equivalence between open subschemes and the over-site.
No coherence, Noetherian hypothesis, or choice of an affine neighbourhood is required.
Source: Stacks Project, Algebra, Tag 00LP (lemma-resolution-by-finite-free), Schemes,
Tag 01HV (lemma-spec-sheaves), and Modules, Tag 01AG (lemma-abelian)
(blueprint: lem-sc-finite-free-resolution-sheafification).

Proof:
1. Put `A^(n j)` in cochain degree `-j`, zero in every positive degree, and use `d j`
   from degree `-(j+1)` to `-j`. The image-kernel identities imply that consecutive
   differentials compose to zero. The augmentation is `ε` in degree zero and zero
   otherwise; its compatibility follows from `range (d 0) = ker ε`.
2. Apply tilde termwise. Its stalk at a prime is the localization of the given module
   (Tag 01HV). Localization preserves the specified augmented exact sequence, and
   stalks detect exactness (Tag 01AG). Thus this augmentation induces an isomorphism
   on degree-zero homology and both sides have zero homology in every other degree.
3. Pull the sheaf complex back along the chart isomorphism `e`, then apply
   `(Scheme.Modules.overEquiv U).inverse` termwise. These equivalences preserve
   exactness, zero objects and finite direct sums of the unit, so preserve the
   augmentation quasi-isomorphism and the bound zero. The tilde of `A^(n j)` is
   free of rank `n j`: identify finite functions with finitely supported functions
   and use `tildeFinsupp`. Transport the standard basis along `Equiv.ulift` to the
   index type `ULift (Fin (n j))`. The positive-degree zero terms are free of rank
   zero. Commutation with the degree-zero single functor gives the stated target.

The statement concerns only the conversion of explicit algebraic resolution data into
an augmented sheaf complex. For the zero module, the zero ring, or an empty chart the
same construction works; rank zero is allowed in every degree. -/
theorem finite_free_resolution_sheafification
    (X : Scheme.{u}) (U : X.Opens)
    (A : Type u) [CommRing A] (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (M : Type u) [AddCommGroup M] [Module A M]
    (n : ℕ → ℕ) (ε : (Fin (n 0) → A) →ₗ[A] M)
    (d : ∀ j : ℕ, (Fin (n (j + 1)) → A) →ₗ[A] (Fin (n j) → A))
    (hε : Function.Surjective ε) (h₀ : LinearMap.ker ε = LinearMap.range (d 0))
    (hd : ∀ j : ℕ, LinearMap.ker (d j) = LinearMap.range (d (j + 1))) :
    ∃ E : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (E.X i)) ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
      ∃ q : E ⟶ (CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) 0).obj
          ((Scheme.Modules.overEquiv U).inverse.obj
            ((Scheme.Modules.restrictFunctor e.hom).obj (tilde (ModuleCat.of A M)))),
        QuasiIso q := by sorry

end AlgebraicGeometry
