/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion

/-! # Properties of explicit subset insertion

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- Explicit subset insertion agrees with the singleton augmentation.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-insertion-augmentation).

Proof: Expand the augmentation as restriction into the degree-zero tuple column
followed by its total summand inclusion. In the finite subset insertion, all coordinates
except singleton subsets are zero, and their insertions vanish by additivity.
For a singleton, increasing enumeration is its unique one-tuple. Naturality of the
restriction equivalence identifies restriction after transporting a global section
with transporting its restriction to the corresponding principal open. The equality
hes identifies the coefficient degrees, and proof irrelevance equates the transports.
Summing these singleton insertions gives the degree-zero column inclusion, hence the
augmentation. For the empty cover the sum and the degree-zero column are both zero. -/
theorem principalSubsetInsertion_augmentation
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :
    let V := principalSubsetUnion A r f
    let D := principalSubsetOpen A r f
    ∀ (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      let R := SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
        (Scheme.Modules.overEquiv V).functor
      let J' := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
      let U : Fin r → V.toScheme.Opens :=
        fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
      let G := (forget₂
        (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)
      ∀ (n : ℤ) (s : (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V)),
          principalSubsetInsertion A r f J n (fun S ↦ if h : S.val.card = 1 then
            (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
              (homOfLE (hls S h)).op
              ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
                (op V) s) else 0) =
            (G.map ((alternatingCechAugmentation U).app J')).f n
              (by
                change (forget₂
                  (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
                  AddCommGrpCat).obj
                    ((RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace).obj
                      (R.obj (J.X n)))
                exact (principalOpenSectionTransport A V (J.X n)).hom s) := by sorry

end AlgebraicGeometry
