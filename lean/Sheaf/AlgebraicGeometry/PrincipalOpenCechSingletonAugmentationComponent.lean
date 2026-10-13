/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion

/-! # The singleton component of subset insertion

Source: Stacks Project, Tags 08C1 and 01FM.
(blueprint: lem-sc-principal-open-cech-singleton-augmentation-component).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

open Classical in
/-- A singleton restriction inserts exactly its degree-zero tuple coordinate.
Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-singleton-augmentation-component).

Proof: Write S={i} using card S=1. Its increasing enumeration is the one-tuple
with value i. Its principal open is D(f_i), and its intersection in V is the
inverse image of D(f_i). Expand principalSubsetSectionTransport and
principalOpenSectionTransport. Naturality of the inverse overFunctorEquiv and
of restrictAppIso with respect to this open inclusion identifies the transported
restriction with the i-th coordinate of alternatingCechZero. The degree equality
identifies J^n with the coefficient in insertOne; proof irrelevance identifies
all equality transports. Since card S-1=0, the extendXIso and total inclusion
in insertOne are precisely those displayed on the right. -/
theorem principalSubsetInsertOne_singleton_augmentation
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ)
    (S : {S : Finset (Fin r) // S.Nonempty}) (h : S.val.card = 1)
    (hl : principalSubsetOpen A r f S.val ≤ principalSubsetUnion A r f)
    (he : n = n + 1 - (S.val.card : ℤ))
    (s : (modulesSpecToSheaf.obj (J.X n)).obj.obj (op (principalSubsetUnion A r f))) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let J' := principalSubsetRestriction A r f J
    let L := alternatingCechComplex U ((alternatingCechModulePresheaf).obj (J'.X n))
    let K := (alternatingCechDoubleFunctor U).obj J'
    let H := forget₂
      (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    let e : (K.X 0).X n ≅ L.X 0 := L.extendXIso ComplexShape.embeddingUpNat rfl
    let z := (H.map (alternatingCechZero U (J'.X n) ≫ e.hom))
      ((principalOpenSectionTransport A V (J.X n)).hom s)
    principalSubsetInsertOne A r f J n S
      ((modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
        (homOfLE hl).op
        ((modulesSpecToSheaf.map (eqToHom (congrArg J.X he))).hom.app (op V) s)) =
      (H.map e.inv ≫ H.map (K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n)))
        (Pi.single (S.val.orderEmbOfFin h) (z (S.val.orderEmbOfFin h))) := by sorry

end AlgebraicGeometry
