/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration

/-! # Finite scalar realization of the canonical locally closed extension

Source: blueprint scalar-six-ctf (1), comparison of locally closed extensions.
(blueprint: lem-sfb-finite-scalar-etale-extension-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- On a sheaf in degree zero, finite scalar realization commutes with the canonical
locally closed extension through the scheme-theoretic image.

Source: blueprint scalar-six-ctf (1), ordinary/internal compactification comparison and
coefficient-isomorphism transport.
(blueprint: lem-sfb-finite-scalar-etale-extension-iso).

Proof: Since X is Noetherian, factor a as its quasi-compact open immersion into its
scheme-theoretic image followed by a closed immersion. The closed immersion is proper,
so this is the compactification used by both specified extension constructions. The
étale/pro-étale comparison identifies exact open extension and, on this bounded-below
input, the derived closed direct image. On the étale site the closed pushforward is
exact, so their composite on L[0] is the single complex of flatModelEtaleExtension L.
The constant-ring module equivalence commutes with open extension by uniqueness of
left adjoints, and with derived closed pushforward by transport of injective resolutions
through its exact inverse. Compose those comparisons with the coefficient-isomorphism
shriek comparison for e.symm. The resulting target composite is precisely
sfbLocallyClosedDerivedExtension, and its input is the same realized L[0]. Associators
supply the indicated object isomorphism. No finite-projectivity hypothesis is required
for this comparison. Zero rings and empty strata are included. -/
theorem sfbFiniteScalarEtaleExtensionIso
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsNoetherian X.left]
    (S : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    Nonempty ((sfbFiniteScalarRealization A e eR X.left).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension (ULift.{u + 1} A) a ha).obj L)) ≅
      (sfbLocallyClosedDerivedExtension Λ a ha).obj
        ((sfbFiniteScalarRealization A e eR S).obj
          ((DerivedCategory.singleFunctor _ 0).obj L))) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
