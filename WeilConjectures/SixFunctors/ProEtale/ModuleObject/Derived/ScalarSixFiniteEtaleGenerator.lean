/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension

/-! # Étale finite-projective generators in scalar coordinates

Source: blueprint scalar-six-ctf (1), identification of generators.
(blueprint: lem-sfb-finite-scalar-etale-generator).
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

/-- A single locally closed extension of an étale lisse finite-projective module is a
canonical locally perfect scalar generator after finite scalar realization.

Source: blueprint scalar-six-ctf (1), finite projective local models and locally closed
extension comparison; Stacks Tags 00NX and 099Y.
(blueprint: lem-sfb-finite-scalar-etale-generator).

Proof: Trivialize the lisse module on an étale cover, with finite projective constant
modules. Pull that cover to the pro-étale site. Under the constant-ring encoding a finite
projective module is a retract of a finite sum of the regular scalar module; lift its
splitting by full faithfulness of the encoding. Restriction along e identifies regular
modules and preserves those splittings. Place the resulting scalar modules in degree
zero, with common bounds [0,0]. Pullback compatibility of the encoding and scalar
restriction identifies their constant realizations with the pullbacks of the transported
module. This proves it is locally perfect. Factor a through its scheme-theoretic image.
The open factor is quasi-compact and the closed factor is proper because X is Noetherian.
The ordinary/internal comparison for this compactification, and the coefficient-isomorphism
shriek comparison, identify the transported étale extension in degree zero with the
canonical derived composite defining sfbLocallyClosedDerivedExtension. The exact closed
pushforward and open extension commute with degree-zero embeddings. This gives the
required generator witness. Empty strata, rank zero and the zero ring need no exclusions. -/
theorem sfbFiniteScalarEtaleGenerator
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsNoetherian X.left]
    (S : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (hL : FlatModelEtaleLisseProjective (ULift.{u + 1} A) L) :
    sfbPerfectScalarGenerator Λ X
      ((sfbFiniteScalarRealization A e eR X.left).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension (ULift.{u + 1} A) a ha).obj L))) := by
  let : IsNoetherian S :=
    ((coefficientHeart_locallyClosedExtension Λ.X X.left).1 S a ha).1
  refine ⟨S, a, ha, _, sfbFiniteScalarEtaleLisseModel A e eR S L hL, ?_⟩
  exact sfbFiniteScalarEtaleExtensionIso A e eR X S a ha L

end AlgebraicGeometry.ProEtale.CondensedRing
