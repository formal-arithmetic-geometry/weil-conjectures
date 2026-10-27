/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.SheafTensor

/-! # Sheafified cohomology of the profinite action site

Source: Stacks Project, Tags 072W and 03FD; blueprint direct-images proof paragraph (3)
(blueprint: lem-sfb-profinite-invariants-sheafified-cohomology).

The comparison is specified on resolution cocycles, so neither an arbitrary isomorphism
nor exactness of evaluation on abelian sheaves is part of its specification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
open CochainComplex.HomComplex

namespace Profinite.CondensedAction.SheafifiedCohomology

open CoherentPresentation

variable (A : CategoryTheory.CondensedBar.Ring.{u})
variable (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]

/-- Forget an internal module to its recorded abelian sheaf.
Source: Stacks 03FD (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
abbrev underlyingModule : CategoryTheory.CondensedBar.Modules A ⥤
    Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} := Mod.forget A.X

/-- The original profinite parameters equipped with the trivial action.
Source: Stacks 072W (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def parameters : Profinite.{u} ⥤ Space J := AsSmall.up ⋙ trivialParameter J

variable {A J} {P : SetPresentation J} (D : ModulePresentation J P A.toMon)

/-- The normalized equivalence's recorded additive structure.
Source: Stacks 03FD (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
instance presentationAdditive : D.data.equivalence.functor.Additive := D.properties.additive

/-- Scalar forgetting after the normalized action-site equivalence.
Source: Stacks 03FD (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def presentedAbelian : CategoryTheory.CondensedBar.Equivariant A J ⥤
    Sheaf (coverage J).toGrothendieck
    AddCommGrpCat.{u + 1} :=
  D.data.equivalence.functor ⋙ SheafOfModules.toSheaf _

/-- Additivity of the composite with scalar forgetting, from the recorded presentation.
Source: Stacks 03FD (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
instance presentedAbelianAdditive : (presentedAbelian D).Additive :=
  inferInstanceAs (D.data.equivalence.functor ⋙ SheafOfModules.toSheaf _).Additive


/-- Small-site abelian sheaves have Ext in the common containing universe.
Source: Stacks 01FT (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
instance actionSiteHasExt : HasExt.{u + 1}
    (Sheaf (coverage J).toGrothendieck AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _


/-- The presheaf P^q_M(S) = H^q(tS,Phi(M)_ab), with its actual coefficient maps.
Source: Stacks 072W and object cohomology 01FT
(blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def objectPresheaf (q : ℕ) : CategoryTheory.CondensedBar.Equivariant A J ⥤
    Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  presentedAbelian D ⋙ Sheaf.cohomologyPresheafFunctor (coverage J).toGrothendieck q ⋙
    (Functor.whiskeringLeft _ _ _).obj (parameters J).op


/-- The invariant complex of the specified resolution, extended by zero to integer degrees.
Source: Stacks 072W (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def invariantComplex {M : CategoryTheory.CondensedBar.Equivariant A J} (Q : InjectiveResolution M) :
    CochainComplex (CategoryTheory.CondensedBar.Modules A) ℤ :=
  ((invariants A J).functor.mapHomologicalComplex (.up ℤ)).obj Q.cochainComplex


/-- The abelian presheaf complex of invariant sections, before sheafification.
Source: Stacks 072W (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def invariantPresheafComplex {M : CategoryTheory.CondensedBar.Equivariant A J}
    (Q : InjectiveResolution M) :
    CochainComplex (Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ :=
  ((underlyingModule A ⋙ sheafToPresheaf _ _).mapHomologicalComplex (.up ℤ)).obj
    (invariantComplex Q)

/-- The transported resolution as an abelian sheaf complex on the action site.
Source: Stacks 03FD (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def presentedComplex {M : CategoryTheory.CondensedBar.Equivariant A J} (Q : InjectiveResolution M) :
    CochainComplex (Sheaf (coverage J).toGrothendieck AddCommGrpCat.{u + 1}) ℤ :=
  ((presentedAbelian D).mapHomologicalComplex (.up ℤ)).obj Q.cochainComplex


/-- The transported augmentation retains the standard comparison with a single complex.
Source: Stacks 03FD (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def presentedAugmentation {M : CategoryTheory.CondensedBar.Equivariant A J}
    (Q : InjectiveResolution M) :
    (CochainComplex.singleFunctor _ 0).obj ((presentedAbelian D).obj M) ⟶
      presentedComplex D Q :=
  (HomologicalComplex.singleMapHomologicalComplex (presentedAbelian D) (.up ℤ) 0).inv.app M ≫
    ((presentedAbelian D).mapHomologicalComplex (.up ℤ)).map Q.ι'


/-- Restrict the transported resolution to trivial parameters, before taking cohomology.
Source: Stacks 072W (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def restrictedComplex {M : CategoryTheory.CondensedBar.Equivariant A J}
    (Q : InjectiveResolution M) :
    CochainComplex (Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ :=
  ((sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj
    (parameters J).op).mapHomologicalComplex (.up ℤ)).obj (presentedComplex D Q)


/-- The actual resolution computation arrow H^q(Gamma Q) to H^q(RGamma(M[0])).
Source: Stacks 072W, injective-resolution formula
(blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def computation {M : CategoryTheory.CondensedBar.Equivariant A J}
    (Q : InjectiveResolution M) (q : ℕ) :
    (invariantComplex Q).homology (q : ℤ) ⟶
      (DerivedCategory.homologyFunctor (CategoryTheory.CondensedBar.Modules A) (q : ℤ)).obj
        ((derived A J).obj
          ((DerivedCategory.singleFunctor
            (CategoryTheory.CondensedBar.Equivariant A J) 0).obj M)) :=
  (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).inv.app (invariantComplex Q) ≫
    (DerivedCategory.homologyFunctor _ (q : ℤ)).map
      ((invariants A J).functor.rightDerivedFunctorUnitQ Q.cochainComplex ≫
        (derived A J).map (inv (DerivedCategory.Q.map Q.ι')))


/-- The counit identifies the termwise sheafification of invariant presheaves with the
original abelian sheaf complex. Source: Stacks 072W
(blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def sheafifiedComplexMap {M : CategoryTheory.CondensedBar.Equivariant A J}
    (Q : InjectiveResolution M) :
    ((presheafToSheaf (coherentTopology Profinite.{u})
      AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).obj (invariantPresheafComplex Q) ⟶
    ((underlyingModule A).mapHomologicalComplex (.up ℤ)).obj (invariantComplex Q) :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (underlyingModule A) (sheafificationAdjunction _ _).counit) (.up ℤ)).app
      (invariantComplex Q)


/-- The canonical eta_Q: sheafify(H^q(Gamma Q on sections)) to U(R^q Gamma M).
It uses exact sheafification and exact scalar forgetting, followed by the actual total
right-derived computation unit. Source: Stacks 072W and 03FD
(blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def sheafifiedComputation {M : CategoryTheory.CondensedBar.Equivariant A J}
    (Q : InjectiveResolution M) (q : ℕ) :
    (presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}).obj
      ((invariantPresheafComplex Q).homology (q : ℤ)) ⟶
    (underlyingModule A).obj
      ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((derived A J).obj ((DerivedCategory.singleFunctor _ 0).obj M))) :=
  letI : (underlyingModule A).PreservesHomology :=
    { preservesKernels := fun _ ↦ inferInstance
      preservesCokernels := fun _ ↦ inferInstance }
  (((invariantPresheafComplex Q).sc (q : ℤ)).mapHomologyIso
      (presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})).inv ≫
    HomologicalComplex.homologyMap (sheafifiedComplexMap Q) (q : ℤ) ≫
    (((invariantComplex Q).sc (q : ℤ)).mapHomologyIso (underlyingModule A)).hom ≫
    (underlyingModule A).map (computation Q q)


/-- The free abelian sheaf representing sections at an action-space parameter.
Source: Stacks 01FT (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
abbrev freeParameterSheaf (S : Profinite.{u}) :=
  (presheafToSheaf (coverage J).toGrothendieck AddCommGrpCat.{u + 1}).obj
    (yoneda.obj ((parameters J).obj S) ⋙ AddCommGrpCat.free)

/-- The section of a sheaf morphism from the free abelian representable, evaluated on
its identity generator. Source: Stacks 01FT and Yoneda
(blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def generatorSection (S : Profinite.{u})
    {F : Sheaf (coverage J).toGrothendieck AddCommGrpCat.{u + 1}}
    (z : freeParameterSheaf (J := J) S ⟶ F) :
    F.obj.obj (op ((parameters J).obj S)) :=
  (z.hom.app _).hom ((toSheafify (coverage J).toGrothendieck
    (yoneda.obj ((parameters J).obj S) ⋙ AddCommGrpCat.free)).app _
      (FreeAbelianGroup.of (𝟙 ((parameters J).obj S))))

/-- The class of a pointwise cycle, with the canonical evaluation/homology comparison.
Source: Stacks 072W (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def cycleClass (K : CochainComplex (Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ)
    (q : ℕ) (S : Profinite.{u}) (y : (K.asFunctor.obj (op S)).cycles (q : ℤ)) :
    (K.homology (q : ℤ)).obj (op S) :=
  (((K.sc (q : ℤ)).mapHomologyIso
    ((evaluation _ _).obj (op S))).hom).hom
      (((K.asFunctor.obj (op S)).homologyπ (q : ℤ)).hom y)


/-- The actual map on invariant section complexes induced by a resolution chain map.
Source: Stacks 072W (blueprint: lem-sfb-profinite-invariants-sheafified-cohomology). -/
def invariantPresheafMap {M N : CategoryTheory.CondensedBar.Equivariant A J}
    {Q : InjectiveResolution M} {Q' : InjectiveResolution N}
    (g : Q.cochainComplex ⟶ Q'.cochainComplex) :
    invariantPresheafComplex Q ⟶ invariantPresheafComplex Q' :=
  ((underlyingModule A ⋙ sheafToPresheaf _ _).mapHomologicalComplex (.up ℤ)).map
    (((invariants A J).functor.mapHomologicalComplex (.up ℤ)).map g)

/-- Sheafified action-site cohomology computes higher internal invariants, naturally in
coefficients and in all continuous profinite parameter maps, independently of resolutions.
The first equation normalizes the section-complex identification by the fixed inclusion.
The second normalizes beta on every cocycle and every abelian injective comparison.
The third is naturality for every resolution lift (including lifts of the identity).
The fourth says that alpha is exactly eta_Q after the inverse of sheafified beta_Q.
The final equation spells out the coefficient naturality of alpha.

Source: Stacks Project, Tags 072W and 03FD, with the normalized action presentation;
blueprint direct-images proof paragraph (3)
(blueprint: lem-sfb-profinite-invariants-sheafified-cohomology).
Proof:
1. Transport Q along the exact additive equivalence Phi. Equivalences preserve injectives
   and resolutions (lem-weil-pbc-equivalence-injective-resolutions). The normalized section
   formulas identify its restriction to tS with Gamma(Q)(S), including all differentials.
2. Apply lem-sfb-module-resolution-derived-presheaf-comparison to Phi(Q): its underlying
   abelian terms are inclusion-acyclic. Any chain comparison to an abelian injective
   resolution is a presheaf quasi-isomorphism, unique up to homotopy. The free abelian
   representable/Yoneda identification sends its cocycles to precisely the Ext classes
   specified below. Objectwise homology gives beta, compatible with every restriction.
3. Lift an equivariant map between injective resolutions. The preceding comparison is
   natural for that lift and independent of it up to homotopy. Taking the identity map
   gives independence of resolution via the canonical comparison isomorphisms.
4. Ordinary total derived invariants are computed on Q by boundedBelowComputation.
   Scalar forgetting is exact by the internal/sectionwise module equivalence and
   lem-weil-pbc-module-sheaves-colimits-forgetful. Exact sheafification commutes with
   homology (lem-weil-pbc-site-module-presheaf-sheafification-exact). Its counit recovers
   the original sheaf complex. These are exactly the factors of sheafifiedComputation.
5. Define alpha = eta_Q after inverse sheafified beta_Q. The two lift-naturalities and
   lem-weil-pbc-derived-functor-map-via-lift prove its displayed coefficient equation.
   Homotopy uniqueness gives independence of every choice. No exactness of evaluation
   on sheaves, discreteness, or cohomological-dimension bound is used. -/
theorem profiniteInvariants_sheafifiedCohomology (q : ℕ) :
    ∃ (e : ∀ (M : CategoryTheory.CondensedBar.Equivariant A J)
          (Q : InjectiveResolution M), invariantPresheafComplex Q ≅ restrictedComplex D Q)
      (beta : ∀ (M : CategoryTheory.CondensedBar.Equivariant A J)
          (Q : InjectiveResolution M),
        (invariantPresheafComplex Q).homology (q : ℤ) ≅ (objectPresheaf D q).obj M)
      (alpha : objectPresheaf D q ⋙
          presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} ≅
        ((DerivedCategory.singleFunctor (CategoryTheory.CondensedBar.Equivariant A J) 0 ⋙
          derived A J) ⋙ DerivedCategory.homologyFunctor
            (CategoryTheory.CondensedBar.Modules A) (q : ℤ)) ⋙ underlyingModule A),
      (∀ (M : CategoryTheory.CondensedBar.Equivariant A J) (Q : InjectiveResolution M)
          (n : ℤ) (S : Profinite.{u})
          (x : ((invariantPresheafComplex Q).X n).obj (op S)),
        ((invariants A J).inclusion.app (Q.cochainComplex.X n)).hom.hom.app (op S) x =
          D.data.moduleSection (Q.cochainComplex.X n) ((parameters J).obj S)
            (((e M Q).hom.f n).app (op S) x)) ∧
      (∀ (M : CategoryTheory.CondensedBar.Equivariant A J) (Q : InjectiveResolution M)
          (I : InjectiveResolution ((presentedAbelian D).obj M))
          (b : presentedComplex D Q ⟶ I.cochainComplex)
          (_hb : presentedAugmentation D Q ≫ b = I.ι') (S : Profinite.{u})
          (z : Cocycle ((CochainComplex.singleFunctor _ 0).obj
            (freeParameterSheaf (J := J) S)) (presentedComplex D Q) (q : ℤ))
          (y : ((restrictedComplex D Q).asFunctor.obj (op S)).cycles (q : ℤ)),
        (((restrictedComplex D Q).asFunctor.obj (op S)).iCycles (q : ℤ)).hom y =
          generatorSection S (Cochain.fromSingleEquiv (zero_add (q : ℤ)) z.val) →
        ((beta M Q).hom.app (op S)).hom
          (((HomologicalComplex.homologyMap (e M Q).inv (q : ℤ)).app (op S)).hom
            (cycleClass (restrictedComplex D Q) q S y)) =
          I.extEquivCohomologyClass.symm (CohomologyClass.mk (z.postcomp b))) ∧
      (∀ (M N : CategoryTheory.CondensedBar.Equivariant A J) (f : M ⟶ N)
          (Q : InjectiveResolution M) (Q' : InjectiveResolution N)
          (g : Q.cochainComplex ⟶ Q'.cochainComplex),
        Q.ι' ≫ g = (CochainComplex.singleFunctor _ 0).map f ≫ Q'.ι' →
        HomologicalComplex.homologyMap (invariantPresheafMap g) (q : ℤ) ≫
          (beta N Q').hom = (beta M Q).hom ≫ (objectPresheaf D q).map f) ∧
      (∀ (M : CategoryTheory.CondensedBar.Equivariant A J) (Q : InjectiveResolution M),
        (presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}).map
          (beta M Q).hom ≫ alpha.hom.app M = sheafifiedComputation Q q) ∧
      (∀ (M N : CategoryTheory.CondensedBar.Equivariant A J) (f : M ⟶ N),
        alpha.hom.app M ≫ (underlyingModule A).map
          ((DerivedCategory.homologyFunctor _ (q : ℤ)).map
            ((derived A J).map ((DerivedCategory.singleFunctor _ 0).map f))) =
        (presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}).map
          ((objectPresheaf D q).map f) ≫ alpha.hom.app N) := by
  sorry

end Profinite.CondensedAction.SheafifiedCohomology
