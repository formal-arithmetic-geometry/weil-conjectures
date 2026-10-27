/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.Paper.CoefficientHeartFiltration
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.Paper.CoefficientHeartOrderedRefinement
import Sheaf.Paper.CoefficientHeartLisseRestriction
import Sheaf.Paper.CondensedSurjectiveClosedEquivalence
import Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.CoefficientHeartLocallyClosedExtension
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-! # Ordered finite-field models for norm-continuous coefficients

Source: blueprint main-20261015, direct-image stability proof paragraph (3),
the extracted ordered finite-model and open-support filtration obligation.
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration).

The algebraic closure is the chosen `PadicAlgCl`. Its continuous-map coefficient ring
is distinct from the finite-subextension-valued condensed algebraic closure. Refinement
means containment of images, and compatibility is imposed on the actual fibre product.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormAlgclOrderedModels

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Use the canonical norm topology on each finite intermediate field.
Source: direct-image stability proof (3), the restricted norm on E
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
instance finiteField_isTopologicalRing (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsTopologicalRing E :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- Use the canonical extended norm topology on the chosen algebraic closure.
Source: direct-image stability proof (3), the extended norm on Omega
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
instance algcl_isTopologicalRing : IsTopologicalRing (PadicAlgCl ℓ) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- The canonical inclusion of the finite-field continuous coefficient into the full
norm-continuous coefficient, by postcomposition with the field inclusion.
Source: direct-image stability proof (3), A_E to B
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
def scalarInclusion (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Profinite.continuousMapRingObj.{u} E ⟶
      Profinite.continuousMapRingObj (PadicAlgCl ℓ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (T := E) (T' := PadicAlgCl ℓ)
        E.val.subtype continuous_subtype_val)

/-- Multiplicativity inherited from the continuous ring map defining the inclusion.
Source: direct-image stability proof (3), A_E to B
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
instance scalarInclusion_isMonHom (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsMonHom (scalarInclusion.{u} ℓ E) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMap (T := E) (T' := PadicAlgCl ℓ)
      E.val.subtype continuous_subtype_val)

/-- Ordinary relative tensor with B, using the canonical scalar inclusion on the scheme.
Source: direct-image stability proof (3), B_T tensor over A_E,T
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
def scalarExtension (E : PadicAlgCl.FiniteIntermediateField ℓ) (T : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) T) ⥤
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) T) :=
  Mod.extendScalars ((upperStarFromPoint T).map (scalarInclusion ℓ E))

/-- The Noetherian topology supplied by the finite-type structure map to the field.
This is only instance data for the existing canonical closure-extension construction.
Source: direct-image stability proof (3), finite-type setting
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
abbrev noetherianSpace {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    TopologicalSpace.NoetherianSpace X.left :=
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := ⟨⟩
  inferInstance

/-- Existing open-then-closed extension through the scheme-theoretic closure, with the
Noetherian instance derived from the finite-type setting rather than assumed.
Source: direct-image stability proof (3), F_a = (a_a)_! L_a
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
def extension {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S : Scheme.{u}} (a : S ⟶ X.left)
    (ha : IsImmersion a) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left) :=
  letI : TopologicalSpace.NoetherianSpace X.left := noetherianSpace X
  coefficientHeartLocallyClosedExtension Λ a ha


/-- The restriction comparison is normalized by the actual closed counit and open unit.
This equation uniquely specifies the usual map a^* a_! L to L, without choosing an
arbitrary isomorphism of the two objects.
Source: direct-image stability proof (3), canonical extension restriction
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
def RestrictionNormalized {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S : Scheme.{u}} (a : S ⟶ X.left)
    (ha : IsImmersion a)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (ρ : (CondensedRing.upperStar Λ a).obj ((extension X Λ a ha).obj L) ≅ L) : Prop :=
  letI : TopologicalSpace.NoetherianSpace X.left := noetherianSpace X
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let F := (extension X Λ a ha).obj L
  ρ.hom ≫ (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ a.toImage).unit.app L =
    eqToHom (congrArg (fun f : S ⟶ X.left ↦ (CondensedRing.upperStar Λ f).obj F)
      a.toImage_imageι.symm) ≫
    (CondensedRing.upperStarComp Λ a.toImage a.imageι).hom.app F ≫
    (CondensedRing.upperStar Λ a.toImage).map
      ((CondensedRing.upperStarLowerStarAdjunction Λ a.imageι).counit.app
        ((CondensedRing.openImmersionLowerShriek Λ a.toImage).obj L))

/-- Comparison on the actual fibre product, obtained only from pullback composition,
the pullback-square equation, and the normalized restriction comparison.
Source: direct-image stability proof (3), q^* V' identified with b^* L
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
def fibreRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S R X : Scheme.{u}}
    (a : S ⟶ X) (r : R ⟶ X)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (ρ : (CondensedRing.upperStar Λ a).obj F ≅ L) :
    (CondensedRing.upperStar Λ (pullback.fst r a)).obj
      ((CondensedRing.upperStar Λ r).obj F) ≅
    (CondensedRing.upperStar Λ (pullback.snd r a)).obj L :=
  ((CondensedRing.upperStarComp Λ (pullback.fst r a) r).app F).symm ≪≫
    eqToIso (congrArg (fun f : pullback r a ⟶ X ↦ (CondensedRing.upperStar Λ f).obj F)
      (pullback.condition (f := r) (g := a))) ≪≫
    (CondensedRing.upperStarComp Λ (pullback.snd r a) a).app F ≪≫
    (CondensedRing.upperStar Λ (pullback.snd r a)).mapIso ρ


/-- The specified finite-field model on a refined stratum is the restriction of the
old supported model, not a newly chosen lisse module.
Source: direct-image stability proof (3), V'_t = F_a(t)|R_t
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
def refinedModel {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {S R : Scheme.{u}}
    (a : S ⟶ X.left) (ha : IsImmersion a)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) S)) (r : R ⟶ X.left) :
    Mod (Sheaf (Scheme.ProEt.topology R) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) R) :=
  (CondensedRing.upperStar (Profinite.continuousMapRingObj E) r).obj
    ((extension X (Profinite.continuousMapRingObj E) a ha).obj L)

/-- Equality after pullback to R times_X S, using the canonical scalar comparison,
the square equation, and the normalized old-stratum restriction. This records the
given phi rather than merely asserting existence of some finite-field model.
Source: direct-image stability proof (3), q^* psi = b^* phi
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration). -/
def ModelCompatible
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (α : A ⟶ B) [IsMonHom α] {S R X : Scheme.{u}}
    (a : S ⟶ X) (r : R ⟶ X)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (φ : (Mod.extendScalars (coefficientMap α S)).obj L ≅
      (CondensedRing.upperStar B a).obj M)
    (ρ : (CondensedRing.upperStar A a).obj F ≅ L)
    (ψ : (Mod.extendScalars (coefficientMap α R)).obj
      ((CondensedRing.upperStar A r).obj F) ≅ (CondensedRing.upperStar B r).obj M) : Prop :=
  (CondensedRing.upperStar B (pullback.fst r a)).map ψ.hom ≫
      (fibreRestriction B a r M ((CondensedRing.upperStar B a).obj M) (Iso.refl _)).hom =
    (CondensedRing.pullIso α (pullback.fst r a)).inv.app
        ((CondensedRing.upperStar A r).obj F) ≫
      (Mod.extendScalars (coefficientMap α (pullback r a))).map
        (fibreRestriction A a r F L ρ).hom ≫
      (CondensedRing.pullIso α (pullback.snd r a)).hom.app L ≫
      (CondensedRing.upperStar B (pullback.snd r a)).map φ.hom

/-- Ordered finite-field models with their prescribed pullback compatibility and the
finite filtration by actual open-extension counits.

Source: blueprint main-20261015, direct-image stability proof paragraph (3),
extracted ordered finite-model obligation; norm-topology literature reference WANTED.
(blueprint: lem-sfb-norm-algcl-ordered-finite-model-filtration).

Proof plan, following the seven steps of the node:
1. Finite type over k makes X Noetherian. Apply
lem-sfb-coefficient-heart-lisse-extension-constructible separately over each E_a;
lem-sfb-locally-closed-module-extension-coherence identifies the supported extension.
Use sk-def-sfb-constructible to choose a finite adapted partition for each F_a.
2. Apply new-det-lem-coefficient-heart-common-stratification-refinement simultaneously
to these partitions and the supplied partition. The lisse clause
new-det-lem-coefficient-heart-common-stratification-lisse makes every F_a lisse on
each refined stratum. It requires image containment only.
3. For W = R times_X S, immersion base change and containment of images make q a
surjective immersion. Its image is closed, hence q is closed. Apply
new-lem-weil-pbc-condensed-surjective-closed-equivalence to B.
4. The normalized extension restriction identifies q^*V' with b^*L. The canonical
scalar pullback comparison identifies the scalar extensions. Full faithfulness
uniquely descends b^*phi to psi, with exactly ModelCompatible; conservativity makes
it invertible. Use sk-def-sfb-module-pushforward-pullback, sk-def-sfb-change-of-scalars,
lem-sfb-finite-upper-star-tensor and sk-def-sfb-pullback-from-point-comp.
5. Use lem-weil-pbc-proetale-ringed-open-closed for every open prefix and its reduced
closed complement (lem-weil-pbc-reduced-induced-closed-subscheme). Its counit is mono.
The difference stratum is closed in the larger prefix. All needed opens are
quasi-compact by lem-sfb-coefficient-heart-locally-closed-extension.
6. Apply exact open extension to the localization sequence inside each prefix.
Normalized immersion composition and adjunction transposition identify the first
arrow over M with the preceding counit. The cokernel is the supported restriction;
apply extension to psi inverse for the displayed finite-model quotient. Empty and
whole opens give zero and M. Use lem-sfb-locally-closed-module-extension-coherence.
7. Apply lem-sf-derived-ses-triangle to each resulting short exact sequence of
internal B_X-modules. Its singleTriangle is the corresponding distinguished triangle
in the ordinary unbounded derived category. Empty X uses no strata; zero M gives
zero terms. Neither strictness nor nonempty strata nor positive rank is required. -/
theorem orderedFiniteModelFiltration
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X.left))
    (hM : IsConstantModelConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X.left M)
    (P : Scheme.Stratification X.left)
    (E : Fin P.n → PadicAlgCl.FiniteIntermediateField ℓ)
    (L : ∀ a : Fin P.n, Mod (Sheaf (Scheme.ProEt.topology (P.domain a)) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (E a)) (P.domain a)))
    (hL : ∀ a : Fin P.n, IsLisseCoefficientModule (Profinite.continuousMapRingObj (E a)) (L a))
    (φ : ∀ a : Fin P.n, (scalarExtension ℓ (E a) (P.domain a)).obj (L a) ≅
      (CondensedRing.upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ))
        (P.immersion a)).obj M) :
    ∃ ρ : ∀ a : Fin P.n,
        (CondensedRing.upperStar (Profinite.continuousMapRingObj (E a)) (P.immersion a)).obj
          ((extension X (Profinite.continuousMapRingObj (E a))
            (P.immersion a) (P.isImmersion a)).obj (L a)) ≅ L a,
      (∀ a : Fin P.n, RestrictionNormalized X (Profinite.continuousMapRingObj (E a))
        (P.immersion a) (P.isImmersion a) (L a) (ρ a)) ∧
    ∃ (R : X.left.FiniteLocallyClosedStratification)
      (V : Fin (R.n + 1) → X.left.Opens) (a : Fin R.n → Fin P.n),
      (∀ t : Fin (R.n + 1),
        (V t : Set X.left) = ⋃ s : Fin R.n, ⋃ (_ : s.val < t.val), R.stratum s) ∧
      V 0 = ⊥ ∧ V (Fin.last R.n) = ⊤ ∧
      (∀ t : Fin R.n, R.stratum t ⊆ P.stratum (a t)) ∧
      (∀ (b : Fin P.n) (t : Fin R.n),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj (E b))
          (refinedModel ℓ X (E b) (P.immersion b) (P.isImmersion b) (L b)
            (R.immersion t))) ∧
    ∃ ψ : ∀ t : Fin R.n,
        (scalarExtension ℓ (E (a t)) (R.domain t)).obj
          (refinedModel ℓ X (E (a t)) (P.immersion (a t)) (P.isImmersion (a t))
            (L (a t)) (R.immersion t)) ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ))
          (R.immersion t)).obj M,
      (∀ t : Fin R.n,
        IsClosedImmersion (pullback.fst (R.immersion t) (P.immersion (a t))) ∧
        Surjective (pullback.fst (R.immersion t) (P.immersion (a t))) ∧
        ModelCompatible (scalarInclusion ℓ (E (a t))) (P.immersion (a t))
          (R.immersion t) ((extension X (Profinite.continuousMapRingObj (E (a t)))
            (P.immersion (a t)) (P.isImmersion (a t))).obj (L (a t)))
          (L (a t)) M (φ (a t)) (ρ (a t)) (ψ t)) ∧
      (∀ t : Fin (R.n + 1), Mono (coefficientHeartOpenCounit
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) M (V t))) ∧
      IsZero (coefficientHeartOpenTerm (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) M (V 0)) ∧
      IsIso (coefficientHeartOpenCounit
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) M (V (Fin.last R.n))) ∧
    ∃ d : ∀ t : Fin R.n,
        coefficientHeartOpenTerm (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) M (V t.castSucc) ⟶
          coefficientHeartOpenTerm (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) M (V t.succ),
      ∀ t : Fin R.n,
        d t ≫ coefficientHeartOpenCounit (Profinite.continuousMapRingObj (PadicAlgCl ℓ))
          M (V t.succ) =
        coefficientHeartOpenCounit (Profinite.continuousMapRingObj (PadicAlgCl ℓ))
          M (V t.castSucc) ∧
        Nonempty (cokernel (d t) ≅
          (extension X (Profinite.continuousMapRingObj (PadicAlgCl ℓ))
            (R.immersion t) (R.isImmersion t)).obj
              ((scalarExtension ℓ (E (a t)) (R.domain t)).obj
                (refinedModel ℓ X (E (a t)) (P.immersion (a t)) (P.isImmersion (a t))
                  (L (a t)) (R.immersion t)))) ∧
        ∃ h : (ShortComplex.mk (d t) (cokernel.π (d t)) (cokernel.condition (d t))).ShortExact,
          h.singleTriangle ∈ distTriang _ := by
  sorry

end AlgebraicGeometry.ProEtale.NormAlgclOrderedModels
