/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs

/-!
# Evaluation from local projective quotients

Source: Stacks Project, Morphisms, Tags 01VR (the beginning of (2) implies (4))
and 01VQ (blueprint: lem-trf-local-quotient-evaluation).

The comparison maps below use the actual section-normalized tensor adjunction.
Restrictions are Mathlib's sectionwise restriction functor for open immersions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison from pulling back a restriction to restricting a pullback.
It is the composite of the normalized composition comparisons around the restriction square.
Open restriction is compared with tensor pullback by the unique left-adjoint comparison of
Mathlib's restriction adjunction and the section-normalized tensor adjunction (the comparison
of lem-weil-pbc-open-immersion-module-pullback-restriction, written out here).
Source: Stacks, Tag 01VR, evaluation-factorization paragraph; Sheaves, Tags 0096, 0097
(blueprint: lem-trf-local-quotient-evaluation). -/
noncomputable def localQuotientPullbackRestrictionIso {Z X : Scheme.{u}} (g : Z ⟶ X)
    (V : X.Opens) (M : X.Modules) :
    (tensorPullback (g ∣_ V)).obj (M.restrict V.ι) ≅
      ((tensorPullback g).obj M).restrict (g ⁻¹ᵁ V).ι :=
  (tensorPullback (g ∣_ V)).mapIso
      (((restrictAdjunction V.ι).leftAdjointUniq (tensorPullbackSectionAdjunction V.ι)).app M) ≪≫
    (tensorPullbackSectionComp (g ∣_ V) V.ι).symm.app M ≪≫
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj M) (morphismRestrict_ι g V)) ≪≫
    (tensorPullbackSectionComp (g ⁻¹ᵁ V).ι g).app M ≪≫
    ((restrictAdjunction (g ⁻¹ᵁ V).ι).leftAdjointUniq
      (tensorPullbackSectionAdjunction (g ⁻¹ᵁ V).ι)).symm.app ((tensorPullback g).obj M)

/-- Restrict the actual global evaluation counit and transpose it along the restricted map.
This is the canonical direct-image/restriction comparison, whose sections identify both
sides with N(g^{-1}W), rather than a freely chosen isomorphism of the two modules.
Source: Stacks, Tag 01VR, evaluation-factorization paragraph; Sheaves, Tag 0096
(blueprint: lem-trf-local-quotient-evaluation). -/
noncomputable def localQuotientPushforwardRestrictionMap {Z X : Scheme.{u}} (g : Z ⟶ X)
    (N : Z.Modules) (V : X.Opens) :
    ((pushforward g).obj N).restrict V.ι ⟶
      (pushforward (g ∣_ V)).obj (N.restrict (g ⁻¹ᵁ V).ι) :=
  (tensorPullbackSectionAdjunction (g ∣_ V)).homEquiv _ _
    ((localQuotientPullbackRestrictionIso g V ((pushforward g).obj N)).hom ≫
      (restrictFunctor (g ⁻¹ᵁ V).ι).map ((tensorPullbackSectionAdjunction g).counit.app N))

/-- Pull the normalized tautological quotient through the specified twist isomorphism.
Source: Stacks, Tag 01VR, proof (2) implies (4), local quotient paragraph
(blueprint: lem-trf-local-quotient-evaluation). -/
noncomputable def localProjectiveQuotient {Z X : Scheme.{u}} (g : Z ⟶ X) (N : Z.Modules)
    (V : X.Opens) (E : V.toScheme.Modules) [E.IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (i : (g ⁻¹ᵁ V).toScheme ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hi : i ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = g ∣_ V)
    (e : (tensorPullback i).obj D.line ≅ N.restrict (g ⁻¹ᵁ V).ι) :
    (tensorPullback (g ∣_ V)).obj E ⟶ N.restrict (g ⁻¹ᵁ V).ι :=
  ProjectiveBundleQuotientGeometry.pulledQuotient D (g ∣_ V) i hi ≫ e.hom

/-- Local projective immersions give separatedness, quasi-coherent direct image,
surjective evaluation, the specified adjoint factorizations and a unique classifying map.
No finite-generation or local-freeness condition is imposed on the local modules.

Source: Stacks Project, Morphisms, Tags 01VQ and 01VR, proof (2) implies (4), before
its immersion comparison (blueprint: lem-trf-local-quotient-evaluation).

Proof, following the node's six steps:
1. Each local projective projection is separated by
lem-trf-projective-bundle-quotient-geometry. Compose with the immersion using
lem-trf-immersion-over-separated-base, then descend along the open cover using
lem-sfb-separated-lfp-target-open-locality. The cover need not be finite.
2. Apply lem-pc-separated-quasi-separated. Invertibility gives quasi-coherence of N;
quasi-compactness and quasi-separatedness give quasi-coherence of g_*N by
pqf-lem-pushforward-qcoh. Its sections are N(g^{-1}W).
3. Pull back each tautological epimorphism and compose with the chosen line isomorphism.
Use lem-weil-pbc-module-pullback-epi-direct-sum and the normalized composition comparison
of lem-pc-module-pullback-identity-composition to obtain the surjective local quotient.
4. On W contained in V_j, the restricted direct image and the direct image of the
restriction have the same sections N(g^{-1}W), restrictions and scalar actions. The
comparison map displayed here is that identification: both normalized counits send
a tensor germ a tensor s to a*s. Transpose q_j by lem-pc-module-pullback-adjunction,
then apply the inverse sectionwise comparison to obtain alpha_j. The inverse Hom
bijection is pullback of alpha_j followed by the counit. Open restriction agrees with
tensor pullback by lem-weil-pbc-open-immersion-module-pullback-restriction, so this counit
is precisely the restricted global counit under localQuotientPullbackRestrictionIso.
5. Each germ of N lies locally in the image of q_j, hence of evaluation by step 4.
The inverse images of the V_j cover Z, so evaluation is surjective on every stalk.
6. Apply lem-trf-projective-bundle-quotient-geometry to the quasi-coherent module g_*N
and the invertible quotient (N, evaluation). Its unique-classifying-morphism clause
gives the required r and the quotient-compatible twist isomorphism in Classifies. -/
theorem local_quotient_evaluation {Z X : Scheme.{u}} (g : Z ⟶ X) [QuasiCompact g]
    (N : Z.Modules) [N.IsInvertible] (J : Type v) (V : J → X.Opens)
    (hV : iSup V = ⊤) (E : ∀ j : J, (V j).toScheme.Modules)
    [hE : ∀ j : J, (E j).IsQuasicoherent]
    (D : ∀ j : J, ProjectiveBundleQuotientGeometry.TautologicalQuotient (E j))
    (i : ∀ j : J, (g ⁻¹ᵁ V j).toScheme ⟶
      (SymmetricAlgebraSheaf.gradedAlgebraData (E j)).relProj)
    (hi : ∀ j : J,
      i j ≫ (SymmetricAlgebraSheaf.gradedAlgebraData (E j)).relProjHom = g ∣_ V j)
    (himm : ∀ j : J, IsImmersion (i j))
    (e : ∀ j : J, (tensorPullback (i j)).obj (D j).line ≅ N.restrict (g ⁻¹ᵁ V j).ι) :
    IsSeparated g ∧ QuasiSeparated g ∧
      Epi ((tensorPullbackSectionAdjunction g).counit.app N) ∧
      (∀ j : J,
        ∃ b : ((pushforward g).obj N).restrict (V j).ι ≅
          (pushforward (g ∣_ V j)).obj (N.restrict (g ⁻¹ᵁ V j).ι),
          b.hom = localQuotientPushforwardRestrictionMap g N (V j) ∧
          ∃ α : E j ⟶ ((pushforward g).obj N).restrict (V j).ι,
            α = (tensorPullbackSectionAdjunction (g ∣_ V j)).homEquiv _ _
              (localProjectiveQuotient g N (V j) (E j) (D j) (i j) (hi j) (e j)) ≫ b.inv ∧
            localProjectiveQuotient g N (V j) (E j) (D j) (i j) (hi j) (e j) =
              (tensorPullback (g ∣_ V j)).map α ≫
                (localQuotientPullbackRestrictionIso g (V j) ((pushforward g).obj N)).hom ≫
                (restrictFunctor (g ⁻¹ᵁ V j).ι).map
                  ((tensorPullbackSectionAdjunction g).counit.app N)) ∧
      ∃ hF : ((pushforward g).obj N).IsQuasicoherent,
        ∃ DF : @ProjectiveBundleQuotientGeometry.TautologicalQuotient X
          ((pushforward g).obj N) hF,
          ∃! r : Z ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData X
            ((pushforward g).obj N) hF).relProj,
            @ProjectiveBundleQuotientGeometry.Classifies X ((pushforward g).obj N) hF
              DF Z g N ((tensorPullbackSectionAdjunction g).counit.app N) r := by
  sorry

end AlgebraicGeometry.Scheme.Modules
