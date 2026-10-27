/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.SpaceOpenImmersionEtaleLocal

/-!
# Affine factorizations of quasi-affine algebraic-space morphisms

Source: Stacks Project, Morphisms of Spaces, Tag 086S
(lemma-characterize-quasi-affine), with the canonical factorization of Tag 081X;
used in Tag 0871 (blueprint: lem-sfb-space-quasiaffine-affine-factorization).

Quasi-affineness is spelled out on affine scheme tests using the existing
`Scheme.IsQuasiAffine`, which includes quasi-compactness. Representability and
open immersion use the scheme-test predicates of `AlgebraicSpace`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-affine morphism factors through a quasi-compact open immersion and an
affine morphism. No quasi-compactness or quasi-separatedness of the target is assumed.
Source: Stacks Project, Morphisms of Spaces, Tag 086S, forward implication, and
Tag 081X (blueprint: lem-sfb-space-quasiaffine-affine-factorization).

Proof:
1. Choose affine etale charts U_a of Y [lem-a1-space-affine-etale-cover]. Their
   pullbacks X_a are quasi-affine schemes. The canonical affine-embedding lemma
   [lem-trf-quasi-affine-canonical-affine-embedding] gives quasi-compactness and
   absolute separation of X_a. Affine schemes are quasi-separated
   [lem-weil-pbc-affine-scheme-qcqs], so the morphism permanence lemma
   [lem-weil-pbc-qcqs-morphism-permanence] gives quasi-compactness of X_a -> U_a.
   Its relative diagonal is a base change of the absolute closed diagonal of X_a
   [lem-weil-pbc-closed-immersion-base-change]. Descend quasi-compactness and
   separation by [lem-trf-space-qc-separated-etale-local].
2. The structure module is quasi-coherent, with its one-generator, no-relation
   presentation [def-trf-space-quasi-coherent-module]. Its direct image A = f_* O_X
   is quasi-coherent by [lem-trf-space-qc-separated-quasi-coherent-pushforward].
   Multiplication and unit on sections make it an O_Y-algebra. Relative Spec
   [lem-sfb-space-relative-spec-correspondence] supplies Z and affine p : Z -> Y.
3. The evaluation counit f^* A -> O_X [def-trf-space-etale-module-functors] is an
   algebra map. Its source is quasi-coherent
   [lem-sfb-space-module-pullback-quasicoherent]. Relative Spec and its base-change
   compatibility give X -> X x_Y Z -> Z, defining j with j followed by p equal to f.
4. On each U_a, the identity-on-sections restriction comparison
   [lem-trf-space-etale-module-pushforward-restriction] identifies A with
   (f_a)_* O_{X_a}, preserving multiplication and unit. The relative-Spec chart
   formula identifies Z_a with Spec Gamma(X_a, O). Evaluation sends each global
   function to itself, so uniqueness [lem-weil-pbc-morphism-into-affine-scheme]
   identifies j_a with the canonical map to Spec of global functions.
5. The canonical affine-embedding lemma makes j_a an open immersion with
   quasi-compact separated source. Its affine target is quasi-separated, so
   morphism permanence makes j_a quasi-compact. Its relative diagonal is closed
   by the same absolute-diagonal base-change argument as in step 1.
6. Base change gives the jointly surjective etale family Z_a -> Z
   [lem-trf-space-fibre-products-etale-covers]. The base change of j there is j_a.
   Descend open immersion by [lem-trf-space-open-immersion-etale-local], and
   quasi-compactness and separation by [lem-trf-space-qc-separated-etale-local].
   The resulting quasi-compact open immersion j and affine p give the factorization. -/
theorem exists_quasiCompact_openImmersion_affine_factorization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hrep : IsRepresentable f.hom.hom)
    (hqa : ∀ (T : Over S) (_ : IsAffine T.left) (a : yoneda.obj T ⟶ Y.obj.obj),
      ∃ (U : Over S) (_ : U.left.IsQuasiAffine) (p : U ⟶ T)
        (q : yoneda.obj U ⟶ X.obj.obj), IsPullback q (yoneda.map p) f.hom.hom a) :
    ∃ (Z : AlgebraicSpace S) (j : X ⟶ Z) (p : Z ⟶ Y),
      IsQuasiCompactPresheafMap j.hom.hom ∧
      IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) j.hom.hom ∧
      MapIsAffine p ∧ j ≫ p = f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
