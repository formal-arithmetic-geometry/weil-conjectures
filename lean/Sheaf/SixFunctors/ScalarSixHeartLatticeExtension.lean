/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def


/-! # Constructibility in the coefficient heart

The statement transports the integral-generator calculation to the published
normalized locally closed extension on internal module objects.
Source: blueprint main-20261015, rational proper base change, paragraph (3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Extending a lisse integral lattice by the normalized exact locally closed
extension gives a constructible module in the coefficient heart.

Source: blueprint main-20261015, proper-base-change rational proof, paragraph (3),
common-field argument step 4; integral generators, clause (3).
(blueprint: lem-sfb-normalized-integral-heart-extension-constructible).

Proof: Factor the immersion as an open immersion into its closed image followed
by the closed immersion into W. The hypotheses on W make it Noetherian. Under the
internal/sectionwise module equivalence, H's open extension and the actual open
extension are left adjoints to the same inverse image, so their unit-normalized
comparison is invertible. Its closed comparison is H.closedComparison. The gamma
of H and its coherence identify H's extension along the composite with the
closed direct image of the open extension. The normalization of G identifies the
coefficient arrows in these comparisons with the actual condensed coefficient
arrows. A lisse lattice has the finite free local presentations required by
integral_models_generators (3). Apply that clause to the open/closed factorization.
It gives finite constant local models for its degree-zero extension. Each such
model is, by definition, the pullback of a finitely presented condensed module.
Map its finite-free cokernel presentation by inverse image from the point. The
inverse image is exact, additive and monoidal, so this is a finite presentation
on the scheme. Restriction along the invertible condensed coefficient comparison
preserves these presentations. On each of the finitely many strata, compose the
trivializing covers to obtain locally finite presentation. Transport along the
preceding normalized comparisons and use invariance of module constructibility
under isomorphism. The argument also covers rank zero and the empty stratum;
both give the zero module.
-/
theorem normalized_integral_heart_extension_constructible
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] (hne : ell ≠ p)
    (H : LocallyClosedExtensionData.{u}) (hH : H.Coherent)
    (G : ScalarSixGeometry.{u})
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (W Z : Over (Spec (.of k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (a : Z ⟶ W) [IsImmersion a.left]
    (M : ModuleRingedComparison.internalModules
      (Profinite.padicIntegersRingObj ell E.1) Z.left)
    (hM : IsLisseCoefficientModule (Profinite.padicIntegersRingObj ell E.1) M) :
    IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) W.left)
      ((ModuleRingedComparison.equivalence
          (Profinite.padicIntegersRingObj ell E.1) W.left).inverse.obj
        ((H.extension (scalarSixImmersion G
            (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing) a)).obj
          ((ModuleRingedComparison.equivalence
            (Profinite.padicIntegersRingObj ell E.1) Z.left).functor.obj M))) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
