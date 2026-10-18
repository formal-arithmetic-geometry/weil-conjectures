/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized
import Sheaf.Paper.EtaleLocalMonodromyRealization
import Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients
import Sheaf.Paper.CoefficientFiniteDescentLisse
import Sheaf.Paper.CondensedFlatCoefficientCalculus
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.Monoidal.Mod
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-!
# Closure of lisse and constructible coefficient sheaves

Source: Weil blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart/
sk-lem-coefficient-heart-closure.md, clauses (1)--(2) and the concluding paragraph
(blueprint: det-lem-coefficient-heart-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Lisse coefficient sheaves are closed under extensions, kernels and cokernels on a
 topologically Noetherian scheme. On a Noetherian scheme, constructible sheaves form an
 abelian full subcategory with exact inclusion and are exactly the sheaves lisse on a
 finite stratification.
Source: blueprint coefficient-heart-closure, clauses (1)--(2) and concluding paragraph
(blueprint: det-lem-coefficient-heart-closure).

Proof plan (the eight steps of the DAG node):
1. The scalar rings of E and Qbar_l are fields. A finitely presented scalar module has
 a finite basis, so det-def-sfb-constructible-local-model identifies finite constant
 local models with pro-etale local finite freeness. For an extension, trivialize its
 end terms on a common cover. Cartesian coefficients identify restriction with exact
 inverse image (sk-prop-sfb-cartesian-coefficients). Lift the finitely many quotient
 basis sections after successive covering refinements, using
 lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective and lem-sfb-modobj-cokernels.
 These lifts split the sequence, making its middle term a finite direct sum of free
 modules; rank zero is allowed. The underlying abelian-sheaf and tensor hypotheses
 follow from lem-weil-pbc-site-sheaves-enough-injectives and sk-def-sfb-sheaf-tensor.
2. For E, identify the pulled-back condensed coefficient ring with continuous-function
 coefficients by def-sfb-subfield-coefficient-ring,
 lem-weil-pbc-condensed-field-continuous-realization and
 def-weil-pbc-lisse-lattice-coefficients. This identification preserves standard bases.
 Apply lem-sfb-etale-local-monodromy-realization to the finite diagram F to G.
3. Apply lem-sfb-continuous-representation-subquotients to its representation map.
 The realization's ambient exactness identifies the realized quotient with the
 ambient cokernel. Exact restriction from sk-prop-sfb-cartesian-coefficients then
 identifies it with the restricted sheaf cokernel, which is locally finite free.
4. For Qbar_l, a topologically Noetherian scheme is qcqs. Use clause (1) of
 det-lem-coefficient-finite-descent-lisse to descend both objects to finite fields;
 their compositum is finite because products of spanning elements span it.
5. Scalar extension sends a finite basis to a finite basis. Use the specified tensor
 comparisons of lem-weil-pbc-condensed-flat-coefficient-calculus and clause (2) of
 det-lem-coefficient-finite-descent-lisse to descend the actual transported morphism
 to a larger finite subextension, not merely its endpoints up to isomorphism.
6. Its finite-field cokernel is lisse. The left adjoint of sk-def-sfb-change-of-scalars
 preserves cokernels, so its Qbar_l extension is the original cokernel and is lisse.
 Use the coefficient colimit of sk-prop-sfb-qlbar-colimit-x and the colimit-preserving
 tensor of sk-def-sfb-sheaf-tensor; no preservation of kernels is needed here.
7. For either coefficient, take finite-free duals using def-sfb-modobj-internal-hom.
 Its Grothendieck hypotheses follow from lem-weil-pbc-ring-sheaves-grothendieck for
 the integer ring sheaf, and its tensor hypotheses from sk-def-sfb-sheaf-tensor.
 The cokernel D of the transpose is lisse. Evaluation identifies ker(phi) with D dual:
 v gives the functional [lambda] mapped to lambda(v). Conversely, a functional a
 gives sum_i a([e_i dual]) e_i in a finite basis. Annihilating the transpose image
 says phi(v) = 0. These inverse constructions are basis independent and commute
 with restriction, hence glue. Dual bases prove local finite freeness, also in rank zero.
8. Use det-lem-coefficient-heart-common-stratification to adapt a finite stratification
 to both objects, or to the end terms of an extension. Restriction to each stratum
 is exact; its underlying space is Noetherian. The preceding local results and
 sk-def-sfb-constructible give global closure and the stratification equivalence.
 The ambient category is abelian by lem-sfb-modobj-abelian, using the abelian sheaf
 and tensor hypotheses already cited. Zero and finite direct sums are constructible.
 Fullness gives the ambient kernels and cokernels their universal properties inside
 Cons. The ambient coimage-image isomorphism and its inverse lie in Cons, proving
 abelianity; these same kernels and cokernels make the inclusion exact. -/
theorem coefficientHeart_closure (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ) :
    (∀ (S : Scheme.{u}) [TopologicalSpace.NoetherianSpace S],
      ObjectProperty.IsClosedUnderExtensions
        (IsLisseCoefficientModule ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) (X := S)) ∧
      ObjectProperty.IsClosedUnderKernels
        (IsLisseCoefficientModule ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) (X := S)) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsLisseCoefficientModule ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) (X := S))) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X],
      ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X) ∧
      Nonempty (Abelian (ConstantModelConstructible ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X)) ∧
      PreservesFiniteLimits
        (ObjectProperty.ι (IsConstantModelConstructible
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X)) ∧
      PreservesFiniteColimits
        (ObjectProperty.ι (IsConstantModelConstructible
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X)) ∧
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj ((sheafCompose (coherentTopology Profinite.{u})
              (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X),
        IsConstantModelConstructible ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X M ↔
          ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
            IsLisseCoefficientModule ((sheafCompose (coherentTopology Profinite.{u})
                (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ)
              ((CondensedRing.upperStar ((sheafCompose (coherentTopology Profinite.{u})
                  (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) (R.immersion a)).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale
