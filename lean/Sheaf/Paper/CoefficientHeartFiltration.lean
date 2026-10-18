/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Subobject.Lattice
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CoefficientHeartClosure

/-!
# The filtration associated to an adapted coefficient stratification

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart/
sk-lem-coefficient-heart-filtration.md and its proof
(blueprint: det-lem-coefficient-heart-filtration).

The filtration steps are the images of the actual open-extension counits. The theorem
asserts that those counits are monomorphisms, so the images represent exactly the given
extensions by zero as subsheaves of F. Locally closed extension is the open extension
into the scheme-theoretic closure followed by its closed direct image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The specified object `v_! v^* F` for an open subscheme V.
Source: blueprint sk-lem-coefficient-heart-filtration, definition of F_k
(blueprint: det-lem-coefficient-heart-filtration). -/
abbrev coefficientHeartOpenTerm {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) :=
  (CondensedRing.openImmersionLowerShriek Λ V.ι).obj
    ((CondensedRing.upperStar Λ V.ι).obj F)

/-- The canonical map from the open-extension term to F, namely the adjunction counit.
Source: blueprint sk-lem-coefficient-heart-filtration, definition of the inclusions
(blueprint: det-lem-coefficient-heart-filtration). -/
abbrev coefficientHeartOpenCounit {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) : coefficientHeartOpenTerm Λ F V ⟶ F :=
  (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ V.ι).counit.app F

/-- The subsheaf represented by the image of the canonical counit. Its equality with the
open-extension object as a subsheaf follows from the monomorphism assertion below.
Source: blueprint sk-lem-coefficient-heart-filtration, F_k as a subsheaf of F
(blueprint: det-lem-coefficient-heart-filtration). -/
abbrev coefficientHeartFiltrationStep {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) : Subobject F :=
  imageSubobject (coefficientHeartOpenCounit Λ F V)

/-- For a locally closed immersion a into a topologically Noetherian scheme, use its
canonical scheme-theoretic closure: `a.toImage` is open and `a.imageι` is closed.
The source is topologically Noetherian because an immersion is a topological embedding;
therefore a is quasi-compact and the existing open-immersion instance for `a.toImage`
applies. No choice of an extension functor is made.
Source: blueprint sk-lem-coefficient-heart-filtration, definition `a_! = i_* u_!`
(blueprint: det-lem-coefficient-heart-filtration). -/
def coefficientHeartLocallyClosedExtension {S X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (a : S ⟶ X) (ha : IsImmersion a) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  CondensedRing.openImmersionLowerShriek Λ a.toImage ⋙ CondensedRing.lowerStar Λ a.imageι

/-- The given ordered adapted stratification produces the counit filtration, with its
successive quotients the extensions by zero of the lisse restrictions. `V` is simply a
presentation of the open prefixes; its carrier equation fixes every V_k, including
V_0 and V_m. No connectedness or strictness condition is imposed.

Source: blueprint sk-lem-coefficient-heart-filtration and its proof
(blueprint: det-lem-coefficient-heart-filtration).

Proof plan:
1. Use sk-prop-sfb-cartesian-coefficients to identify coefficient inverse images and
module pullbacks. Noetherian open subschemes are Noetherian and quasi-separated
(lem-weil-pbc-noetherian-open-subscheme-noetherian and
lem-weil-pbc-locally-noetherian-quasi-separated). All open immersions between the
prefixes are quasi-compact. Apply det-sf-open-closed-sequence-ring-sheaf (3) to see
that each open counit is mono. Its clauses (1) and the normalized pure-open composition
of lem-sfb-locally-closed-extension-coherence identify the nesting maps over F: their
adjuncts restrict to the identity. Extension from the empty open is zero and extension
along the identity is the identity, giving the bottom and top endpoints.
2. On V_k use the localization sequence for V_{k-1} and its closed complement S_k.
Apply the exact open extension from V_k to X. The nesting map is the map over F from
step 1, so its cokernel is exactly the quotient of these two image subobjects.
3. Apply lem-sfb-locally-closed-extension-coherence to compare this closed-then-open
extension with open extension into the closure followed by closed direct image. The
comparison is normalized by restriction to S_k, and gives the stated quotient isomorphism.
4. Adaptedness and det-lem-coefficient-heart-closure identify the finite constant
local models over E or Qlb with locally finite free modules. Thus every restriction
is lisse. In the zero-sheaf case the inclusions are equal, as allowed in the statement. -/
theorem coefficientHeart_filtration (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj L) X))
    (hF : IsConstantModelConstructible (coefficientHeartRingObj L) X F)
    (R : X.FiniteLocallyClosedStratification)
    (hadapt : ∀ a : Fin R.n,
      HasFiniteConstantLocalModel (coefficientHeartRingObj L) (R.domain a)
        ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F))
    (V : Fin (R.n + 1) → X.Opens)
    (hV : ∀ k : Fin (R.n + 1),
      (V k : Set X) = ⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) :
    (∀ k : Fin (R.n + 1),
      Mono (coefficientHeartOpenCounit (coefficientHeartRingObj L) F (V k))) ∧
    coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V 0) = ⊥ ∧
    coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V (Fin.last R.n)) = ⊤ ∧
    ∃ h : ∀ a : Fin R.n,
      coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.castSucc) ≤
        coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.succ),
      ∀ a : Fin R.n,
        Nonempty (cokernel (Subobject.ofLE
          (coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.castSucc))
          (coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.succ)) (h a)) ≅
          (coefficientHeartLocallyClosedExtension (coefficientHeartRingObj L)
            (R.immersion a) (R.isImmersion a)).obj
              ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F)) ∧
        IsLisseCoefficientModule (coefficientHeartRingObj L)
          ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F) := by
  sorry

end AlgebraicGeometry.ProEtale
