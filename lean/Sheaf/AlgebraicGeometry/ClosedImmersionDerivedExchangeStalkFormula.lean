/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import Sheaf.AlgebraicGeometry.ClosedIdealBaseChangeAffineDiagram
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso
import Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionIsIso

/-! # Closed-immersion derived exchange on ordinary Zariski stalks

Source: Stacks Project, perfect.tex, Tag 0E23,
lemma-compare-base-change-closed-immersion, the proof before Tor independence.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula).

The tensor models below reuse the functorial K-flat models of RingTensorCohomology.
Natural isomorphisms are stated after precomposition with the localization Q;
this expresses naturality for all derived objects, since Q is a localization.
The target's transport to the actual fibre-product stalk is specified on pure tensors.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

noncomputable section
namespace AlgebraicGeometry.ClosedImmersionExchange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {Z X Z' X' : Scheme.{u}}
  (i : Z ⟶ X) (i' : Z' ⟶ X') (f : X' ⟶ X) (g : Z' ⟶ Z)
  (sq : IsPullback g i' i f)

/-- The base-to-new-base stalk map, with the equality of ambient points transported
as in the recorded stalk-square interface. Source: Stacks Tag 0E23, proof.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula). -/
def baseMap (z' : Z') :
    SingleComplexBaseChange.R i g z' →+* SingleComplexBaseChange.B i' z' :=
  letI := SingleComplexBaseChange.rightAlgebra i i' f g sq z'
  algebraMap _ _

/-- The functorial model of M tensor-derived-over-R B. Source: Stacks Tag 0E23,
proof, and More on Algebra, equation comparison-map.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula). -/
def sourceModel (z' : Z') :
    CochainComplex (ModuleCat.{u} (SingleComplexBaseChange.A g z')) ℤ ⥤
      CochainComplex (ModuleCat.{u} (SingleComplexBaseChange.B i' z')) ℤ :=
  letI := SingleComplexBaseChange.leftAlgebra i g z'
  letI := SingleComplexBaseChange.rightAlgebra i i' f g sq z'
  RingTensorCohomology.sourceComplex
    (SingleComplexBaseChange.R i g z') (SingleComplexBaseChange.A g z')
    (SingleComplexBaseChange.B i' z')

/-- The functorial model of Res_B(M tensor-derived-over-A (A tensor_R B)).
Source: Stacks Tag 0E23, proof, and More on Algebra, equation comparison-map.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula). -/
def targetModel (z' : Z') :
    CochainComplex (ModuleCat.{u} (SingleComplexBaseChange.A g z')) ℤ ⥤
      CochainComplex (ModuleCat.{u} (SingleComplexBaseChange.B i' z')) ℤ :=
  letI := SingleComplexBaseChange.leftAlgebra i g z'
  letI := SingleComplexBaseChange.rightAlgebra i i' f g sq z'
  RingTensorCohomology.targetComplex
    (SingleComplexBaseChange.R i g z') (SingleComplexBaseChange.A g z')
    (SingleComplexBaseChange.B i' z')

/-- The same target expressed using the actual stalk C and its actual maps A -> C
and B -> C. Resolve over A, extend to C, then restrict to B.
Source: Stacks Tag 0E23, displayed stalk comparison.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula). -/
def actualTargetModel (z' : Z') :
    CochainComplex (ModuleCat.{u} (SingleComplexBaseChange.A g z')) ℤ ⥤
      CochainComplex (ModuleCat.{u} (SingleComplexBaseChange.B i' z')) ℤ :=
  RingTensorCohomology.resolution (SingleComplexBaseChange.A g z') ⋙
    (ModuleCat.extendScalars.{u, u, u} (g.stalkMap z').hom).mapHomologicalComplex (.up ℤ) ⋙
    (ModuleCat.restrictScalars.{u} (i'.stalkMap z').hom).mapHomologicalComplex (.up ℤ)

/-- The canonical affine derived comparison, selected from its unique K-flat-span
characterization. Source: More on Algebra, equation comparison-map; Stacks Tag 0E23.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula). -/
def ringComparison (z' : Z') :
    sourceModel i i' f g sq z' ⋙
        @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
          (ModuleCat.{u} (SingleComplexBaseChange.B i' z'))) ⟶
      targetModel i i' f g sq z' ⋙
        @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
          (ModuleCat.{u} (SingleComplexBaseChange.B i' z'))) :=
  letI := SingleComplexBaseChange.leftAlgebra i g z'
  letI := SingleComplexBaseChange.rightAlgebra i i' f g sq z'
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B i' z'))
  Classical.choose (RingTensorCohomology.exists_affineDerivedBaseChangeComparison
    (SingleComplexBaseChange.R i g z') (SingleComplexBaseChange.A g z')
    (SingleComplexBaseChange.B i' z')).2

/-- The original ordinary Zariski stalk applied degreewise. Source: Stacks Tag 0E23.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula). -/
abbrev stalkModel (z' : Z') :=
  (RingedSpace.moduleStalkFunctor Z.toRingedSpace (g z')).mapHomologicalComplex (.up ℤ)

/-- The canonical map A tensor_R B -> C for this square. Source: Stacks Tag 0E23,
proof, and Tag 01JQ. This is the existing tensorMap, without new ring-map choices.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula). -/
abbrev tensorMap (z' : Z') := SingleComplexBaseChange.tensorMap i i' f g sq z'

/-- Stalks of the specified derived exchange mate for a closed immersion.
Source: Stacks Project, perfect.tex, Tag 0E23, proof before Tor independence.
(blueprint: lem-sfb-closed-immersion-derived-exchange-stalk-formula).

Proof:
1. On affine neighbourhoods a closed immersion is a quotient. Its base change is
   the corresponding quotient of the new base. Localizing gives A = R/I and
   C = B/IB, so the existing tensorMap is bijective (closed-ideal base-change
   diagram and affine-open/spec-map stalk-localization lemmas).
2. Closed-pushforward stalks are scalar restrictions on the image and zero off it.
   Restriction is exact, hence both closed pushforwards are exact by module-stalk
   exactness. Their derived functors are therefore computed termwise.
3. Choose flat-term K-flat models P for K and E -> i_*P. The derived pullbacks
   are f^*E and g^*P. Tensor-pullback composition, the absolute derived universal
   properties and the derived-adjunction counit formula show that the ordinary
   mate f^*E -> i'_*g^*P represents precisely schemeDerivedBaseChangeMap.
4. Exact stalks and the K-flat stalk criterion identify the source with the
   R-derived tensor of P_z and the target with its A-derived tensor with C.
   Ordinary base-tensor associativity and the quotient-ring isomorphism give
   the complex isomorphism d; its pure-tensor formula fixes the transport.
5. On stalks the mate sends e tensor b to s(e) tensor image(b). This is the
   K-flat-span characterization of ringComparison. Thus the displayed square
   commutes in D(B), before applying any cohomology. Naturality of all germ maps,
   units and localization comparisons gives the two natural isomorphisms.
6. Off the new closed image, the original closed-pushforward stalk is zero.
   Its K-flat resolution has acyclic stalk, so its derived tensor is zero.
   The target closed-pushforward stalk is already the zero complex.
No Tor independence, boundedness or quasi-coherence enters these steps. -/
theorem derived_exchange_stalk_formula [IsClosedImmersion i] :
    (∀ z' : Z', Function.Bijective (tensorMap i i' f g sq z') ∧
      ∃ (d : targetModel i i' f g sq z' ≅ actualTargetModel i' g z')
        (s : DerivedCategory.Q ⋙ schemeDerivedDirectImage i ⋙ derivedPullback f ⋙
            SingleComplexBaseChange.comparisonDerivedStalk X' (i' z') ≅
          stalkModel g z' ⋙ sourceModel i i' f g sq z' ⋙
            @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
              (ModuleCat.{u} (SingleComplexBaseChange.B i' z'))))
        (t : DerivedCategory.Q ⋙ derivedPullback g ⋙ schemeDerivedDirectImage i' ⋙
            SingleComplexBaseChange.comparisonDerivedStalk X' (i' z') ≅
          stalkModel g z' ⋙ actualTargetModel i' g z' ⋙
            @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
              (ModuleCat.{u} (SingleComplexBaseChange.B i' z')))),
        (∀ (M : CochainComplex (ModuleCat.{u} (SingleComplexBaseChange.A g z')) ℤ)
          (n : ℤ) (b : SingleComplexBaseChange.B i' z')
          (p : ((RingTensorCohomology.resolution (SingleComplexBaseChange.A g z')).obj M).X n),
          (d.hom.app M).f n (b ⊗ₜ[SingleComplexBaseChange.R i g z', baseMap i i' f g sq z'] p) =
            ((i'.stalkMap z').hom b ⊗ₜ[SingleComplexBaseChange.A g z', (g.stalkMap z').hom] p)) ∧
        ∀ M : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ,
          s.hom.app M ≫ (ringComparison i i' f g sq z').app ((stalkModel g z').obj M) ≫
              (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
                (ModuleCat.{u} (SingleComplexBaseChange.B i' z')))).map
                  (d.hom.app ((stalkModel g z').obj M)) =
            (SingleComplexBaseChange.comparisonDerivedStalk X' (i' z')).map
              (schemeDerivedBaseChangeMap i i' f g sq.w (DerivedCategory.Q.obj M)) ≫
                t.hom.app M) ∧
    ∀ (x' : X'), x' ∉ Set.range i' → ∀ K : schemeDerivedCategory Z,
      IsZero ((SingleComplexBaseChange.comparisonDerivedStalk X' x').obj
        ((derivedPullback f).obj ((schemeDerivedDirectImage i).obj K))) ∧
      IsZero ((SingleComplexBaseChange.comparisonDerivedStalk X' x').obj
        ((schemeDerivedDirectImage i').obj ((derivedPullback g).obj K))) := by
  sorry

end AlgebraicGeometry.ClosedImmersionExchange
