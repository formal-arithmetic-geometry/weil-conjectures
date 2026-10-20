/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.Paper.DualityPairing
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.Algebra.Homology.RhomGlobalSections
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition
import Sheaf.SixFunctors.TensorProjectionAdjunct
import Sheaf.SmoothPurity.InternalAdjunctionEvaluation

/-! # The double-dual morphism under proper direct image

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2123 (blueprint: lem-weil-delta-proper-pushforward).

All constructions use ordinary unbounded etale module derived categories. Evaluation and
its transpose are normalized by tensor-Hom adjunction. The trace uses the mate of the
compactification composition comparison, and the exchange is the transpose of the
pushed-forward evaluation pairing.

## Main definitions and statement

* `ambientDualEvaluation` and `ambientDoubleDualMap`: signed evaluation and its transpose.
* `properAmbientShriekStarIso` and `ambientShriekCompIso`: canonical support comparisons.
* `properAmbientDualizingIso` and `properAmbientDualityTrace`: the adjoint mate and trace.
* `ambientDirectImageProduct`: direct-image product from projection and the counit.
* `properAmbientVerdierExchangeMap`: the transpose of evaluation followed by trace.
* `ProperAmbientDoubleDualCompatibility`: the natural exchange and double-dual square.
* `proper_ambient_double_dual_compatibility`: the proper pushforward assertion.
-/

@[expose] public section

set_option autoImplicit false

universe a u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Evaluation

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (X : Scheme.{u})

/-- The evaluation pairing in the order DK tensor K. Source: blueprint order 2123,
second proof paragraph (blueprint: lem-weil-delta-proper-pushforward).
This is the evaluation of lem-weil-duality-pairing: signed symmetry followed by the
inverse tensor-Hom transpose of the identity, so its normalization is fixed. -/
noncomputable def ambientDualEvaluation
    (W K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (((derivedHom A X).obj (op K)).obj W)).obj K ⟶ W :=
  ((derivedTensorSymmetry A X).hom.app (((derivedHom A X).obj (op K)).obj W)).app K ≫
    ((derivedTensorHomAdjunction A K).homEquiv _ _).symm (𝟙 _)

/-- The canonical double-dual arrow, the transpose of evaluation in the preceding order.
Source: blueprint order 2123, third proof paragraph
(blueprint: lem-weil-delta-proper-pushforward). This fixes the Koszul signs by the existing
signed symmetry, and applies to every ambient object W and every unbounded K. -/
noncomputable def ambientDoubleDualMap
    (W K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ (dualityDoubleFunctor (derivedHom A X) W).obj K :=
  (derivedTensorHomAdjunction A (((derivedHom A X).obj (op K)).obj W)).homEquiv K W
    (ambientDualEvaluation A X W K)

end Evaluation

/-- The canonical proper identification with direct image, through the identity
compactification and the proper/open comparison. Source: blueprint order 2123, first
proof paragraph (blueprint: lem-weil-delta-proper-pushforward).
No isomorphism is selected from a mere existence assertion. -/
noncomputable def properAmbientShriekStarIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ≅
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor := by
  let c := Compactification.ofIsProper f
  letI := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) c.i (c.isClopen_range_openImmersion inferInstance).isClosed
  let e := asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) c.i)
  letI : PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} Λ) c.i) :=
    preservesFiniteColimits_of_natIso e
  letI : PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} Λ) c.i) :=
    preservesFiniteLimits_of_natIso e
  exact (rightDerivedLowerShriekIso Λ c).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) _ ≪≫
    Functor.isoWhiskerRight
      ((lowerStar (ModuleCat.{u + 1} Λ) c.i).rightDerivedFunctorIsoMapDerivedCategory).symm _ ≪≫
    rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) c.i c.g ≪≫
    rightDerivedLowerStarCongr (ModuleCat.{u + 1} Λ) c.comm.symm

/-- The unbounded compact-support composition comparison, assembled from the existing
proper/open exchange and the canonical compactification comparisons.
Source: blueprint order 2123, first proof paragraph; Stacks 0F7H--0F7J
(blueprint: lem-weil-delta-proper-pushforward). This is the explicit construction underlying
nonempty_iso_rightDerivedLowerShriek_comp, with no choice from that theorem. -/
noncomputable def ambientShriekCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g := by
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  exact (rightDerivedLowerShriekIso Λ (d.comp e)).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationCompIso Λ d e).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ e.restrict) _

/-- The canonical identification f-times omega-Y with omega-X, the right-adjoint mate of
compact-support composition after proper coincidence. Source: blueprint order 2123,
first proof paragraph (blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def properAmbientDualizingIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) g) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) :=
  (conjugateIsoEquiv
    (((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).ofNatIsoLeft
      (properAmbientShriekStarIso Λ f)).comp
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) g))
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (f ≫ g))
    (ambientShriekCompIso Λ f g ≪≫
      Functor.isoWhiskerRight (properAmbientShriekStarIso Λ f)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g))).app (𝟙_ _)

/-- The trace F omega-X to omega-Y, transported from the exceptional counit by the
preceding canonical mate. Source: blueprint order 2123, first proof paragraph
(blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def properAmbientDualityTrace
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) ⟶
      dualizingComplex (ModuleCat.{u + 1} Λ) g :=
  (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
      (properAmbientDualizingIso Λ f g).inv ≫
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).ofNatIsoLeft
      (properAmbientShriekStarIso Λ f)).counit.app
        (dualizingComplex (ModuleCat.{u + 1} Λ) g)

section Product

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The symmetric product map FU tensor FV to F(U tensor V), using the ordinary
inverse-image/direct-image counit. Source: blueprint order 2123, second proof paragraph
(blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def ambientDirectImageProduct
    (U V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A Y).obj ((lowerStar A f).rightDerivedFunctor.obj U)).obj
        ((lowerStar A f).rightDerivedFunctor.obj V) ⟶
      (lowerStar A f).rightDerivedFunctor.obj (((derivedTensor A X).obj U).obj V) :=
  ((rightDerivedLowerStarProjectionMap A f).app U).app
      ((lowerStar A f).rightDerivedFunctor.obj V) ≫
    (lowerStar A f).rightDerivedFunctor.map
      ((derivedTensor A X).obj U |>.map ((derivedUpperStarLowerStarAdjunction A f).counit.app V))

end Product

/-- The ambient Verdier exchange, defined as the transpose of pushed-forward evaluation
followed by trace. Source: blueprint order 2123, second proof paragraph
(blueprint: lem-weil-delta-proper-pushforward). Its orientation is F DX to DY F. -/
noncomputable def properAmbientVerdierExchangeMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] (K : DerivedCategoryModule Λ X) :
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
        ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (op K)) ⟶
      (verdierDual (ModuleCat.{u + 1} Λ) g).obj
        (op ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
    ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)).homEquiv _ _
    (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)).app
        ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (op K))) ≫
      ambientDirectImageProduct (ModuleCat.{u + 1} Λ) f _ K ≫
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
        (ambientDualEvaluation (ModuleCat.{u + 1} Λ) X
          (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) K) ≫
      properAmbientDualityTrace Λ f g)

/-- Proper direct image carries the canonical double-dual arrow to the canonical
one under its ambient exchange. Source: blueprint order 2123, final displayed comparison
(blueprint: lem-weil-delta-proper-pushforward).
The middle equality is the comparison square before inverting either exchange map;
its two sides have target DY(F(DX K)). Thus it states the double-dual comparison
without assuming either double-dual arrow invertible. -/
def ProperAmbientDoubleDualCompatibility
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] : Prop :=
  (∀ (K L : DerivedCategoryModule Λ X) (h : K ⟶ L),
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
        ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).map h.op) ≫
        properAmbientVerdierExchangeMap Λ f g K =
      properAmbientVerdierExchangeMap Λ f g L ≫
        (verdierDual (ModuleCat.{u + 1} Λ) g).map
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map h).op) ∧
  (∀ K : DerivedCategoryModule Λ X, IsIso (properAmbientVerdierExchangeMap Λ f g K)) ∧
  (∀ K : DerivedCategoryModule Λ X,
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
        (ambientDoubleDualMap (ModuleCat.{u + 1} Λ) X
          (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) K) ≫
        properAmbientVerdierExchangeMap Λ f g
          ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (op K)) =
      ambientDoubleDualMap (ModuleCat.{u + 1} Λ) Y
          (dualizingComplex (ModuleCat.{u + 1} Λ) g)
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K) ≫
        (verdierDual (ModuleCat.{u + 1} Λ) g).map
          (properAmbientVerdierExchangeMap Λ f g K).op) ∧
  (∀ K : DerivedCategoryModule Λ X,
    IsIso (ambientDoubleDualMap (ModuleCat.{u + 1} Λ) Y
      (dualizingComplex (ModuleCat.{u + 1} Λ) g)
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)) →
    IsIso ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
      (ambientDoubleDualMap (ModuleCat.{u + 1} Λ) X
        (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) K)))

/-- The canonical ambient exchange for proper direct image identifies the two double-dual
arrows on arbitrary complexes; invertibility of delta after direct image implies
invertibility of the direct image of delta. Source: blueprint order 2123
(blueprint: lem-weil-delta-proper-pushforward).

Proof:
1. A finite-type scheme over the field is Noetherian, by pqf-lem-locnoeth-lft and finite
   affine covers. The same holds for the proper parts of its compactifications. Use
   thm-amb-etale-exceptional-adjoint for the three ambient right adjoints. Use the
   unbounded proper/open compactification composition of
   lem-sf-unbounded-compact-support-proper-composition, not bounded-below composition.
2. Compose the adjunctions and take their canonical mate at the coefficient unit.
   This gives f-times omega-Y = omega-X and the transported counit t used above.
3. By lem-weil-pbc-ringed-internal-hom-exact-restriction and lem-pur-rhom-global-sections,
   tensor-Hom adjunction applies to arbitrary complexes. By lem-weil-duality-pairing,
   delta is the transpose of signed evaluation, with its double-evaluation equation.
4. Define mu by the ordinary inverse-image counit and def-kun-projection-formula-map.
   For a test Q, the chain of adjunctions and the invertible proper projection map of
   lem-amb-proper-coproducts-projection identifies Hom(Q,F DXK) with Hom(Q,DY FK).
   Tracing a test arrow through these bijections gives precisely the pairing
   t composed with F(e_K) composed with mu. Thus its transpose is the canonical
   exchange of prop-asd-internal-adjunction and is invertible.
5. Counit naturality and lem-kun-inverse-image-monoidal give naturality of mu.
   Transposing also proves mu composed with the signed symmetry equals the image
   of the signed symmetry composed with mu, using lem-kun-tensor-sym.
6. Transpose the two sides of the displayed square. By naturality of mu, the
   double-evaluation identity and symmetry, both are b_K composed with symmetry,
   where b_K = t F(e_K) mu. Tensor-Hom adjunction is injective, so the square commutes.
7. The two exchange maps are invertible independently of biduality. The contravariant
   DY preserves inverse pairs. Inverting DY(theta_K) identifies F DDXK with DDY FK,
   and the square says this identification carries F(delta_K) to delta_(FK).
   If the latter is invertible, so is F(delta_K). This does not assert that F reflects
   isomorphisms. No constructible exceptional-adjoint or geometric biduality is used.
-/
theorem proper_ambient_double_dual_compatibility
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    ProperAmbientDoubleDualCompatibility Λ f aY := by
  sorry

end AlgebraicGeometry.Etale
