/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Sheaf.AlgebraicGeometry.AlgebraicStackTotalEqualizers
import Sheaf.CategoryTheory.RingedSiteSliceExactShriek

/-! # Restriction to a test fibre preserves injective module sheaves

Source: Stacks Project, stacks-sheaves.tex, Tags 06TS, 06WY and 06X2
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives).

A test object over V is written as its associated map from the represented discrete
fibred category h_V. This retains the object and its automorphisms, by 2-Yoneda.
The Boolean parameter selects big etale (true) or big fppf (false) coverings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The two inherited topologies, with all objects and arrows retained.
Source: Stacks 06TP, 06TS
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives). -/
def moduliTestFibreTopology {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (etale : Bool) : GrothendieckTopology F.obj :=
  if etale then
    (AlgebraicGeometry.Scheme.etalePrecoverage.comap (moduliSchemeForget F)).toGrothendieck
  else moduliFppfTopology F

/-- The original regular-function presheaf is a sheaf for either inherited topology.
Source: Stacks 06TV and 06TS
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives).

Proof: for fppf use moduliStructurePresheaf_isSheaf from
 def-sfb-stack-quasi-coherent-algebra. An etale covering is an fppf covering; cartesian
lifts identify overlaps with scheme fibre products. Hence the same unique gluing
condition for regular functions applies to etale coverings as well. -/
theorem moduliTestFibreStructure_isSheaf {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (etale : Bool) :
    Presheaf.IsSheaf (moduliTestFibreTopology F etale) (moduliStructurePresheaf F) := by
  sorry

/-- The structure ring has exactly the recorded regular functions and pullback maps.
Source: Stacks 06TV
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives). -/
def moduliTestFibreModuleRings {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (etale : Bool) :=
  (sheafCompose (moduliTestFibreTopology F etale)
    (forget₂ CommRingCat.{max (u + 1) v w} RingCat.{max (u + 1) v w})).obj
    ⟨moduliStructurePresheaf F, moduliTestFibreStructure_isSheaf F hF etale⟩

/-- The actual 2-fibre product with the scheme test V, using the recorded construction.
Source: Stacks 06X2, specialization to a test fibre
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives). -/
abbrev moduliTestFibre {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {Y : BasedCategory.{v', w'} (Over S)}
    (h : BasedFunctor X Y) {V : Over S}
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) Y) :=
  moduliTwoFiberProduct h y

/-- Projection from the actual test fibre to X; it retains the underlying base scheme.
Source: Stacks 06TS, 06X2
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives). -/
abbrev moduliTestFibreProjection {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {Y : BasedCategory.{v', w'} (Over S)}
    (h : BasedFunctor X Y) {V : Over S}
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) Y) :=
  (moduliTwoFiberFst h y).toFunctor

/-- Precomposition along the test projection preserves sheaves in either topology.
Source: Stacks 06TS
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives).

Proof, step 1 of the node: cartesian lifting of the object, map to V and comparison
isomorphism makes the fibre product fibred in groupoids. The projection preserves
underlying schemes and covering families and their pullbacks. Apply
lem-sfb-fibred-site-functor-continuity to the chosen scheme topology. -/
theorem moduliTestFibreProjection_isContinuous
    {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {Y : BasedCategory.{v', w'} (Over S)}
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (h : BasedFunctor X Y) {V : Over S}
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) Y) (etale : Bool) :
    (moduliTestFibreProjection h y).IsContinuous
      (moduliTestFibreTopology (moduliTestFibre h y) etale)
      (moduliTestFibreTopology X etale) := by
  sorry

/-- The fibre's structure ring is literal precomposition: at a triple over T it is
Gamma(T,O_T), with its original restriction maps. Canonical ULift ring equivalences
identify the coefficient carriers with the original rings, just as in the recorded
moduliStructurePresheaf. No scalar extension is introduced.
Source: Stacks 06TV, 06TS
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives). -/
def moduliTestFibreRestrictedRings {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {Y : BasedCategory.{v', w'} (Over S)}
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (h : BasedFunctor X Y) {V : Over S}
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) Y) (etale : Bool) :=
  letI := moduliTestFibreProjection_isContinuous hX hY h y etale
  ((moduliTestFibreProjection h y).sheafPushforwardContinuous RingCat
    (moduliTestFibreTopology (moduliTestFibre h y) etale)
    (moduliTestFibreTopology X etale)).obj (moduliTestFibreModuleRings X hX etale)

/-- Literal module precomposition, with the identity structural ring homomorphism.
Its value at (x,T to V,alpha) is M(x), with M's scalar action and restriction maps.
Source: Stacks 06TS, 06X2
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives). -/
def moduliTestFibreRestriction {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {Y : BasedCategory.{v', w'} (Over S)}
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (h : BasedFunctor X Y) {V : Over S}
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) Y) (etale : Bool) :
    ringedSiteModules.{max (u + 1) v w v' w'} (moduliTestFibreModuleRings X hX etale) ⥤
      ringedSiteModules.{max (u + 1) v w v' w'}
        (moduliTestFibreRestrictedRings hX hY h y etale) :=
  letI := moduliTestFibreProjection_isContinuous hX hY h y etale
  SheafOfModules.pushforward (F := moduliTestFibreProjection h y) (𝟙 _)

/-- Restriction is additive and exact and preserves every injective module sheaf.
Source: Stacks 06X2, using 06TS and 06WY
(blueprint: lem-sfb-stack-test-fibre-restriction-injectives).

Proof:
1. The fibre product is fibred in groupoids and its projection is continuous and
   cocontinuous by lem-sfb-fibred-site-functor-continuity. The structure ring is literal
   precomposition. The exact additive restriction is therefore the displayed functor,
   by lem-trf-ringed-site-restriction-generator-data.
2. The projection is faithful: the arrow between the scheme tests is uniquely
   determined by its underlying scheme arrow. No faithfulness of h is required.
3. Cartesian lifts of scheme fibre products give pullbacks in the total categories
   by lem-sfb-cartesian-lift-pullback-square, and the projection preserves them.
4. Use lem-sfb-algebraic-stack-total-equalizers in X. An equalizer w to x lifts to the
   triple (w, the composite map to V, the pulled-back comparison isomorphism).
   Factorizations lift uniquely by their compatibility with that comparison; hence
   the fibre has equalizers and its projection preserves them.
5. By lem-sfb-fibred-test-object-ringed-localization both slices over a test triple
   and its image are equivalent to Sch/T. Their scheme projections commute strictly
   with the induced slice functor, which is thus an equivalence of ringed sites.
6. Apply lem-sfb-ringed-site-slice-equivalence-exact-shriek to get an exact additive
   left adjoint. It preserves monomorphisms. Adjunction.map_injective, the Mathlib
   match for lem-exc-rg-right-adjoint-preserves-injectives, now proves injective
   preservation. Exactness in these module categories is expressed by preservation
   of finite limits and finite colimits. No module quasi-coherence is used. -/
theorem moduliTestFibreRestriction_exact_preservesInjectives
    {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {Y : BasedCategory.{v', w'} (Over S)}
    (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (h : BasedFunctor X Y) {V : Over S}
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) Y) (etale : Bool) :
    (moduliTestFibreRestriction hX.1.1 hY.1.1 h y etale).Additive ∧
    PreservesFiniteLimits (moduliTestFibreRestriction hX.1.1 hY.1.1 h y etale) ∧
    PreservesFiniteColimits (moduliTestFibreRestriction hX.1.1 hY.1.1 h y etale) ∧
    (moduliTestFibreRestriction hX.1.1 hY.1.1 h y etale).PreservesInjectiveObjects := by
  sorry

end CategoryTheory
