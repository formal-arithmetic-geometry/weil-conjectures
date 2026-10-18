/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Exact pullback of finite constant pro-etale left modules

Source: Weil conjectures blueprint, order 1236; Stacks Project, Tags 00WJ, 03D2, and 04JC
(blueprint: prop-weil-pbc-proetale-constant-exact).

The coefficient categories are the recorded continuous-function ringed module categories.
The small-model module Kan extension gives inverse image over the inverse-image ring;
restriction along the inverse of the canonical coefficient map transports the action.
The commutative comparison uses the recorded tensor pullback, with the canonical
constant-preserving coefficient identifications written explicitly.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
  [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Register the recorded coefficient isomorphism, without choosing any new map.
Source: blueprint order 1235 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable instance finiteCoefficientInverseImageMap_invertible :
    IsIso (finiteCoefficientInverseImageMap f Λ) :=
  finiteCoefficientInverseImageMap_isIso f Λ

/-- The inverse-image coefficient ring on the original small site.
Source: Stacks Tag 03D2 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable abbrev finiteCoefficientInverseRing :=
  (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).obj (finiteCoefficientRingSheaf V Λ)

/-- The ring adjunction unit on the small site models. Only the Hom universe is enlarged.
Source: Stacks Tags 00YV and 03D2 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable def finiteCoefficientModelRingUnit :
    ((AsSmall.down : Scheme.proEtaleSiteModel V ⥤ V.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.proEtaleModelTopology V) (Scheme.ProEt.topology V)).obj
        (finiteCoefficientRingSheaf V Λ) ⟶
    ((Scheme.proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.proEtaleModelTopology V) (Scheme.proEtaleModelTopology U)).obj
        (((AsSmall.down : Scheme.proEtaleSiteModel U ⥤ U.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (Scheme.proEtaleModelTopology U) (Scheme.ProEt.topology U)).obj
            (finiteCoefficientInverseRing f Λ)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app
      (finiteCoefficientRingSheaf V Λ)).hom)⟩

/-- Inverse image of left modules over the inverse-image ring. Mathlib's module pullback
is the module Kan extension followed by sheafification, along the actual ring unit.
Its action is the inverse image of the original action under the product comparison.
Transport to and from the equivalent small model retains every original site object.
Source: Stacks Tag 03D2 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable def finiteCoefficientModuleInverseImage :
    FiniteCoefficientModules V Λ ⥤ SheafOfModules.{u + 1} (finiteCoefficientInverseRing f Λ) :=
  Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf V Λ) ⋙
    SheafOfModules.pullback (finiteCoefficientModelRingUnit f Λ) ⋙
    Scheme.proEtaleModuleFromModel (finiteCoefficientInverseRing f Λ)

/-- The specified pullback: transport the inverse-image action by c_f inverse.
Thus r acts as c_f inverse(r), and on underlying abelian maps the functor is inverse image.
No tensor product or multiplicative commutativity is required here.
Source: blueprint order 1236; Stacks Tag 03D2
(blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable def finiteCoefficientModulePullback :
    FiniteCoefficientModules V Λ ⥤ FiniteCoefficientModules U Λ :=
  finiteCoefficientModuleInverseImage f Λ ⋙
    SheafOfModules.restrictScalars (inv (finiteCoefficientInverseImageMap f Λ))

/-- Additivity needed to map short complexes by the specified pullback.
Source: blueprint order 1236; Stacks Tags 03D2 and 04JC
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof: inverse image carries addition of abelian maps to addition, by preservation of
products and the addition operation. The module Kan extension is the same lifted inverse
image by its universal property. Restriction along c_f inverse changes only scalar actions,
so preserves this equality on maps. No commutativity of the ring is used. -/
theorem finiteCoefficientModulePullback_additive :
    (finiteCoefficientModulePullback f Λ).Additive := by
  sorry

attribute [instance] finiteCoefficientModulePullback_additive

/-- The specified pullback preserves kernels, cokernels and all short exact sequences.
Finite-limit and finite-colimit preservation encode the two exactness clauses in these
abelian categories; the final clause explicitly records short exact sequences.
Source: blueprint order 1236; Stacks Tags 04JC and 03DA
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof:
1. The arbitrary scheme map gives a morphism of small pro-etale sites, by
   def-weil-proetale-inverse-image. Apply lem-weil-pbc-site-pullback-abelian-exact
   after transporting to the equivalent small models of def-weil-pbc-proetale-site.
   Its abelian inverse image preserves kernels, cokernels and short exact sequences.
2. Finite-product preservation transports the ring multiplication and the left module
   action, together with all unit, associativity and distributivity identities.
   Naturality transports the linearity identities. This is the module Kan extension
   along the ring unit by its universal property. The canonical coefficient map of
   prop-weil-pbc-proetale-constant-ring-map is invertible; restrict the action along
   its inverse. Commutativity is unnecessary. The commutative tensor identification
   is stated separately below, using def-weil-pbc-proetale-operations.
3. By def-weil-sheaf-of-modules-category, module kernels and cokernels have the
   corresponding underlying abelian sheaves. The abelian comparison isomorphisms
   from step 1 are linear by their inclusions and quotient maps; their inverses are
   linear as inverses of bijective linear maps. Scalar transport leaves underlying
   abelian groups and maps unchanged. Thus kernels, cokernels and short exact
   sequences are preserved. In additive categories finite products are biproducts;
   kernel and cokernel preservation therefore give the two finite-preservation clauses. -/
theorem finiteCoefficientModulePullback_exact :
    PreservesFiniteLimits (finiteCoefficientModulePullback f Λ) ∧
    PreservesFiniteColimits (finiteCoefficientModulePullback f Λ) ∧
    ∀ S : ShortComplex (FiniteCoefficientModules V Λ),
      S.ShortExact → (S.map (finiteCoefficientModulePullback f Λ)).ShortExact := by
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
  [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- The canonical commutative constant coefficient presentation for the tensor comparison.
Source: blueprint order 1236 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable abbrev finiteCoefficientCommRing (T : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- Compatibility of the commutative presentation with ring sheafification.
This supplies the construction obligation of the canonical coefficient comparison below.
Source: Stacks Tags 00W1 and 00YV; blueprint order 1236
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof: sheafification is the double-plus construction, formed from matching-family
limits and filtered colimits of covers. Forgetting commutativity preserves these
limits and filtered colimits and reflects isomorphisms. It therefore carries each
plus construction, its unit, and the resulting sheafification equivalences to their
ring-valued counterparts. This changes no ring data or constant sections. -/
theorem finiteCoefficientCommRing_preservesSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  sorry

attribute [instance] finiteCoefficientCommRing_preservesSheafification

/-- The canonical constant-preserving comparison from the commutative presentation.
Source: blueprint order 1236; Stacks Tag 0H7J
(blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable def finiteCoefficientCommRingComparison (T : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (finiteCoefficientCommRing Λ T) ⟶ finiteCoefficientRingSheaf T Λ :=
  (constantCommuteCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of Λ) ≫
      finiteCoefficientConstantComparison Λ T

/-- The canonical commutative coefficient map is invertible too.
Source: blueprint order 1236; Stacks Tags 0H7J and 09A5
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof: inverse image of the constant sheaf is constant, by the ring-sheaf adjunction
and the constant-preserving identifications of prop-weil-pbc-proetale-constant-ring-map.
Forgetting commutativity commutes with the inverse-image construction, since that
construction lifts the finite-product-preserving set inverse image. The resulting ring
map is the canonical invertible map of that proposition. The forgetful functor reflects
isomorphisms, so the commutative map is invertible. -/
theorem finiteCoefficientCommRingMap_isIso :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ)) := by
  sorry

attribute [instance] finiteCoefficientCommRingMap_isIso

/-- The commutative tensor pullback is naturally isomorphic to the specified transport
pullback under the canonical constant-preserving coefficient identifications.
Source: blueprint order 1236; Stacks Tag 03D2 and tensor cancellation along an isomorphism
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof: the coefficient comparisons preserve constants and carry the canonical structure
map to the canonical commutative one, by prop-weil-pbc-proetale-constant-ring-map.
For a module M, the map from tensor pullback to transported inverse image sends
r tensor m to c inverse(r)m; its inverse sends m to 1 tensor m. The balancing relation
makes both composites identities. These maps commute with restrictions and module
morphisms, so extend by sheafification and give inverse natural transformations.
The coefficient comparisons are isomorphisms: constantCommuteCompose is an isomorphism,
and finiteCoefficientConstantComparison_isIso identifies constants with the prescribed
continuous-function sheaf. Thus both sides compare precisely the original module
categories through restriction of scalars, without changing the coefficient objects. -/
theorem finiteCoefficientModulePullback_tensor :
    Nonempty
      (finiteCoefficientModulePullback f Λ ⋙
          SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison Λ U) ≅
        SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison Λ V) ⋙
          Scheme.proEtaleRingModulePullback f
            (finiteCoefficientCommRing Λ V) (finiteCoefficientCommRing Λ U)
            (asIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
              (CommRingCat.of Λ)))) := by
  sorry

end AlgebraicGeometry.ProEtale
