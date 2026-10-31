/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.ReducedClosedSubspaceSupport
import WeilConjectures.AlgebraicGeometry.AtlasEtaleRestriction
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The elementary étale square sequence of module endofunctors

Source: Stacks Project, Spaces and Modules, Tags 08GV(1), 08GN(2), and
Modules on Sites, Tags 03DI--03DJ
(blueprint: lem-sfb-space-elementary-shriek-exact).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- Étale module restriction has a left adjoint, determined by its Hom universal property.
Source: Stacks 03DI, 03DJ (blueprint: lem-sfb-space-elementary-shriek-exact).
Proof: identify the enlarged site over the étale object with the localized ringed site
using lem-trf-space-enlarged-etale-ringed-site-model. Apply
lem-pur-site-restriction-module-adjunction-exact: form the direct sum over lifts to the
object and apply module sheafification. Its Hom correspondence evaluates on each summand,
so its counit is evaluation. Transport across the normalized module restriction
equivalences. Representability makes the set of lifts from each scheme chart small:
it is a set of sections of a scheme over that chart. Thus this adjunction exists in the
original module universe, including for non-quasi-compact, non-separated étale maps. -/
theorem etaleModuleRestriction_isRightAdjoint (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    (pullback j hj).IsRightAdjoint := by
  sorry

/-- The extension by zero characterized by the localized direct-sum Hom correspondence.
Selection uses the adjoint universal property, which determines the object up to the
unique adjunction-compatible isomorphism, as allowed by AGENTS.md §5.
Source: Stacks 03DI (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def etaleModuleShriek (j : Z ⟶ X) (hj : IsEtale j.hom.hom) : Z.Modules ⥤ X.Modules :=
  @Functor.leftAdjoint _ _ _ _ (pullback j hj) (etaleModuleRestriction_isRightAdjoint j hj)

/-- The adjunction of the specified extension by zero and literal étale restriction.
Source: Stacks 03DI (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def etaleModuleShriekAdjunction (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    etaleModuleShriek j hj ⊣ pullback j hj :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (pullback j hj)
    (etaleModuleRestriction_isRightAdjoint j hj)

/-- The endofunctor `j_! j^*` on the actual small étale module category.
Source: Stacks 08GV(1) (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def etaleModuleSum (j : Z ⟶ X) (hj : IsEtale j.hom.hom) : X.Modules ⥤ X.Modules :=
  pullback j hj ⋙ etaleModuleShriek j hj

/-- Evaluation is the adjunction counit, hence sums all lift components.
Source: Stacks 03DI, 08GV(1) (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def etaleModuleSumCounit (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    etaleModuleSum j hj ⟶ 𝟭 X.Modules :=
  (etaleModuleShriekAdjunction j hj).counit

/-- Iterated literal restriction agrees with restriction along the composite.
Source: Stacks 03LP, 03DI (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def etaleModuleRestrictionComp (k : Z ⟶ Y) (j : Y ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :
    pullback j hj ⋙ pullback k hk ≅
      pullback (k ≫ j) (isEtale_comp k.hom.hom j.hom.hom hk hj) :=
  NatIso.ofComponents (fun F ↦
    (SheafOfModules.fullyFaithfulForget Z.structureSheaf).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)))
    (by intros; ext; rfl)

/-- The overlap-to-slice map: transpose the pulled-back unit, then evaluate.
This is the counit for the further restriction, under composition of left adjoints.
Source: Stacks 03DI, 08GV(1) (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def etaleModuleSumMap (k : Z ⟶ Y) (j : Y ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :
    etaleModuleSum (k ≫ j) (isEtale_comp k.hom.hom j.hom.hom hk hj) ⟶
      etaleModuleSum j hj :=
  ((Adjunction.whiskerRight X.Modules (etaleModuleShriekAdjunction (k ≫ j)
      (isEtale_comp k.hom.hom j.hom.hom hk hj))).homEquiv _ _).symm
    ((etaleModuleRestrictionComp k j hk hj).inv ≫
      whiskerRight (whiskerLeft (pullback j hj)
        (etaleModuleShriekAdjunction j hj).unit) (pullback k hk) ≫
      (isoWhiskerRight (Functor.associator (pullback j hj)
        (etaleModuleShriek j hj) (pullback j hj)).symm (pullback k hk)).hom ≫
      (Functor.associator (etaleModuleSum j hj) (pullback j hj) (pullback k hk)).hom ≫
      whiskerLeft (etaleModuleSum j hj) (etaleModuleRestrictionComp k j hk hj).hom)

/-- Binary sums inherited from the existing sectionwise products of module sheaves.
Source: Stacks 03DA (blueprint: lem-sfb-space-elementary-shriek-exact). -/
instance etaleModules_binaryBiproducts (W : AlgebraicSpace S) :
    HasBinaryBiproducts W.Modules :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Binary sums of module endofunctors, computed pointwise.
Source: Stacks 08GV(1) (blueprint: lem-sfb-space-elementary-shriek-exact). -/
instance etaleModuleEndofunctors_binaryBiproducts (W : AlgebraicSpace S) :
    HasBinaryBiproducts (W.Modules ⥤ W.Modules) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Transport of the canonical sum endofunctor along equality of its structure arrow.
Source: Stacks 03DI (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def etaleModuleSumCongr (j j' : Z ⟶ X)
    (hj : IsEtale j.hom.hom) (hj' : IsEtale j'.hom.hom) (e : j = j') :
    etaleModuleSum j hj ≅ etaleModuleSum j' hj' :=
  e ▸ Iso.refl (etaleModuleSum j hj)

/-- The overlap map for a commuting triangle, with the specified composite identified.
Source: Stacks 03DI, 08GV(1) (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def etaleModuleSumMapOver (k : Z ⟶ Y) (j : Y ⟶ X) (t : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) (ht : IsEtale t.hom.hom)
    (e : k ≫ j = t) : etaleModuleSum t ht ⟶ etaleModuleSum j hj :=
  (etaleModuleSumCongr (k ≫ j) t
    (isEtale_comp k.hom.hom j.hom.hom hk hj) ht e).inv ≫ etaleModuleSumMap k j hk hj

/-- The first differential has the negative sign in its V-component.
Source: Stacks 08GV(1) (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def elementaryEtaleSumDifferential {U V T : AlgebraicSpace S}
    (jU : U ⟶ X) (jV : V ⟶ X) (jT : T ⟶ X) (a : T ⟶ U) (b : T ⟶ V)
    (hU : IsEtale jU.hom.hom) (hV : IsEtale jV.hom.hom) (hT : IsEtale jT.hom.hom)
    (ha : IsEtale a.hom.hom) (hb : IsEtale b.hom.hom)
    (ea : a ≫ jU = jT) (eb : b ≫ jV = jT) :
    etaleModuleSum jT hT ⟶ etaleModuleSum jU hU ⊞ etaleModuleSum jV hV :=
  biprod.lift (etaleModuleSumMapOver a jU jT ha hU hT ea)
    (-etaleModuleSumMapOver b jV jT hb hV hT eb)

/-- The second differential adds the two evaluation counits.
Source: Stacks 08GV(1) (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def elementaryEtaleSumEvaluation {U V : AlgebraicSpace S} (jU : U ⟶ X) (jV : V ⟶ X)
    (hU : IsEtale jU.hom.hom) (hV : IsEtale jV.hom.hom) :
    etaleModuleSum jU hU ⊞ etaleModuleSum jV hV ⟶ 𝟭 X.Modules :=
  biprod.desc (etaleModuleSumCounit jU hU) (etaleModuleSumCounit jV hV)

/-- Exactness and additivity of restriction, extension, and their composite.
Source: Stacks 03DI--03DJ (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def EtaleModuleSumExact (j : Z ⟶ X) (hj : IsEtale j.hom.hom) : Prop :=
  (pullback j hj).Additive ∧ PreservesFiniteLimits (pullback j hj) ∧
  PreservesFiniteColimits (pullback j hj) ∧
  (etaleModuleShriek j hj).Additive ∧ PreservesFiniteLimits (etaleModuleShriek j hj) ∧
  PreservesFiniteColimits (etaleModuleShriek j hj) ∧
  (etaleModuleSum j hj).Additive ∧ PreservesFiniteLimits (etaleModuleSum j hj) ∧
  PreservesFiniteColimits (etaleModuleSum j hj)

/-- The specified natural short exact sequence for every presentation of the overlap.
All étaleness witnesses are conclusions, rather than extra geometric assumptions.
Source: Stacks 08GV(1) (blueprint: lem-sfb-space-elementary-shriek-exact). -/
def ElementaryEtaleSumExact {U V : AlgebraicSpace S}
    (jU : U ⟶ X) (jV : V ⟶ X) (hV : IsEtale jV.hom.hom) : Prop :=
  ∀ (T : AlgebraicSpace S) (a : T ⟶ U) (b : T ⟶ V) (sq : IsPullback a b jU jV),
    ∃ (hU : IsEtale jU.hom.hom) (ha : IsEtale a.hom.hom) (hb : IsEtale b.hom.hom),
      EtaleModuleSumExact jU hU ∧ EtaleModuleSumExact jV hV ∧
      EtaleModuleSumExact (a ≫ jU) (isEtale_comp a.hom.hom jU.hom.hom ha hU) ∧
      (etaleModuleSum jU hU ⊞ etaleModuleSum jV hV).Additive ∧
      PreservesFiniteLimits (etaleModuleSum jU hU ⊞ etaleModuleSum jV hV) ∧
      PreservesFiniteColimits (etaleModuleSum jU hU ⊞ etaleModuleSum jV hV) ∧
      ∃ hz : elementaryEtaleSumDifferential jU jV (a ≫ jU) a b hU hV
          (isEtale_comp a.hom.hom jU.hom.hom ha hU) ha hb rfl sq.w.symm ≫
            elementaryEtaleSumEvaluation jU jV hU hV = 0,
        (ShortComplex.mk
          (elementaryEtaleSumDifferential jU jV (a ≫ jU) a b hU hV
            (isEtale_comp a.hom.hom jU.hom.hom ha hU) ha hb rfl sq.w.symm)
          (elementaryEtaleSumEvaluation jU jV hU hV) hz).ShortExact

/-- The elementary-square sequence of exact additive étale sum endofunctors, stable
under every base change, with the reduced complement formed on the new space.
Source: Stacks 08GV(1), 08GN(2), 03DI--03DJ
(blueprint: lem-sfb-space-elementary-shriek-exact).
Proof:
1. Work on the enlarged ringed site using
   lem-trf-space-enlarged-etale-ringed-site-model. Its localization equivalence and
   lem-pur-site-restriction-module-adjunction-exact give exact restriction and exact
   additive direct-sum extension. Finite sums of exact additive functors are exact.
2. In the direct-sum presheaves (def-weil-extension-by-zero-presheaf), reindex the
   overlap summand by its two projections, taking the negative in the V component.
   Evaluation sums components. Module sheafification
   (def-weil-presheaf-modules-sheafification) gives the displayed natural maps.
   Their adjunction characterization identifies them with the definitions above.
   Both evaluation composites agree on every summand, so the differential squares to zero.
3. At a geometric point, lem-sfb-space-etale-sum-stalks identifies this with
   0 -> directSum(A times B,M) -> directSum(A,M) plus directSum(B,M) -> M -> 0.
   Fibre products identify the overlap lift set with A times B
   (lem-trf-space-fibre-products-etale-covers). All sums have finite support.
4. The open fibre A is empty or singleton. In the singleton case the maps are
   c |-> (sum c,-c) and (a,c) |-> a+sum c: the second component proves injectivity,
   (m,0) proves surjectivity, and a+sum c=0 gives (a,c)=d(-c).
   If A is empty, the point factors through the reduced closed complement:
   a closed subscheme with nonempty support in the spectrum of a field is the spectrum.
   The isomorphism over the complement makes B singleton; the sequence is
   0 -> 0 -> M -> M -> 0. This uses lem-sfb-space-reduced-closed-support.
5. Geometric stalks detect exactness by lem-sfb-space-etale-conservative-geometric-points
   and lem-weil-pbc-module-sheaves-colimits-forgetful, proving natural short exactness.
6. After arbitrary base change, open immersions and étale maps persist
   (lem-trf-space-chartwise-etale-permanence). Geometric lifts are those at the image
   point, so steps 3--5 apply verbatim with any module on the new space. Construct its
   reduced complement by lem-sfb-space-reduced-closed-support. It need not equal the
   pullback of the old reduced complement. No exactness of base-change pullback,
   flatness, quasi-compactness, separation, or finiteness of the étale fibres is used. -/
theorem elementary_etale_shriek_exact {U V : AlgebraicSpace S}
    (jU : U ⟶ X) (jV : V ⟶ X)
    (hU : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) jU.hom.hom)
    (hV : IsEtale jV.hom.hom) (E : ClosedSubspace X)
    (hE : IsReduced (E.val : AlgebraicSpace S))
    (hSupport : pointImage E.val.arrow.hom.hom = (pointImage jU.hom.hom)ᶜ)
    (hIso : IsIso (Limits.pullback.snd jV.hom E.val.arrow.hom)) :
    ElementaryEtaleSumExact jU jV hV ∧
      ∀ (X₁ U₁ V₁ : AlgebraicSpace S) (h : X₁ ⟶ X)
        (jU₁ : U₁ ⟶ X₁) (jV₁ : V₁ ⟶ X₁) (pU : U₁ ⟶ U) (pV : V₁ ⟶ V),
        IsPullback pU jU₁ jU h → IsPullback pV jV₁ jV h →
        ∃ hV₁ : IsEtale jV₁.hom.hom,
          ElementaryEtaleSumExact jU₁ jV₁ hV₁ ∧
          ∃ E₁ : ClosedSubspace X₁, IsReduced (E₁.val : AlgebraicSpace S) ∧
            pointImage E₁.val.arrow.hom.hom = (pointImage jU₁.hom.hom)ᶜ ∧
            IsIso (Limits.pullback.snd jV₁.hom E₁.val.arrow.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
