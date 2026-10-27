module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import Sheaf.Paper.ModuleRingedToposDerivedComparison
public import Sheaf.Paper.CondensedOpenExceptionalProjectionFormula
public import Sheaf.Paper.BoundedConstructiblePushforwardRestriction
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.PoincareDuality.ProperProjectionFormulaBounded

/-! # The canonical compactification projection and its inverse

Source: blueprint main-20261015, `det-lem-int-tensor-projection.proof.md`,
Open immersions and Derived version, with the proper projection comparison
(blueprint: lem-pd-compactification-projection-inverse).

The isomorphisms below have specified forward and inverse arrows. Their existential
packaging supplies invertibility without assuming it as an extra hypothesis.
-/

@[expose] public noncomputable section

attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [IsEllAdicFinitenessCoefficient ℓ Λ]
  {f : X ⟶ Y} (c : Compactification f.left)

section Main

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

/-- The specified restricted composition comparison, oriented from the two pullbacks
into the pullback of `f`. Source: blueprint main-20261015, composition in the derived
projection formula (blueprint: lem-pd-compactification-projection-inverse). -/
def compactificationProjectionPullbackIso :
    boundedConstructibleUpperStar Λ ℓ c.overG ⋙
        boundedConstructibleUpperStar Λ ℓ c.overI ≅
      boundedConstructibleUpperStar Λ ℓ f :=
  (boundedConstructibleUpperStarComp Λ ℓ
    c.overI c.overG).symm ≪≫
      eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ)
        c.overI_overG)

/-- The proper and open canonical arrows are invertible; their specified composite has
precisely the displayed reverse composite as inverse and is natural in the second factor.
The witnesses `alpha`, `Q` and `P` are isomorphisms whose forward maps are fixed below;
no unspecified comparison arrow is substituted.

Source: blueprint main-20261015, `det-lem-int-tensor-projection.proof.md`,
Open immersions and Derived version
(blueprint: lem-pd-compactification-projection-inverse).

Proof: (1) Restrict the ambient functors, tensors and adjunctions by
sk-def-sfb-dc-restricted-functors. The proper and open normalization clauses below,
from lem-pd-module-ringed-topos-derived-comparison, identify the actual maps with
lem-weil-pbc-ringed-projection-mate-exact and the ringed open projection.
(2) Apply lem-pd-condensed-proper-projection-formula to the given compactification
and K,B, and lem-pd-condensed-open-exceptional-projection-formula to j,K,N.
This makes alpha and Q invertible in the full subcategories.
(3) Put s = Rq_*j_!(1 tensor a) and t = Rq_*Q. Functoriality gives
P = alpha followed by t inverse followed by s, and its inverse is s inverse
followed by t followed by alpha inverse. Cancel adjacent inverse factors in
both orders, using the inherited composition of sk-def-sfb-bounded-constructible.
(4) Naturality of the proper mate, the open projection, and
def-sfb-dc-upper-star-comp gives the three successive naturality squares;
paste them to obtain the displayed equality for every h.
(5) Unfold sk-def-sfb-dc-lower-shriek at the chosen compactification and the
ambient exceptionalProjectionMorphismOfCompactification. Its composition
comparison is the inverse of leftDerivedUpperStarCompactificationIso.
Full faithfulness identifies its restriction with the target component, as
stated in the final chosen-compactification clause. -/
def compactification_projection_inverseClauses
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X.left)) : Prop :=
    ∃ (alpha : ∀ B : ProEtale.BoundedConstructible
        (condensedRingObj Λ Y.left),
      (boundedConstructibleLowerShriekOfCompactification
          Λ ℓ c).obj K ⊗ B ≅
        (boundedConstructibleLowerStar Λ ℓ c.overG).obj
          ((boundedConstructibleOpenImmersionLowerShriek
              Λ ℓ c.overI).obj K ⊗
            (boundedConstructibleUpperStar Λ ℓ c.overG).obj B))
      (Q : ∀ N : ProEtale.BoundedConstructible
        (condensedRingObj Λ c.Z),
      (boundedConstructibleOpenImmersionLowerShriek
          Λ ℓ c.overI).obj
          (K ⊗ (boundedConstructibleUpperStar
            Λ ℓ c.overI).obj N) ≅
        (boundedConstructibleOpenImmersionLowerShriek
          Λ ℓ c.overI).obj K ⊗ N),
    (∀ B, (alpha B).hom =
      (boundedConstructibleUpperStarLowerStarAdjunction
        Λ ℓ c.overG).projectionMorphism
          ((boundedConstructibleOpenImmersionLowerShriek
            Λ ℓ c.overI).obj K) B) ∧
    (∀ N, (Q N).hom = (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      Λ ℓ c.overI).projectionComparison K N) ∧
    ∃ P : ∀ B : ProEtale.BoundedConstructible
        (condensedRingObj Λ Y.left),
      (boundedConstructibleLowerShriekOfCompactification
          Λ ℓ c).obj K ⊗ B ≅
        (boundedConstructibleLowerShriekOfCompactification
          Λ ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B),
    (∀ B, (P B).hom = (alpha B).hom ≫
      (boundedConstructibleLowerStar Λ ℓ c.overG).map
        (Q ((boundedConstructibleUpperStar Λ ℓ c.overG).obj B)).inv ≫
      (boundedConstructibleLowerShriekOfCompactification
        Λ ℓ c).map
        (K ◁ (compactificationProjectionPullbackIso Λ ℓ c).hom.app B)) ∧
    (∀ B, (P B).inv =
      (boundedConstructibleLowerShriekOfCompactification
        Λ ℓ c).map
        (K ◁ (compactificationProjectionPullbackIso Λ ℓ c).inv.app B) ≫
      (boundedConstructibleLowerStar Λ ℓ c.overG).map
        (Q ((boundedConstructibleUpperStar Λ ℓ c.overG).obj B)).hom ≫
      (alpha B).inv) ∧
    (∀ B, (P B).hom ≫ (P B).inv = 𝟙 _ ∧ (P B).inv ≫ (P B).hom = 𝟙 _) ∧
    (∀ (B B' : ProEtale.BoundedConstructible
        (condensedRingObj Λ Y.left)) (h : B ⟶ B'),
      (boundedConstructibleLowerShriekOfCompactification
        Λ ℓ c).obj K ◁ h ≫ (P B').hom =
      (P B).hom ≫ (boundedConstructibleLowerShriekOfCompactification
        Λ ℓ c).map
        (K ◁ (boundedConstructibleUpperStar Λ ℓ f).map h)) ∧
    (∀ (B : ProEtale.BoundedConstructible (condensedRingObj Λ Y.left)),
      c = compactificationOverField f → HEq (P B).hom
        (((boundedConstructibleExceptionalProjection Λ ℓ f).app K).app B))

end Main

section RingedNormalization

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1, u + 1, u + 2}
  (ModuleRingedComparison.modules.{u} Λ T)]

/-- The restricted proper and open arrows are the precise ambient module-object maps,
not just maps with the same endpoints. The following ringed clauses normalize them
under the specified section-module equivalences.
Source: blueprint main-20261015, Open immersions and Derived version
(blueprint: lem-pd-compactification-projection-inverse).
Proof: unfold the restricted adjunctions from sk-def-sfb-dc-restricted-functors
and def-sfb-dc-open-lower-shriek-adjunction. Their Hom equivalences, units,
counits and tensor maps are the ambient ones. Apply the faithful inclusion
to the adjoint of counit after delta and to unit, lax tensor, counit respectively.
These are exactly internalProjection and internalOpenProjection. -/
def compactification_projection_ambient_normalizationClauses
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X.left))
    (B : ProEtale.BoundedConstructible (condensedRingObj Λ Y.left))
    (N : ProEtale.BoundedConstructible (condensedRingObj Λ c.Z)) : Prop :=
    ((boundedConstructibleUpperStarLowerStarAdjunction
        Λ ℓ c.overG).projectionMorphism
      ((boundedConstructibleOpenImmersionLowerShriek
        Λ ℓ c.overI).obj K) B).hom =
      internalProjection Λ c.g
        ((D((c.i)_!open⟦Λ⟧)).obj K.obj) B.obj ∧
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      Λ ℓ c.overI).projectionComparison K N).hom =
      internalOpenProjection Λ c.i K.obj N.obj

/-- The proper normalization is the actual ringed-topos projection mate, with every
pushforward, tensor and pullback comparison inserted.
Source: blueprint main-20261015, canonical-map equality in derived projection
(blueprint: lem-pd-compactification-projection-inverse).
Proof: apply projection_comparison of lem-pd-module-ringed-topos-derived-comparison
to q, j_!K and B. Its derived_homEquiv identifies the actual counit and
delta_comparison the actual oplax map. Transposing their composite gives
precisely the ringed mate of lem-weil-pbc-ringed-projection-mate-exact. -/
def compactification_projection_proper_normalizationClauses {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X))
    (L : DerivedCategory (internalModules Λ Y)) : Prop :=
    (derivedEquivalence Λ Y).functor.map (internalProjection Λ f K L) ≫
        (derivedPushComparison Λ f).hom.app
          (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensorComparison Λ X).hom.app
          (K, (internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensor Λ X).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ X).functor.obj K))
          ((derivedPullComparison Λ f).hom.app L))) =
      (tensorComparison Λ Y).hom.app
          ((internalDerivedPushforward Λ f).obj K, L) ≫
        (tensor Λ Y).map (Prod.mkHom ((derivedPushComparison Λ f).hom.app K)
          (𝟙 ((derivedEquivalence Λ Y).functor.obj L))) ≫
        projection Λ f ((derivedEquivalence Λ X).functor.obj K)
          ((derivedEquivalence Λ Y).functor.obj L)

/-- The open normalization is the precise ringed unit--lax-tensor--counit projection.
Source: blueprint main-20261015, Open immersions and Derived version
(blueprint: lem-pd-compactification-projection-inverse).
Proof: apply openProjection_comparison of lem-pd-module-ringed-topos-derived-comparison
to j,K,N. The equality of open Hom equivalences identifies unit and counit, and
mu_comparison identifies the actual inverse of delta. Naturality of the tensor
and extension comparisons then gives the displayed equality of all three factors. -/
def compactification_projection_open_normalizationClauses
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (internalModules Λ U))
    (L : DerivedCategory (internalModules Λ X)) : Prop :=
    (derivedEquivalence Λ X).functor.map (internalOpenProjection Λ j K L) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedExtension Λ j).obj K, L) ≫
        (tensor Λ X).map (Prod.mkHom ((derivedExtensionComparison Λ j).hom.app K)
          (𝟙 ((derivedEquivalence Λ X).functor.obj L))) =
      (derivedExtensionComparison Λ j).hom.app
          (((CondensedRing.derivedTensor Λ U).obj K).obj ((internalDerivedPullback Λ j).obj L)) ≫
        (derivedExtension Λ j).map ((tensorComparison Λ U).hom.app
          (K, (internalDerivedPullback Λ j).obj L)) ≫
        (derivedExtension Λ j).map ((tensor Λ U).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ U).functor.obj K))
          ((derivedPullComparison Λ j).hom.app L))) ≫
        openProjection Λ j ((derivedEquivalence Λ U).functor.obj K)
          ((derivedEquivalence Λ X).functor.obj L)

end RingedNormalization

/-- The specified compactification projection is invertible with the prescribed inverse,
naturality, chosen-compactification component and both ringed normalization clauses.
Source: blueprint main-20261015, `det-lem-int-tensor-projection.proof.md`,
Open immersions and Derived version
(blueprint: lem-pd-compactification-projection-inverse).
Proof: restrict the actual ambient tensor and adjunction structures. The section-module
comparison identifies counit after delta with the proper ringed mate and unit followed
by the inverse delta with the open projection. Apply the condensed proper projection
formula to j_!K,B and the condensed open projection formula to K,N. These give alpha
and Q. Compose alpha, Rq_*(Q inverse), and Rq_*j_!(1 tensor a) to obtain P.
Its inverse is the reverse composite of inverse factors; cancellation gives both
identity equations. Paste the naturality squares of alpha, Q and a for every h.
At the chosen compactification unfold the target's exceptional projection definition;
its ambient arrow and composition comparison are exactly these factors.
See the five-step proof plan at compactification_projection_inverseClauses. -/
theorem compactification_projection_inverse
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1, u + 1, u + 2}
      (ModuleRingedComparison.modules.{u} (Profinite.padicAlgClRingObj.{u} ℓ) T)]
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    compactification_projection_inverseClauses (Profinite.padicAlgClRingObj ℓ) ℓ c K ∧
    (∀ (B : ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))
      (N : ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) c.Z)),
      compactification_projection_ambient_normalizationClauses
        (Profinite.padicAlgClRingObj ℓ) ℓ c K B N) ∧
    (∀ B : ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left),
      compactification_projection_proper_normalizationClauses
        (Profinite.padicAlgClRingObj.{u} ℓ) c.g
        ((D((c.i)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj) B.obj) ∧
    (∀ N : ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) c.Z),
      compactification_projection_open_normalizationClauses
        (Profinite.padicAlgClRingObj.{u} ℓ) c.i K.obj N.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
