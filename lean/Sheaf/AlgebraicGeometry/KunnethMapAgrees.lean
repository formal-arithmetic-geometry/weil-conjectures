/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Data.ZMod.Basic
public import Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow
import Sheaf.EtaleCohomology.SepClosedFieldVanishing
import Mathlib.Algebra.Homology.Additive
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.Paper.KFlatRingedToposPullback
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.AlgebraicGeometry.ProperStability
import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Mathlib.GroupTheory.Torsion
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.FieldDiscreteModules
import Sheaf.AlgebraicGeometry.KunnethGlobalSections
import Sheaf.AlgebraicGeometry.RGammaUnboundedBounded
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Compatibility of the Künneth map with Leray and projection

Source: blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lem-kun-kunneth-map-agrees, and Stacks Project, Tags 0F14 and 0F1E
(blueprint: lem-kun-kunneth-map-agrees).

We state the identity in D(S_et, Λ). For S = Spec k with k separably closed,
evaluation at S is the exact monoidal equivalence with D(Λ). Under this specified
identification Rf(E), Rg(K) are A, B, Lg(A) is the constant complex, and the
projection map for g is exactly the constant-coefficient map r. This is the
identification checked on constant labels and derived counits in proof step 1
of the node. Thus every arrow below is the arrow of the displayed composite,
written before applying that equivalence, with no additional hypothesis.

The helper definitions expose the particular exchange, the two particular
projection maps, the six-arrow inverse, and the conjunction asserted in both
cases. They introduce no new tensor, pullback, global sections or Künneth map.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Arrows

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {S X Y W : Scheme.{u}}

/-- The node's e, using the recorded exact exchange transported from termwise
inverse image to the canonically isomorphic left derived pullback.
Source: Stacks Tag 07A7 (blueprint: lem-kun-kunneth-map-agrees). -/
noncomputable def kunnethLerayExchange
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : CommSq p q f g) (E : DerivedCategoryModule Λ X) :
    L((g)^*[ModuleCat.{u + 1} Λ]).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj E) ⟶
      R((q)_*[ModuleCat.{u + 1} Λ]).obj (L((p)^*[ModuleCat.{u + 1} Λ]).obj E) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).hom.app _ ≫
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app E ≫
      R((q)_*[ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) p).inv.app E)

/-- The node's t, the existing projection morphism for q at F = Lp(E), K.
Source: Stacks equation 0B56 (blueprint: lem-kun-kunneth-map-agrees). -/
noncomputable def kunnethLerayProjection (p : W ⟶ X) (q : W ⟶ Y)
    (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) q).app
    (L((p)^*[ModuleCat.{u + 1} Λ]).obj E)).app K

/-- The node's r before the separably closed base equivalence: PF_g(K,Rf(E)).
The constant-label tensor constraints and counits identify this with the recorded
constantDerivedProjectionMap after evaluation at S. Source: node proof step 1,
Stacks equation 0B56 (blueprint: lem-kun-kunneth-map-agrees). -/
noncomputable def kunnethLerayConstantProjection (f : X ⟶ S) (g : Y ⟶ S)
    (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app K).app
    (R((f)_*[ModuleCat.{u + 1} Λ]).obj E)

/-- The six-arrow theta of the node, with its actual canonical maps and symmetries.
The hypotheses here only permit forming the inverses; the two case theorems below
assert them as conclusions. Source: blueprint's displayed theta and Stacks Tag 0F14
(blueprint: lem-kun-kunneth-map-agrees). -/
noncomputable def kunnethLerayInverse
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : CommSq p q f g) (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y)
    [he : IsIso (kunnethLerayExchange Λ sq E)]
    [ht : IsIso (kunnethLerayProjection Λ p q E K)]
    [hr : IsIso (kunnethLerayConstantProjection Λ f g E K)] :
    R((p ≫ f)_*[ModuleCat.{u + 1} Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
          (L((p)^*[ModuleCat.{u + 1} Λ]).obj E)).obj
            (L((q)^*[ModuleCat.{u + 1} Λ]).obj K)) ⟶
      ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj E)).obj
          (R((g)_*[ModuleCat.{u + 1} Λ]).obj K) :=
  (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ)
    q g (p ≫ f) sq.w.symm).inv.app _ ≫
  R((g)_*[ModuleCat.{u + 1} Λ]).map (inv (kunnethLerayProjection Λ p q E K)) ≫
  R((g)_*[ModuleCat.{u + 1} Λ]).map
    (((derivedTensor (ModuleCat.{u + 1} Λ) Y).map
      (inv (kunnethLerayExchange Λ sq E))).app K) ≫
  R((g)_*[ModuleCat.{u + 1} Λ]).map
    (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app
      (L((g)^*[ModuleCat.{u + 1} Λ]).obj
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj E))).app K) ≫
  inv (kunnethLerayConstantProjection Λ f g E K) ≫
  ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) S).hom.app
    (R((g)_*[ModuleCat.{u + 1} Λ]).obj K)).app
      (R((f)_*[ModuleCat.{u + 1} Λ]).obj E)

/-- All three isomorphism assertions, the displayed left-inverse identity, and
invertibility with precisely theta as inverse. The right-inverse identity merely
spells out the final inverse clause. Source: blueprint's conclusion, Stacks Tag 0F14
(blueprint: lem-kun-kunneth-map-agrees). -/
def KunnethLerayAgreement
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : CommSq p q f g) (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :
    Prop :=
  ∃ (he : IsIso (kunnethLerayExchange Λ sq E))
    (ht : IsIso (kunnethLerayProjection Λ p q E K))
    (hr : IsIso (kunnethLerayConstantProjection Λ f g E K)),
    kunnethMap (ModuleCat.{u + 1} Λ) p q f g (p ≫ f) rfl sq.w.symm E K ≫
        kunnethLerayInverse Λ sq E K (he := he) (ht := ht) (hr := hr) = 𝟙 _ ∧
    kunnethLerayInverse Λ sq E K (he := he) (ht := ht) (hr := hr) ≫
        kunnethMap (ModuleCat.{u + 1} Λ) p q f g (p ≫ f) rfl sq.w.symm E K = 𝟙 _ ∧
    IsIso (kunnethMap (ModuleCat.{u + 1} Λ) p q f g (p ≫ f) rfl sq.w.symm E K)

end Arrows

/-- Case (a), integral bounded-below coefficients, including the actual inverse.
Source: blueprint lem-kun-kunneth-map-agrees; Stacks Tag 0F14
(blueprint: lem-kun-kunneth-map-agrees).

Proof: evaluation at Spec k and constants are exact inverse monoidal equivalences
(lem-kun-0ezp, def-kun-constant-sheaf, lem-kun-pullback-constant). On local labels
the constant adjunction and tensor comparisons agree with those of g; deriving on
the same K-injectives identifies r with PF_g. Leray is the composition comparison
normalized on K-injectives, hence compatible with composite counits
(lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-weil-pbc-inverse-image-composition-module-linear). Inverse image preserves
flat K-flat models and the signed tensor symmetry; on local pure tensors its
composition constraints agree with successive pullbacks
(lem-weil-pbc-site-derived-tensor-descent, lem-weil-pbc-ringed-pullback-preserves-kflat).
Let s be symmetry, then r, then Rg of the reverse symmetry. Its g-adjoint is
identity tensor the g-counit. The q-adjoints of e and t are respectively the
pulled-back f-counit and q-counit tensor identity
(lem-weil-pbc-adjunct-counit-identity). Thus the composite of s, Rg(e tensor 1),
Rg(t) and inverse Leray has c-adjoint exactly the tensor of the pulled-back
f- and g-counits. This is the defining adjunct of kunnethMap; injectivity of
the Hom bijection identifies the maps. For (a), q is proper; exact inverse
image preserves lower bounds and torsion. Bounded-below proper base change
(thm-weil-pbc-bounded-below) makes e invertible, lem-kun-0f0f makes t invertible,
and lem-kun-0f0e makes r invertible since Rf(E) is bounded below and Y is qcqs.
Bounded and unbounded exchange agree on their common K-injective models.
Cancel the six isomorphisms in the map identity: the specified theta is both
inverse maps of kappa, and kappa is an isomorphism. -/
theorem kunnethMap_agrees_with_leray_projection_formula_integral
    {k : Type u} [Field k] [IsSepClosed k] {X Y W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsProper f]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (p : W ⟶ X) (q : W ⟶ Y) (sq : IsPullback p q f g)
    (E : DerivedCategoryModule (ULift.{u + 1} ℤ) X)
    (K : DerivedCategoryModule (ULift.{u + 1} ℤ) Y)
    (hE : ∃ a : ℤ, _root_.DerivedCategory.IsGE E a)
    (hK : ∃ b : ℤ, _root_.DerivedCategory.IsGE K b)
    (hEt : DerivedCategory.torsionCohomology (ULift.{u + 1} ℤ) X E) :
    KunnethLerayAgreement (ULift.{u + 1} ℤ) sq.toCommSq E K := by
  sorry

/-- Case (b), finite cyclic coefficients and arbitrary unbounded inputs.
Source: blueprint lem-kun-kunneth-map-agrees; Stacks Tag 0F14
(blueprint: lem-kun-kunneth-map-agrees).

Proof: the canonical-adjoint calculation is the one detailed in the integral
case: constants/evaluation identify r, normalized Leray identifies the composite
adjunction, tensor and symmetry agree on K-flat models, and two transposes
identify kappa with the forward factorization whose reverse is theta.
Proper base change for cyclic coefficients (lem-kun-0f0c) makes e invertible.
The proper projection formula for torsion coefficients (lem-kun-0f0g) makes t
invertible. Finite type over a field implies qcqs, and separable closedness gives
finite torsion cohomological dimension (lem-kun-0f10).
The constant projection formula (lem-kun-0f12) therefore makes r invertible.
All three assertions are in the full unbounded category. Cancel the factors
to obtain both inverse equations and IsIso kappa, with the displayed theta.
For n=1 all module categories are zero, and the same construction applies. -/
theorem kunnethMap_agrees_with_leray_projection_formula_modN
    {k : Type u} [Field k] [IsSepClosed k] {X Y W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsProper f]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : k))
    [LocallyOfFiniteType g] [QuasiCompact g]
    (p : W ⟶ X) (q : W ⟶ Y) (sq : IsPullback p q f g)
    (E : DerivedCategoryModule (ULift.{u + 1} (ZMod n)) X)
    (K : DerivedCategoryModule (ULift.{u + 1} (ZMod n)) Y) :
    KunnethLerayAgreement (ULift.{u + 1} (ZMod n)) sq.toCommSq E K := by
  sorry

end AlgebraicGeometry.Etale
