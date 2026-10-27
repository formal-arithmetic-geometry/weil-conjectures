module

public import Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso
public import Sheaf.AlgebraicGeometry.EtaleCohomologyPresentation
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-! # Canonical coherent cohomology classes in an abelian higher image

Source: Stacks Project, Etale Cohomology, Tag 03Q8, lemma-higher-direct-images.
(blueprint: def-weil-pbc-coherent-higher-image-classes).

## Main definitions

* `affineRealizationRawEvaluation`: the actual raw comparison with its coefficient transport.
* `affineRealizationClass`: its inverse followed by the actual abelian higher-image class.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] RingedSpace.moduleCohomology
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived
  CategoryTheory.derivedExtEvaluation coherentEtaleRestrictionIso tensorPullback tensorPullbackObj
  Etale.rawRestrictedCohomologyComparison
  Etale.abelianHigherDirectImageClass
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- The coefficient on the actual fibre product, with the raw-comparison factor order.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-coherent-higher-image-classes). -/
abbrev affineRealizationCoefficient {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (V : S.Etale) : (Limits.pullback V.hom f).Modules :=
  (tensorPullback (Limits.pullback.snd V.hom f)).obj G

/-- The abelian higher direct image, without any transported or independently chosen action.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-coherent-higher-image-classes). -/
abbrev affineRealizationHigherImage {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
    (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (liftedCoherentEtaleSheaf G)))

/-- The constructed additive equivalence underlying raw evaluation.
Source: Stacks Project, Tags 03Q8 and 03P2
(blueprint: def-weil-pbc-coherent-higher-image-classes). -/
def affineRealizationRawEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale) :
    (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V) ≃+
      Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q := by
  let := Etale.isIso_rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V
  exact (asIso (Etale.rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V)
    |>.addCommGroupIsoToAddEquiv).trans
    ((Etale.sheafHDerivedEquiv
      ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj
        (liftedCoherentEtaleSheaf G)) q).symm.trans
      (((Sheaf.functorH _ q).mapIso
        (coherentEtaleRestrictionIso (pullback.snd V.hom f) G)).addCommGroupIsoToAddEquiv))

attribute [local irreducible] affineRealizationRawEquiv

/-- The actual raw evaluation through the constructed additive equivalence.
Source: Stacks Project, Tags 03Q8 and 03P2
(blueprint: def-weil-pbc-coherent-higher-image-classes). -/
def affineRealizationRawEvaluation {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q :=
  affineRealizationRawEquiv f G q V z

attribute [local irreducible] affineRealizationRawEvaluation

/-- The constructed raw evaluation is bijective.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-coherent-higher-image-classes).
Proof: it is the forward map of the constructed additive equivalence. -/
theorem affineRealizationRawEvaluation_bijective {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale) :
    Function.Bijective (affineRealizationRawEvaluation f G q V) := by
  unfold affineRealizationRawEvaluation
  exact (affineRealizationRawEquiv f G q V).bijective

set_option backward.isDefEq.respectTransparency false in
/-- The canonical cohomology class in the abelian higher direct image. The inverse
of raw evaluation is uniquely determined by its bijectivity.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-coherent-higher-image-classes). -/
def affineRealizationClass {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale)
    (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q) :
    (affineRealizationHigherImage f G q).obj.obj (op V) :=
  Etale.abelianHigherDirectImageClass f q (liftedCoherentEtaleSheaf G) V
    ((affineRealizationRawEquiv f G q V).symm x)

attribute [local irreducible] affineRealizationClass


/-- Evaluation followed by its canonical higher-image class gives the actual raw class.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-coherent-higher-image-classes).
Proof: the inverse of the constructed raw equivalence cancels its forward map. -/
theorem affineRealizationClass_rawEvaluation {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    affineRealizationClass f G q V (affineRealizationRawEvaluation f G q V z) =
      Etale.abelianHigherDirectImageClass f q (liftedCoherentEtaleSheaf G) V z := by
  unfold affineRealizationClass affineRealizationRawEvaluation
  exact congrArg (Etale.abelianHigherDirectImageClass f q (liftedCoherentEtaleSheaf G) V)
    ((affineRealizationRawEquiv f G q V).symm_apply_apply z)


end
end AlgebraicGeometry.Scheme.Modules
