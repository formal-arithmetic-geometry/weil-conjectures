module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
public import Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso
public import Sheaf.AlgebraicGeometry.EtaleCohomologyPresentation
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
public import Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback
public import Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Realization of affine coherent cohomology as an etale module higher image

Source: Stacks Project, Etale Cohomology, Tag 03Q8, lemma-higher-direct-images;
Tag 03P2 for the simultaneous coherent comparison.
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization).
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] Etale.sheafHDerivedEquiv Etale.sheafHToDerived
  CategoryTheory.derivedExtEvaluation coherentEtaleRestrictionIso
  moduleAbelianCohomologyLarge coherentEtaleMap qcoherentPullbackSection
  moduleCohomologyFMap IsNormalizedCoherentEtaleComparison
  tensorPullback tensorPullbackObj tensorSectionsComp tensorSectionsUnit
  etaleTensorSectionsRestriction
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The common-lift simultaneous comparison, selected by its unique normalization.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization). -/
def affineRealizationComparison (Y : Scheme.{u}) [CompactSpace Y] [Y.IsSeparated]
    (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Sheaf.H (liftedCoherentEtaleSheaf M) q ≃+
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj M :=
  (Classical.choose (exists_unique_qcoherentNormalizedComparison Y) M q).symm

attribute [local irreducible] affineRealizationComparison

/-- Pullback with the canonical tensor-composition coefficient identification.
Source: Stacks Project, Tags 03Q8 and 01FD
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization). -/
def affineRealizationRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V)) ⟶
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V'.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V')) := by
  let B : S.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
  let b : B.obj V' ⟶ B.obj V := B.map h
  let adj : tensorPullback b.left ⊣ pushforward b.left :=
    Classical.choose (exists_tensorPullbackAdjunction b.left)
  let ψ : (tensorPullback b.left).obj (affineRealizationCoefficient f G V) ⟶
      affineRealizationCoefficient f G V' :=
    (tensorSectionsComp b.left (Limits.pullback.snd V.hom f)).hom.app G ≫
      eqToHom (congrArg (fun j ↦ (tensorPullback j).obj G) b.w)
  exact moduleCohomologyFMap b.left (adj.homEquiv _ _ ψ) q

attribute [local irreducible] affineRealizationRestriction

/-- The affine specialization of the canonical simultaneous comparison.
Quasi-compactness is stable under base change; separatedness over an affine scheme
implies absolute separatedness. Neither property is imposed on S.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization). -/
def affineRealizationAffineComparison {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V : S.Etale) [IsAffine V.left] :
    Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q ≃+
      (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V) := by
  letI : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  letI : CompactSpace ((𝟭 Scheme).obj V.left) :=
    Scheme.compactSpace_of_isAffine V.left
  exact @affineRealizationComparison (Limits.pullback V.hom f)
    (QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst V.hom f))
    ((HasAffineProperty.iff_of_isAffine (P := @IsSeparated)
      (Q := fun Y _ _ _ ↦ Scheme.IsSeparated Y)
      (f := Limits.pullback.fst V.hom f)).mp inferInstance)
    (affineRealizationCoefficient f G V) inferInstance q

attribute [local irreducible] affineRealizationAffineComparison

/-- Evaluate a sectionwise module action without introducing a file-local instance.
Source: Stacks Project, Modules on Sites, definition of a sheaf of modules
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization). -/
def affineRealizationSmul {R : Type v} {A : Type w} [Semiring R] [AddCommMonoid A]
    (m : Module R A) (a : R) (x : A) : A :=
  @SMul.smul R A m.toDistribMulAction.toMulAction.toSemigroupAction.toSMul a x

/-- Compatible affine linear comparisons realize the abelian higher direct image as
an etale module sheaf, with its induced local scalar action and both class normalizations.
The sectionwise Module structures, their semilinear restrictions, and the linearity
of the abelian sheaf isomorphism are precisely an isomorphism of module sheaves.
Source: Stacks Project, Tag 03Q8, lemma-higher-direct-images; Tag 03P2
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization).

Proof:
1. Quasi-compactness and separatedness survive base change. Over an affine base the
fibre product is quasi-compact and separated, and its pulled-back coefficient is
quasi-coherent. Apply the simultaneous canonical coherent comparison there.
2. Etale inverse image is restriction. The normalized tensor-pullback composition
identifies its coefficient with the tensor-section sheaf of the pulled-back module.
3. On the full etale site take the restricted cohomology presheaf. Multiplication
by pullbacks of base functions defines its sectionwise module actions. Functoriality
and coefficient naturality make restrictions semilinear. Module sheafification has
the prescribed underlying abelian higher direct image, by Tag 03Q8.
4. Compose the affine comparisons with the given e. The assumed square gives
naturality; the scalar comparison and scalar-endomorphism lemma give linearity.
5. Affine objects cover every etale object. The full affine subsite, with induced
sieve topology, is dense; restriction is therefore fully faithful on abelian sheaves
in the common coefficient universe.
6. The affine comparison makes the restricted cohomology presheaf a sheaf. Naturality
of the dense-subsite sheafification comparison at the sheafification unit shows that
its restriction is invertible. Compose its inverse with the affine comparisons and
extend the resulting isomorphism by full faithfulness.
7. The unit is linear, as are the affine comparisons. On an arbitrary etale object
restrict to affine opens and use sheaf uniqueness. This proves the stated linearity
for every local scalar, including on non-affine objects.
8. The defining equation gives the cohomology-class normalization. The actual raw
evaluation and raw-restricted-class normalization identify its raw class with that
cohomology class; substitution gives the second formula. -/
theorem exists_affineCohomologyEtaleModuleRealization {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤))
    (e_linear : ∀ (V : S.Etale) [IsAffine V.left] (a : Γ(V.left, ⊤))
      (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e V ((Limits.pullback.fst V.hom f).appTop a • x) = a • e V x)
    (e_natural : ∀ (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
      (h : V' ⟶ V)
      (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e V' (affineRealizationRestriction f G q h x) =
        etaleTensorSectionsRestriction E h (e V x)) :
    ∃ (action : ∀ V : S.Etale,
        Module (ULift.{u + 1} Γ(V.left, ⊤))
          ((affineRealizationHigherImage f G q).obj.obj (op V)))
      (Φ : affineRealizationHigherImage f G q ≅ liftedCoherentEtaleSheaf E),
      (∀ (V V' : S.Etale) (h : V' ⟶ V) (a : ULift.{u + 1} Γ(V.left, ⊤))
        (x : (affineRealizationHigherImage f G q).obj.obj (op V)),
        (affineRealizationHigherImage f G q).obj.map h.op
          (affineRealizationSmul (action V) a x) =
        affineRealizationSmul (action V') (ULift.up (h.left.appTop a.down))
          ((affineRealizationHigherImage f G q).obj.map h.op x)) ∧
      (∀ (V : S.Etale) (a : Γ(V.left, ⊤))
        (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
        affineRealizationSmul (action V) (ULift.up a) (affineRealizationClass f G q V x) =
          affineRealizationClass f G q V (Sheaf.H.map
            (coherentEtaleMap _ _
              ((affineRealizationCoefficient f G V).smulHom
                ((Limits.pullback.fst V.hom f).appTop a)))
            q x)) ∧
      (∀ (V : S.Etale) (a : ULift.{u + 1} Γ(V.left, ⊤))
        (x : (affineRealizationHigherImage f G q).obj.obj (op V)),
        Φ.hom.hom.app (op V) (affineRealizationSmul (action V) a x) =
          ULift.up (a.down • (@id Γ((tensorPullback V.hom).obj E, ⊤)
            (Φ.hom.hom.app (op V) x).down))) ∧
      (∀ (V : S.Etale) [IsAffine V.left]
        (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
        Φ.hom.hom.app (op V) (affineRealizationClass f G q V x) =
          ULift.up (e V (affineRealizationAffineComparison f G q V x))) ∧
      (∀ (V : S.Etale) [IsAffine V.left]
        (z : (Etale.abelianHigherDirectImageRawPresheaf f q
          (liftedCoherentEtaleSheaf G)).obj (op V)),
        Φ.hom.hom.app (op V)
          (Etale.abelianHigherDirectImageClass f q (liftedCoherentEtaleSheaf G) V z) =
          ULift.up (e V (affineRealizationAffineComparison f G q V
            (affineRealizationRawEvaluation f G q V z)))) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
