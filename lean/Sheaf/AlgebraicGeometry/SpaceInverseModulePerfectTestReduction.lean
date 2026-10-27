module

public import Sheaf.AlgebraicGeometry.SpaceInverseModuleDerivedLimit
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.RelativeDualizingTracePair
public import Sheaf.AlgebraicGeometry.RingDerivedScalarExtension
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.SpaceFlatComplexBaseChange
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus

/-! # Perfect tests of infinitesimal module limits

Source: Stacks Project, spaces-flat.tex, Tag 0CX6, lemma-compute-against-perfect (1),
and spaces-perfect.tex, Tag 08IN
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction).

The paper's level n+1 is indexed by n : ℕ. All comparison arrows below are actual
adjunction mates. Compatibility is stated after scalar adjunction and restriction;
this is the transition square with its canonical scalar associativity identifications.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The counit-induced projection comparison in the argument order M tensor E.
Source: Stacks, Tag 08IN, projection formula in the proof of 0CX6
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleProjectionMap {Y X : AlgebraicSpace S}
    [HasDerivedCategory.{w} Y.SmallModules] [HasDerivedCategory.{w} X.SmallModules]
    (i : Y ⟶ X) (N : Y.DerivedModules) (E : X.DerivedModules) :
    X.derivedDualityModel.closed.tensor.obj ((derivedDirectImage i).obj N, E) ⟶
      (derivedDirectImage i).obj (Y.derivedDualityModel.closed.tensor.obj
        (N, (spaceDerivedPullback i).obj E)) :=
  (spaceDerivedAdjunction i).homEquiv _ _
    ((moduleDerivedPullbackTensor i).hom.app ((derivedDirectImage i).obj N, E) ≫
      Y.derivedDualityModel.closed.tensor.map
        (Prod.mkHom ((spaceDerivedAdjunction i).counit.app N) (𝟙 _)))

section Affine

variable [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]

/-- The finite-level tensor test, including its specified base-ring action.
Source: Stacks, Tag 0CX6 (1)
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleFiniteTest {B : Type u} [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (Y : Over S) (b : Y.left ≅ Spec (.of B))
    {Z : AlgebraicSpace S} (g : Z ⟶ schemeSpace Y)
    (M : Z.Modules) (E : Z.DerivedModules) : DerivedCategory (ModuleCat.{u} B) :=
  (spaceAffineDerivedSections Y b g).obj
    (Z.derivedDualityModel.closed.tensor.obj
      ((DerivedCategory.singleFunctor Z.SmallModules 0).obj
        (Z.smallModuleRestriction.obj M), E))

/-- The actual comparison from the tensor test on X to the restricted finite-level test.
The first map derives the ordinary direct image, the second is the counit-induced
projection formula, and the third is normalized derived sections composition.
Source: Stacks, Tags 0CX6 and 08IN
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleTestComparison {B D : Type u} [CommRing B] [CommRing D]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} D)]
    {Y Y' : Over S} (b : Y.left ≅ Spec (.of B)) (d : Y'.left ≅ Spec (.of D))
    (a : Y' ⟶ Y) {X Z : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (i : Z ⟶ X) (g : Z ⟶ schemeSpace Y')
    (sq : i ≫ f = g ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map a) :
        schemeSpace Y' ⟶ schemeSpace Y))
    (M : Z.Modules) (E : X.DerivedModules) :
    (spaceAffineDerivedSections Y b f).obj
        (X.derivedDualityModel.closed.tensor.obj
          ((DerivedCategory.singleFunctor X.SmallModules 0).obj
            (X.smallModuleRestriction.obj ((moduleDirectImage i).obj M)), E)) ⟶
      (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap b d a)).obj
        (inverseModuleFiniteTest Y' d g M ((spaceDerivedPullback i).obj E)) :=
  (spaceAffineDerivedSections Y b f).map
      (X.derivedDualityModel.closed.tensor.map
        (Prod.mkHom
          ((DerivedCategory.singleFunctor X.SmallModules 0).map
            (X.smallModuleRestriction.map
              ((moduleDirectImage i).map (Z.smallModuleEquivalence.unitIso.hom.app M))) ≫
            traceDirectImageComparison i (Z.smallModuleRestriction.obj M))
          (𝟙 E)) ≫
        inverseModuleProjectionMap i
          ((DerivedCategory.singleFunctor Z.SmallModules 0).obj
            (Z.smallModuleRestriction.obj M)) E) ≫
    (spaceDerivedSectionsComposition b d a f i g sq).hom.app _

end Affine

section Tower

variable (A : ℕ → CommRingCat.{u}) (r : ∀ n : ℕ, A (n + 1) ⟶ A n)
  (c : Cone (Functor.ofOpSequence r))
  (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
  [∀ Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))), HasDerivedCategory.{w} Z.SmallModules]
  [HasDerivedCategory.{w} (ModuleCat.{u} c.pt)]
  [∀ n : ℕ, HasDerivedCategory.{w} (ModuleCat.{u} (A n))]
  (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))

/-- The scalar map induced by the actual projection Spec A_n to Spec lim A_n.
Gamma-Spec identifies this with the limit-cone projection c.π.app (op n).
Source: Stacks, Tag 0CX6
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleScalar (n : ℕ) : c.pt →+* A n :=
  spaceAffineRingMap (Iso.refl _) (Iso.refl _)
    (inverseModuleSpecMap (c.π.app (op n)))

/-- The fibre-product square, retaining the canonical structure projection.
Source: Stacks, Tag 0CX6, situation-existence
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction).
Proof: apply faithfulness of the full inclusion of spaces in sheaves, then the
fibre-product condition. The test arrow is exactly Yoneda of the spectrum map. -/
theorem inverseModuleFibreSquare (n : ℕ) :
    properQuotFst f (inverseModuleTest c n) ≫ f =
      properQuotSnd f (inverseModuleTest c n) ≫
        (ObjectProperty.homMk ((Scheme.fppfTopology.over _).yoneda.map
          (inverseModuleSpecMap (c.π.app (op n)))) :
            schemeSpace (inverseModuleSpec (A n)) ⟶ schemeSpace (inverseModuleSpec c.pt)) := by
  sorry

/-- RΓ(X, V tensor E), functorial in the quasi-coherent object V.
Source: Stacks, Tag 0CX6
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleTensorTest (E : X.DerivedModules) :
    X.DerivedQCoh ⥤ DerivedCategory (ModuleCat.{u} c.pt) :=
  X.derivedQCohProperty.ι ⋙ Prod.sectL X.DerivedModules E ⋙
    X.derivedDualityModel.closed.tensor ⋙
      spaceAffineDerivedSections (inverseModuleSpec c.pt) (Iso.refl _) f

/-- The canonical projection-formula comparison at level n.
Source: Stacks, Tags 0CX6 and 08IN
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleLevelComparison
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (E : X.DerivedModules) (n : ℕ) :=
  inverseModuleTestComparison (Iso.refl _) (Iso.refl _)
    (inverseModuleSpecMap (c.π.app (op n))) f
    (properQuotFst f (inverseModuleTest c n)) (properQuotSnd f (inverseModuleTest c n))
    (inverseModuleFibreSquare A r c X f n) (M n) E

/-- The scalar-extension adjunct of the actual Roos projection, followed by the
specified projection-formula comparison. No arbitrary isomorphism is chosen.
Source: Stacks, Tag 0CX6 (1)
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleReduction
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hq : ∀ n : ℕ,
      X.derivedQCohProperty (inverseModuleDerivedTerm f (inverseModuleTest c n) (M n)))
    (K : X.DerivedQCoh) (E : X.DerivedModules) (n : ℕ)
    (q : K ⟶ inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)) :=
  ((Adjunction.ofIsRightAdjoint
    (RingDerivedScalarExtension.moduleDerivedRestriction (inverseModuleScalar A r c n))).homEquiv
      _ _).symm
    ((inverseModuleTensorTest A r c X f E).map q ≫
      inverseModuleLevelComparison A r c X f M E n)


/-- The map on a tensor test induced by a morphism of its right factor.
Source: Stacks, Tag 0CX6, naturality in the perfect test
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleTestRightMap {V : X.DerivedModules}
    {E E' : X.DerivedModules} (v : E ⟶ E') :=
  (spaceAffineDerivedSections (inverseModuleSpec c.pt) (Iso.refl _) f).map
    (X.derivedDualityModel.closed.tensor.map (Prod.mkHom (𝟙 V) v))

/-- The finite-level map induced by a morphism of perfect tests on X.
Source: Stacks, Tag 0CX6, naturality
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleFiniteRightMap
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    {E E' : X.DerivedModules} (v : E ⟶ E') (n : ℕ) :=
  (spaceAffineDerivedSections (inverseModuleSpec (A n)) (Iso.refl _)
    (properQuotSnd f (inverseModuleTest c n))).map
      ((properQuotFibre f (inverseModuleTest c n)).derivedDualityModel.closed.tensor.map
        (Prod.mkHom
          (𝟙 ((DerivedCategory.singleFunctor _ 0).obj
            ((properQuotFibre f (inverseModuleTest c n)).smallModuleRestriction.obj (M n))))
          ((spaceDerivedPullback (properQuotFst f (inverseModuleTest c n))).map v)))

/-- The ring map for one step of the finite-level sequence.
Source: Stacks, Tag 0CX6, situation-existence
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleStepScalar (n : ℕ) : A (n + 1) →+* A n :=
  spaceAffineRingMap (Iso.refl _) (Iso.refl _) (inverseModuleSpecMap (r n))

/-- The scalar cone identity, including the Gamma-Spec identifications.
Source: Stacks, Tag 0CX6
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction).
Proof: naturality of Gamma-Spec identifies each displayed scalar map with its
original ring map. The result is c.w for the generating arrow n+1 to n. -/
theorem inverseModuleScalar_comp (n : ℕ) :
    (inverseModuleStepScalar A r n).comp (inverseModuleScalar A r c (n + 1)) =
      inverseModuleScalar A r c n := by
  sorry

/-- Exact restriction transitivity, with the cone's scalar identification.
Source: Stacks, Tag 0CX6, transition comparisons; Tag 0D6D
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleRestrictionStep (n : ℕ) :
    RingDerivedScalarExtension.moduleDerivedRestriction (inverseModuleStepScalar A r n) ⋙
        RingDerivedScalarExtension.moduleDerivedRestriction (inverseModuleScalar A r c (n + 1)) ≅
      RingDerivedScalarExtension.moduleDerivedRestriction (inverseModuleScalar A r c n) :=
  RingDerivedScalarExtension.moduleDerivedRestrictionComposition
    (inverseModuleScalar A r c (n + 1)) (inverseModuleStepScalar A r n)
    (inverseModuleScalar A r c n) (inverseModuleScalar_comp A r c n)

/-- The unit-preserving derived scalar associator for two consecutive reductions.
Source: Stacks, Tags 0CX6 and 0D6D
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleExtensionStep (n : ℕ) :
    RingDerivedScalarExtension.moduleDerivedExtension (inverseModuleScalar A r c (n + 1)) ⋙
        RingDerivedScalarExtension.moduleDerivedExtension (inverseModuleStepScalar A r n) ≅
      RingDerivedScalarExtension.moduleDerivedExtension (inverseModuleScalar A r c n) :=
  RingDerivedScalarExtension.moduleDerivedExtensionComposition
    (inverseModuleScalar A r c (n + 1)) (inverseModuleStepScalar A r n)
    (inverseModuleScalar A r c n) (inverseModuleScalar_comp A r c n)

/-- The lower fibre square for a consecutive ring transition.
Source: Stacks, Tag 0CX6, situation-existence
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction).
Proof: both sides are the second projection of the pullback map defining
properQuotFibreMap. Its second component is Yoneda of inverseModuleTestMap.left,
which by definition is the prescribed contravariant ring transition. -/
theorem inverseModuleTransitionSquare (n : ℕ) :
    properQuotFibreMap f (inverseModuleTestMap c n) ≫
        properQuotSnd f (inverseModuleTest c (n + 1)) =
      properQuotSnd f (inverseModuleTest c n) ≫
        (ObjectProperty.homMk ((Scheme.fppfTopology.over _).yoneda.map
          (inverseModuleSpecMap (r n))) :
            schemeSpace (inverseModuleSpec (A n)) ⟶
              schemeSpace (inverseModuleSpec (A (n + 1)))) := by
  sorry

/-- The actual map on finite-level tests: the quotient-module adjunction unit,
followed by the specified reduction isomorphism, the projection comparison, and
normalized associativity of derived pullback of E.
Source: Stacks, Tag 0CX6, proof; Tag 08IN
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleFiniteTransition
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n)
    (E : X.DerivedModules) (n : ℕ) :=
  (spaceAffineDerivedSections (inverseModuleSpec (A (n + 1))) (Iso.refl _)
    (properQuotSnd f (inverseModuleTest c (n + 1)))).map
      ((properQuotFibre f (inverseModuleTest c (n + 1))).derivedDualityModel.closed.tensor.map
        (Prod.mkHom ((DerivedCategory.singleFunctor _ 0).map
          ((properQuotFibre f (inverseModuleTest c (n + 1))).smallModuleRestriction.map
            ((moduleTensorAdjunction (properQuotFibreMap f (inverseModuleTestMap c n))).homEquiv
              _ _ (e n).hom))) (𝟙 _))) ≫
    inverseModuleTestComparison (Iso.refl _) (Iso.refl _) (inverseModuleSpecMap (r n))
      (properQuotSnd f (inverseModuleTest c (n + 1)))
      (properQuotFibreMap f (inverseModuleTestMap c n))
      (properQuotSnd f (inverseModuleTest c n)) (inverseModuleTransitionSquare A r c X f n)
      (M n) ((spaceDerivedPullback (properQuotFst f (inverseModuleTest c (n + 1)))).obj E) ≫
    (RingDerivedScalarExtension.moduleDerivedRestriction (inverseModuleStepScalar A r n)).map
      ((spaceAffineDerivedSections (inverseModuleSpec (A n)) (Iso.refl _)
        (properQuotSnd f (inverseModuleTest c n))).map
          ((properQuotFibre f (inverseModuleTest c n)).derivedDualityModel.closed.tensor.map
            (Prod.mkHom (𝟙 _)
              ((spaceDerivedPullbackComp (properQuotFst f (inverseModuleTest c (n + 1)))
                (properQuotFibreMap f (inverseModuleTestMap c n))).inv.app E ≫
                (eqToIso (congrArg (fun j ↦ (spaceDerivedPullback j).obj E)
                  (properQuotFibreMap_fst f (inverseModuleTestMap c n)))).hom))))

/-- The scalar-extension adjunct of the specified finite-level transition.
Source: Stacks, Tag 0CX6, proof, the maps induced by the module isomorphisms
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleFiniteReduction
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n)
    (E : X.DerivedModules) (n : ℕ) :=
  ((Adjunction.ofIsRightAdjoint
    (RingDerivedScalarExtension.moduleDerivedRestriction (inverseModuleStepScalar A r n))).homEquiv
      _ _).symm (inverseModuleFiniteTransition A r c X f M e E n)


/-- Projection from the specified Roos triangle, in the full quasi-coherent category.
Source: Stacks, Tags 0CX5 and 0CX6
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction). -/
def inverseModuleLimitProjection
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hq : ∀ n : ℕ,
      X.derivedQCohProperty (inverseModuleDerivedTerm f (inverseModuleTest c n) (M n)))
    [HasProduct (fun n : ℕ ↦ inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))]
    (K : X.DerivedQCoh)
    (p : K ⟶ ∏ᶜ (fun n : ℕ ↦ inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)))
    (n : ℕ) :=
  p ≫ Pi.π (fun m : ℕ ↦ inverseModuleQCohTerm f (inverseModuleTest c m) (M m) (hq m)) n

/-- Perfect tensor tests of the intrinsic quasi-coherent homotopy limit are perfect
and recover every finite-level test by the specified scalar-adjoint comparison.
The second conjunct is the projection-formula identification on X; the third is
beta, the fourth its naturality, and the final equality is the consecutive-level
square with the unit-preserving derived scalar associator.

Source: Stacks Project, spaces-flat.tex, Tag 0CX6, lemma-compute-against-perfect (1),
with spaces-perfect.tex, Tag 08IN
(blueprint: lem-sfb-space-inverse-module-perfect-test-reduction).

Proof:
1. Finite presentation is stable under base change (flat-proper-fp-locality), and
   derived pullback preserves perfect complexes (space-perfect-limit-category).
   The given proper carrier contains the annihilator support; proper-support
   closed operations make that support proper. Thus M_n[0] satisfies the bounded,
   finitely presented, relatively flat, proper-support tensor theorem's hypotheses.
2. Apply properSupport_tensor_perfect to each finite-level structural map and E_n.
   Derived image composition and affine-etale-derived-module-realization identify
   its global sections with T_n. Derived etale/Zariski equivalence, etale detection
   of perfectness and perfect-affine-bounded-projective make T_n perfect over A_n.
   Flat-complex base change and affine-derived-pullback-tensor-tilde identify its
   consecutive scalar-extension adjunct with the map from the specified e_n.
3. Apply nil-ring-perfect-derived-limit to these T_n: surjectivity, elementwise
   nilpotent kernels and the ring limit reconstruct a perfect T with its actual
   scalar-adjoint projection isomorphisms. No adic-power hypothesis is introduced.
4. The closed fibre maps are affine. Quasi-coherent pushforward and affine module
   higher-image vanishing identify ordinary and derived direct images. The qcqs
   derived projection formula and derived etale chart calculus give exactly
   inverseModuleTestComparison, including its coefficient naturality.
5. Apply space-perfect-tensor-global-limits to K's intrinsic product triangle.
   This gives C_E isomorphic to T with the same projections. Its scalar reduction
   is therefore invertible; scalar adjunction identifies it with inverseModuleReduction.
   Composing with the inverse projection formula gives the equivalent formulation on X.
6. Tensor functoriality, naturality of projection formula and scalar adjunction
   give the displayed E-naturality. For consecutive levels, q_n = q_(n+1)t_n.
   Both sides of the final square have adjunct RΓ(q_n tensor 1) followed by the
   same normalized projection comparison. The quotient-module unit, e_n and
   normalized derived pullback composition are exactly inverseModuleFiniteTransition.
   Adjunction bijectivity proves equality, with inverseModuleExtensionStep supplying
   the canonical scalar associativity. Finite-level flat base change gives its isomorphism.
-/
theorem inverseModulePerfectTestReduction
    (hsurj : ∀ n : ℕ, Function.Surjective (r n))
    (hnil : ∀ (n : ℕ) (a : A (n + 1)), (r n) a = 0 → IsNilpotent a)
    (hc : IsLimit c) (hsep : MapIsSeparated f) (hfp : ProperQuotFinitePresentation f)
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hqc : ∀ n : ℕ, (M n).IsQuasicoherent)
    (hfin : ∀ n : ℕ, (M n).IsFinitePresentation)
    (hflat : ∀ (n : ℕ) (U : (properQuotFibre f (inverseModuleTest c n)).EtaleSite),
      ((schemeRestriction _ U).obj (M n)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ (properQuotSnd f (inverseModuleTest c n)).hom.hom)).left)
    (hsupp : ∀ n : ℕ, ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (i : Z ⟶ properQuotFibre f (inverseModuleTest c n)),
      IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧
      MapIsProper (i ≫ properQuotSnd f (inverseModuleTest c n)) ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M n))
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n)
    (hq : ∀ n : ℕ,
      X.derivedQCohProperty (inverseModuleDerivedTerm f (inverseModuleTest c n) (M n)))
    [HasProduct (fun n : ℕ ↦ inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))]
    (K : X.DerivedQCoh)
    (p : K ⟶ ∏ᶜ (fun n : ℕ ↦ inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)))
    (δ : (∏ᶜ (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))) ⟶ K⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle (fun n : ℕ ↦ inverseModuleDerivedTransition f
      (inverseModuleTestMap c n) (M n) (M (n + 1)) (e n) (hq n) (hq (n + 1))) K p δ)
    (E : X.DerivedQCoh)
    (hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf E.obj) :
    DerivedCategory.IsPerfectRingComplex ((inverseModuleTensorTest A r c X f E.obj).obj K) ∧
    (∀ n : ℕ, IsIso (inverseModuleLevelComparison A r c X f M E.obj n)) ∧
    (∀ n : ℕ, IsIso (inverseModuleReduction A r c X f M hq K E.obj n
      (inverseModuleLimitProjection A r c X f M hq K p n))) ∧
    (∀ (E' : X.DerivedQCoh)
      (_hE' : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf E'.obj) (v : E ⟶ E') (n : ℕ),
      (RingDerivedScalarExtension.moduleDerivedExtension (inverseModuleScalar A r c n)).map
          (inverseModuleTestRightMap A r c X f (V := K.obj) v.hom) ≫
        inverseModuleReduction A r c X f M hq K E'.obj n
          (inverseModuleLimitProjection A r c X f M hq K p n) =
      inverseModuleReduction A r c X f M hq K E.obj n
          (inverseModuleLimitProjection A r c X f M hq K p n) ≫
        inverseModuleFiniteRightMap A r c X f M v.hom n) ∧
    (∀ n : ℕ, IsIso (inverseModuleFiniteReduction A r c X f M e E.obj n) ∧
      (inverseModuleExtensionStep A r c n).hom.app
          ((inverseModuleTensorTest A r c X f E.obj).obj K) ≫
        inverseModuleReduction A r c X f M hq K E.obj n
          (inverseModuleLimitProjection A r c X f M hq K p n) =
      (RingDerivedScalarExtension.moduleDerivedExtension (inverseModuleStepScalar A r n)).map
          (inverseModuleReduction A r c X f M hq K E.obj (n + 1)
            (inverseModuleLimitProjection A r c X f M hq K p (n + 1))) ≫
        inverseModuleFiniteReduction A r c X f M e E.obj n) := by
  sorry

end Tower

end AlgebraicGeometry.AlgebraicSpace
