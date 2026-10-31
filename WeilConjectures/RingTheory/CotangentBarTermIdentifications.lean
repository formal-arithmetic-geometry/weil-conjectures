/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.CotangentDifferentialPresheafSes
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.CategoryTheory.DerivedColimitChangeRings
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import WeilConjectures.RingTheory.PolynomialPresentationHomology
import WeilConjectures.AlgebraicTopology.SurjectiveQuasiIsoTrivialKan
import WeilConjectures.AlgebraicGeometry.TrivialKanHomotopyEquivalence
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
import WeilConjectures.TraceFormula.OnePointDerivedRingIdentification

/-! # The three polynomial-pair bar terms

Source: Stacks Project, Cotangent Complex, Tags 08QX, 08QW, 08PU and 08PN;
Cohomology on Sites, Tags 08Q8 and 06YQ
(blueprint: lem-trf-cotangent-bar-term-identifications).

The three isomorphisms are in the derived category. Their equations specify the
canonical maps, including the flat-presheaf tensor comparison on generators.
The full-site coefficients use the explicit containing-universe transport of the
helpers owned by this node. The landed coordinate-site sheaf-model interface
remains imported without modification. No coefficient map is assumed flat.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings

namespace Algebra.CotangentSheaf

/-- Coefficient transport to the containing universe, including the scalar action.
Source: Stacks 08PS, size convention (blueprint: lem-trf-cotangent-bar-term-identifications). -/
abbrev largeModules (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u + 1} (ULift.{u + 1} R) :=
  ModuleCat.uliftFunctor.{u + 1, u, u} R ⋙
    ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom

/-- Exactness of the explicit coefficient transport, using the existing ULift and
restriction instances. Source: Stacks 08PS
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
instance largeModules_preservesFiniteLimits (R : Type u) [CommRing R] :
    PreservesFiniteLimits (largeModules R) :=
  comp_preservesFiniteLimits (ModuleCat.uliftFunctor.{u + 1, u, u} R)
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom)

/-- Right exactness of the same coefficient transport, by the existing instances.
Source: Stacks 08PS (blueprint: lem-trf-cotangent-bar-term-identifications). -/
instance largeModules_preservesFiniteColimits (R : Type u) [CommRing R] :
    PreservesFiniteColimits (largeModules R) :=
  comp_preservesFiniteColimits (ModuleCat.uliftFunctor.{u + 1, u, u} R)
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom)

/-- Derived colimit on the full presentation site with the containing coefficients.
Source: Stacks 08PS (blueprint: lem-trf-cotangent-bar-term-identifications). -/
def fullLowerShriek (bar : CategoryColimitBarSystem.{u + 1})
    {A B : CommRingCat.{u}} (f : A ⟶ B) :=
  CochainComplex.singleFunctor ((CotangentSites.Site f)ᵒᵖ ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) 0 ⋙ DerivedCategory.Q ⋙
      (bar.models (CotangentSites.Site f) (ULift.{u + 1} B)).derived

/-- The existing standard differential complex, transported termwise by `largeModules`.
Source: Stacks 08PN (blueprint: lem-trf-cotangent-bar-term-identifications). -/
def largeDifferentialComplex (coh : CotangentResolution.Coherence.{u})
    {f : Arrow CommRingCat.{u}} (P : CotangentResolution.Augmentation f) :=
  ((largeModules f.right).mapHomologicalComplex (.up ℤ)).obj
    (CotangentResolution.differentialComplex (coh.differentials P))

/-- The existing cotangent object in the containing module universe, on its standard model.
Source: Stacks 08PN and 08PU (blueprint: lem-trf-cotangent-bar-term-identifications). -/
def largeCotangent (coh : CotangentResolution.Coherence.{u})
    (f : Arrow CommRingCat.{u}) :=
  DerivedCategory.Q.obj (largeDifferentialComplex coh (coh.standard f))

/-- A polynomial resolution in the full presentation site, with both augmentations fixed.
Source: Stacks 08PS and 08QI (blueprint: lem-trf-cotangent-bar-term-identifications). -/
structure FullResolutionLift {A B : CommRingCat.{u}} {f : A ⟶ B}
    (P : CotangentResolution.Augmentation (Arrow.mk f)) where
  diagram : SimplicialObject (CotangentSites.Site f)ᵒᵖ
  ringIso : diagram ⋙ CotangentSites.presentationRing f ≅ P.algebra
  base_eq : ∀ n : ℕ,
    (CotangentSites.presentationBase f).app (diagram.obj (op ⦋n⦌)) ≫
      ringIso.hom.app (op ⦋n⦌) = P.base.app (op ⦋n⦌)
  augmentation_eq : ∀ n : ℕ,
    ringIso.hom.app (op ⦋n⦌) ≫ P.augmentation.app (op ⦋n⦌) =
      (CotangentSites.presentationAugmentation f).app (diagram.obj (op ⦋n⦌))

/-- Evaluation on a full-site resolution, followed by the actual alternating complex.
Source: Stacks 08PS (blueprint: lem-trf-cotangent-bar-term-identifications). -/
def fullEvaluation {A B : CommRingCat.{u}} {f : A ⟶ B}
    {P : CotangentResolution.Augmentation (Arrow.mk f)} (L : FullResolutionLift P) :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ (CotangentSites.Site f)ᵒᵖ
    (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj L.diagram ⋙
      CotangentResolution.negativeComplex (ModuleCat.{u + 1} (ULift.{u + 1} B))

/-- Additivity of evaluation, alternating faces and extension by zero, by their
existing instances. Source: Stacks 08PS
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
instance fullEvaluation_additive {A B : CommRingCat.{u}} {f : A ⟶ B}
    {P : CotangentResolution.Augmentation (Arrow.mk f)} (L : FullResolutionLift P) :
    (fullEvaluation L).Additive :=
  inferInstanceAs (((Functor.whiskeringLeft SimplexCategoryᵒᵖ (CotangentSites.Site f)ᵒᵖ
    (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj L.diagram ⋙
      (AlgebraicTopology.alternatingFaceMapComplex _) ⋙
        ComplexShape.embeddingDownNat.extendFunctor _).Additive)

/-- The element in degree `-n` of a full-site evaluated complex.
Source: Stacks 08PS (blueprint: lem-trf-cotangent-bar-term-identifications). -/
def fullEvaluationElement {A B : CommRingCat.{u}} {f : A ⟶ B}
    {P : CotangentResolution.Augmentation (Arrow.mk f)} (L : FullResolutionLift P)
    (F : (CotangentSites.Site f)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B))
    (n : ℕ) (x : F.obj (L.diagram.obj (op ⦋n⦌))) :
    ((fullEvaluation L).obj F).X (-(n : ℤ)) :=
  (((AlgebraicTopology.alternatingFaceMapComplex _).obj (L.diagram ⋙ F)).extendXIso
    ComplexShape.embeddingDownNat (i := n) rfl).inv x

/-- Compatibility of the full-site resolution comparison with connecting morphisms.
Source: Stacks 08PS and 08Q9 (blueprint: lem-trf-cotangent-bar-term-identifications). -/
def FullPreservesBoundary (bar : CategoryColimitBarSystem.{u + 1})
    {A B : CommRingCat.{u}} {f : A ⟶ B}
    {P : CotangentResolution.Augmentation (Arrow.mk f)} (L : FullResolutionLift P)
    (iso : fullLowerShriek bar f ≅ fullEvaluation L ⋙ DerivedCategory.Q)
    (hExact : ∀ T : ShortComplex ((CotangentSites.Site f)ᵒᵖ ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)),
      T.ShortExact → (T.map (fullEvaluation L)).ShortExact) : Prop :=
  ∀ (T : ShortComplex ((CotangentSites.Site f)ᵒᵖ ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B))) (hT : T.ShortExact)
    (hobj : ∀ V : (CotangentSites.Site f)ᵒᵖ,
      (T.map ((CategoryTheory.evaluation _ _).obj V)).ShortExact),
    (bar.models (CotangentSites.Site f) (ULift.{u + 1} B)).derived.map
        (DerivedCategory.triangleOfSESδ
          ((bar.models (CotangentSites.Site f) (ULift.{u + 1} B)).singleExact T hobj)) ≫
      ((bar.models (CotangentSites.Site f) (ULift.{u + 1} B)).derived.commShiftIso
        (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj T.X₁)) ≫
      (iso.hom.app T.X₁)⟦(1 : ℤ)⟧' =
        iso.hom.app T.X₃ ≫ DerivedCategory.triangleOfSESδ (hExact T hT)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The full-site version of the normalized resolution comparison. The augmentation
is fixed by the ordinary colimit cocone, and its localization is the universal counit.
Source: Stacks 08PS, 08PT, 08PU (blueprint: lem-trf-cotangent-bar-term-identifications). -/
structure FullResolutionComparison (bar : CategoryColimitBarSystem.{u + 1})
    {A B : CommRingCat.{u}} {f : A ⟶ B}
    {P : CotangentResolution.Augmentation (Arrow.mk f)} (L : FullResolutionLift P) where
  iso : fullLowerShriek bar f ≅ fullEvaluation L ⋙ DerivedCategory.Q
  augmentation : ∀ F : (CotangentSites.Site f)ᵒᵖ ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B),
    (fullEvaluation L).obj F ⟶ (CochainComplex.singleFunctor _ 0).obj (colimit F)
  augmentation_formula : ∀ (F : (CotangentSites.Site f)ᵒᵖ ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)) (x : F.obj (L.diagram.obj (op ⦋0⦌))),
    (augmentation F).f 0 (fullEvaluationElement L F 0 x) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (colimit F)).inv
        (colimit.ι F (L.diagram.obj (op ⦋0⦌)) x)
  normalization : ∀ F : (CotangentSites.Site f)ᵒᵖ ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B),
    iso.hom.app F ≫ DerivedCategory.Q.map (augmentation F) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (colim : ((CotangentSites.Site f)ᵒᵖ ⥤
            ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤ _) (.up ℤ) 0).inv.app F) =
      (bar.models (CotangentSites.Site f) (ULift.{u + 1} B)).comparison.app
        ((CochainComplex.singleFunctor _ 0).obj F)
  exact : ∀ T : ShortComplex ((CotangentSites.Site f)ᵒᵖ ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)),
    T.ShortExact → (T.map (fullEvaluation L)).ShortExact
  boundary : FullPreservesBoundary bar L iso exact

/-- The full-site differential comparison on all pure differential tensors.
Source: Stacks 08PU and 08QL (blueprint: lem-trf-cotangent-bar-term-identifications). -/
def FullDifferentialFormula (coh : CotangentResolution.Coherence.{u})
    {A B : CommRingCat.{u}} {f : A ⟶ B} (F : SiteCoefficients f)
    {P : CotangentResolution.Augmentation (Arrow.mk f)} (L : FullResolutionLift P)
    (e : (fullEvaluation L).obj (F.functor ⋙ largeModules B) ≅
      largeDifferentialComplex coh P) : Prop :=
  ∀ (n : ℕ) (b : B)
    (x : (CotangentSites.presentationRing f).obj (L.diagram.obj (op ⦋n⦌))),
    e.hom.f (-(n : ℤ))
      (fullEvaluationElement L (F.functor ⋙ largeModules B) n
        (ULift.up ((F.terms (L.diagram.obj (op ⦋n⦌))).inv
          (tensorD ((CotangentSites.presentationBase f).app (L.diagram.obj (op ⦋n⦌)))
            ((CotangentSites.presentationAugmentation f).app (L.diagram.obj (op ⦋n⦌)))
            b x)))) =
      ULift.up (CotangentResolution.complexGenerator (coh.differentials P) n b
        (L.ringIso.hom.app (op ⦋n⦌) x))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The same cotangent-sheaf model on the full site. Every polynomial resolution
is included, and the normalized differential-tensor formula fixes the comparison.
Source: Stacks 08PS, 08PT, 08PU, 08QI
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
structure FullModel (coh : CotangentResolution.Coherence.{u})
    (bar : CategoryColimitBarSystem.{u + 1}) {A B : CommRingCat.{u}} (f : A ⟶ B)
    (F : SiteCoefficients f) where
  lift : ∀ (P : CotangentResolution.Augmentation (Arrow.mk f)),
    CotangentResolution.IsPolynomialResolution P → FullResolutionLift P
  comparison : ∀ {P : CotangentResolution.Augmentation (Arrow.mk f)}
    (_hP : CotangentResolution.IsPolynomialResolution P) (L : FullResolutionLift P),
    FullResolutionComparison bar L
  differentialIso : ∀ {P : CotangentResolution.Augmentation (Arrow.mk f)}
    (L : FullResolutionLift P),
    (fullEvaluation L).obj (F.functor ⋙ largeModules B) ≅ largeDifferentialComplex coh P
  differential_formula : ∀ {P : CotangentResolution.Augmentation (Arrow.mk f)}
    (L : FullResolutionLift P), FullDifferentialFormula coh F L (differentialIso L)
  agrees : ∀ {P : CotangentResolution.Augmentation (Arrow.mk f)}
    (hP : CotangentResolution.IsPolynomialResolution P) (L : FullResolutionLift P),
    (comparison hP L).iso.hom.app (F.functor ⋙ largeModules B) ≫
      DerivedCategory.Q.map (differentialIso L).hom ≫
      (largeModules B).mapDerivedCategoryFactors.inv.app
        (CotangentResolution.differentialComplex (coh.differentials P)) ≫
      (largeModules B).mapDerivedCategory.map (coh.comparison P hP).hom ≫
      (largeModules B).mapDerivedCategoryFactors.hom.app
        (CotangentResolution.differentialComplex
          (coh.differentials (coh.standard (Arrow.mk f)))) =
    (comparison (coh.standard_resolution (Arrow.mk f))
      (lift (coh.standard (Arrow.mk f)) (coh.standard_resolution (Arrow.mk f)))).iso.hom.app
        (F.functor ⋙ largeModules B) ≫
      DerivedCategory.Q.map (differentialIso
        (lift (coh.standard (Arrow.mk f)) (coh.standard_resolution (Arrow.mk f)))).hom


/-- The canonical full-site theta, evaluated on the standard polynomial resolution.
Source: Stacks 08PT and 08PU (blueprint: lem-trf-cotangent-bar-term-identifications). -/
def fullTheta {coh : CotangentResolution.Coherence.{u}}
    {bar : CategoryColimitBarSystem.{u + 1}} {A B : CommRingCat.{u}} {f : A ⟶ B}
    {F : SiteCoefficients f} (M : FullModel coh bar f F) :
    (fullLowerShriek bar f).obj (F.functor ⋙ largeModules B) ≅
      largeCotangent coh (Arrow.mk f) :=
  (M.comparison (coh.standard_resolution (Arrow.mk f))
      (M.lift (coh.standard (Arrow.mk f)) (coh.standard_resolution (Arrow.mk f)))).iso.app
        (F.functor ⋙ largeModules B) ≪≫
    DerivedCategory.Q.mapIso (M.differentialIso
      (M.lift (coh.standard (Arrow.mk f)) (coh.standard_resolution (Arrow.mk f))))

/-- The normalized cotangent sheaf model also exists on the full polynomial site.
Source: Stacks 08PS, 08PT, 08PU and 08QI
(blueprint: lem-trf-cotangent-bar-term-identifications).

Proof: work directly on the full presentation category. Each term of a
polynomial resolution gives a presentation via its base and augmentation. Maps
from an arbitrary polynomial presentation into that resolution are choices of
lifts of generators. The surjective quasi-isomorphism
boundary-lifting lemma and the trivial Kan homotopy-equivalence lemma make these
simplicial representables contractible, including the empty generator set.
The simplicial derived-colimit computation therefore gives the comparison for
every coefficient presheaf. The ordinary colimit augmentation sends a degree-zero
generator to its colimit inclusion; its derived counit gives normalization.
Evaluation is exact objectwise; naturality of the augmented resolution comparison
with short exact sequences identifies their connecting morphisms. This gives
the boundary law, including the shift isomorphism of derived colimit.
For differential coefficients the universal derivation identifies evaluation
termwise with the differential complex by the displayed formula. Naturality
of the computation and the resolution-coherence comparison give `agrees`.
ULift and scalar restriction along its ring equivalence preserve all these
formulas, finite limits, finite colimits and the alternating differential. -/
theorem fullModel_nonempty (coh : CotangentResolution.Coherence.{u})
    (bar : CategoryColimitBarSystem.{u + 1}) {A B : CommRingCat.{u}} (f : A ⟶ B)
    (F : SiteCoefficients f) : Nonempty (FullModel coh bar f F) := by
  sorry

end Algebra.CotangentSheaf

namespace Algebra.CotangentBarTerms

open CotangentSites CotangentSheaf CotangentDifferentialSequence

/-- The given coefficient-ring map transported by the actual ULift ring equivalences.
Source: Stacks 08Q8, size convention
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
def coefficientMap {B C : CommRingCat.{u}} (g : B ⟶ C) :
    ULift.{u + 1} B →+* ULift.{u + 1} C :=
  RingHom.ulift.{u + 1, u + 1} g.hom

/-- The first pair-site coefficient presheaf in the containing universe.
Precomposition is sectionwise, so this is also the pullback of the extended
coefficient presheaf, definitionally. Source: Stacks 08QX and 08QU
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
def first {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (s : Projections f g) (F : SiteCoefficients f) :=
  firstModule f g s F ⋙ largeModules C

/-- The second pair-site coefficient presheaf in the containing universe.
Source: Stacks 08QX and 08QU
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
def second {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (s : Projections f g) (F : SiteCoefficients (f ≫ g)) :=
  secondModule f g s F ⋙ largeModules C

/-- The third pair-site coefficient presheaf in the containing universe.
Source: Stacks 08QX and 08QU
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
def third {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (s : Projections f g) (F : SiteCoefficients g) :=
  thirdModule f g s F ⋙ largeModules C

/-- The bar complex regarded in the derived category, using the recorded bar system.
Source: Stacks 08PG and 08QX
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
def barObject (bar : CategoryColimitBarSystem.{u + 1})
    {E : Type (u + 1)} [SmallCategory E] {R : Type (u + 1)} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u + 1} R) :=
  DerivedCategory.Q.obj ((bar.models E R).bar.obj F)

/-- The prescribed first composite, expressed after its invertible flat-bar counit.
Source: Stacks 08QX and Sites Cohomology 08Q8
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
def IsFirstComposite {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (coh : CotangentResolution.Coherence.{u}) (bar : CategoryColimitBarSystem.{u + 1})
    (low : LowerShriekData f g bar) (F1 : SiteCoefficients f)
    (m1 : FullModel coh bar f F1)
    (change : CategoryColimitChangeRings bar (Site f) (coefficientMap g))
    (largeFlat : ∀ U : (Site f)ᵒᵖ,
      Module.Flat (ULift.{u + 1} B) ((F1.functor ⋙ largeModules B).obj U))
    (scalarTransport : ModuleCat.extendScalars g.hom ⋙ largeModules C ≅
      largeModules B ⋙ ModuleCat.extendScalars (coefficientMap g))
    (alpha1 : barObject bar (first f g low.sites F1) ≅
      change.point.functor.obj (largeCotangent coh (Arrow.mk f))) : Prop :=
  alpha1.hom ≫ change.point.functor.map (fullTheta m1).inv ≫
      change.point.functor.map
        ((bar.models (Site f) (ULift.{u + 1} B)).model.hom.app
          (F1.functor ⋙ largeModules B)) ≫
      change.point.counit.app
        ((bar.models (Site f) (ULift.{u + 1} B)).bar.obj (F1.functor ⋙ largeModules B)) =
    DerivedCategory.Q.map ((bar.models (PairSite f g) (ULift.{u + 1} C)).bar.map
      (Functor.whiskerLeft (low.sites.projection 0).op
        (Functor.whiskerLeft F1.functor scalarTransport.hom))) ≫
      (bar.models (PairSite f g) (ULift.{u + 1} C)).model.inv.app
        ((low.sites.projection 0).op ⋙
          (categoryBarExtend (coefficientMap g)).obj (F1.functor ⋙ largeModules B)) ≫
      (low.comparison (ULift.{u + 1} C) 0).app
        ((categoryBarExtend (coefficientMap g)).obj (F1.functor ⋙ largeModules B)) ≫
      (bar.models (Site f) (ULift.{u + 1} C)).model.hom.app
        ((categoryBarExtend (coefficientMap g)).obj (F1.functor ⋙ largeModules B)) ≫
      DerivedCategory.Q.map (change.barIso (F1.functor ⋙ largeModules B) largeFlat).hom

/-- Every clause of the three canonical term identifications. `IsFirstComposite` is the
composite formula after composing with the invertible flat-bar computation counit;
this states the formula without selecting any inverse or any additional comparison.
The final existential fixes the standard-complex representative by its actual
universal derived-to-ordinary counit. Tensor factors use the symmetric convention
`C ⊗_B M` throughout, as in the recorded coefficient and change-of-rings models.
Source: Stacks 08QX, 08QW, 08PU, 08PN; Sites Cohomology 08Q8 and 06YQ
(blueprint: lem-trf-cotangent-bar-term-identifications). -/
def Identifications {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (coh : CotangentResolution.Coherence.{u}) (bar : CategoryColimitBarSystem.{u + 1})
    (low : LowerShriekData f g bar)
    (F1 : SiteCoefficients f) (F2 : SiteCoefficients (f ≫ g)) (F3 : SiteCoefficients g)
    (m1 : FullModel coh bar f F1) (m2 : FullModel coh bar (f ≫ g) F2)
    (m3 : FullModel coh bar g F3)
    (change : CategoryColimitChangeRings bar (Site f) (coefficientMap g)) : Prop :=
  -- free
  (∀ U : (Site f)ᵒᵖ, Module.Free B (F1.functor.obj U)) ∧
  -- flat
  (∀ U : (Site f)ᵒᵖ, Module.Flat B (F1.functor.obj U)) ∧
  -- coordinates
  (∀ (U : (Site f)ᵒᵖ) (S : Type u)
    (e : CommRingCat.of (MvPolynomial S A) ≅ (presentationRing f).obj U),
    CommRingCat.ofHom MvPolynomial.C ≫ e.hom = (presentationBase f).app U →
    ∃ b : F1.functor.obj U ≅ ModuleCat.of B (S →₀ B),
      ∀ (s : S) (c : B),
        b.hom ((F1.terms U).inv
          (tensorD ((presentationBase f).app U) ((presentationAugmentation f).app U)
            c (e.hom (MvPolynomial.X s)))) = Finsupp.single s c) ∧
  -- tensor_exact
  (∀ (U : (Site f)ᵒᵖ) (T : ShortComplex (ModuleCat.{u} B)),
    T.ShortExact →
      (T.map ((MonoidalCategory.curriedTensor (ModuleCat.{u} B)).obj
        (F1.functor.obj U))).ShortExact) ∧
  ∃ (largeFlat : ∀ U : (Site f)ᵒᵖ,
    Module.Flat (ULift.{u + 1} B) ((F1.functor ⋙ largeModules B).obj U)),
  ∃ (scalarTransport : ModuleCat.extendScalars g.hom ⋙ largeModules C ≅
    largeModules B ⋙ ModuleCat.extendScalars (coefficientMap g)),
  -- scalar_formula
  (∀ (M : ModuleCat.{u} B) (c : C) (x : M),
    scalarTransport.hom.app M (ULift.up (c ⊗ₜ[B, g.hom] x)) =
      ULift.up c ⊗ₜ[ULift.{u + 1} B, (coefficientMap g)] ULift.up x) ∧
  ∃ (alpha1 : barObject bar (first f g low.sites F1) ≅
    change.point.functor.obj (largeCotangent coh (Arrow.mk f))),
  ∃ (alpha2 : barObject bar (second f g low.sites F2) ≅
    largeCotangent coh (Arrow.mk (f ≫ g))),
  ∃ (alpha3 : barObject bar (third f g low.sites F3) ≅
    largeCotangent coh (Arrow.mk g)),
  -- alpha2_eq
  (alpha2.hom =
    (bar.models (PairSite f g) (ULift.{u + 1} C)).model.inv.app
        (second f g low.sites F2) ≫
      (low.comparison (ULift.{u + 1} C) 1).app (F2.functor ⋙ largeModules C) ≫
        (fullTheta m2).hom) ∧
  -- alpha3_eq
  (alpha3.hom =
    (bar.models (PairSite f g) (ULift.{u + 1} C)).model.inv.app
        (third f g low.sites F3) ≫
      (low.comparison (ULift.{u + 1} C) 2).app (F3.functor ⋙ largeModules C) ≫
        (fullTheta m3).hom) ∧
  -- alpha1_eq
  (IsFirstComposite f g coh bar low F1 m1 change largeFlat scalarTransport alpha1) ∧
  -- middle_formula
  (∀ (n : ℕ) (c : ComposableArrows (Site f) n)
    (x : (F1.functor ⋙ largeModules B).obj (op c.right)) (z : ULift.{u + 1} C),
    (change.barIso (F1.functor ⋙ largeModules B) largeFlat).hom.f (-(n : ℤ))
      ((bar.models (Site f) (ULift.{u + 1} C)).generator
        ((categoryBarExtend (coefficientMap g)).obj (F1.functor ⋙ largeModules B)) n c
        (z ⊗ₜ[ULift.{u + 1} B, (coefficientMap g)] x)) =
      z ⊗ₜ[ULift.{u + 1} B, (coefficientMap g)]
        ((bar.models (Site f) (ULift.{u + 1} B)).generator
          (F1.functor ⋙ largeModules B) n c x)) ∧
  -- standard_bound
  (CochainComplex.IsStrictlyLE
      (largeDifferentialComplex coh (coh.standard (Arrow.mk f))) 0) ∧
  -- standard_free
  (∀ q : ℤ, Module.Free (ULift.{u + 1} B)
    ((largeDifferentialComplex coh (coh.standard (Arrow.mk f))).X q)) ∧
  -- standard_flat
  (∀ q : ℤ, Module.Flat (ULift.{u + 1} B)
    ((largeDifferentialComplex coh (coh.standard (Arrow.mk f))).X q)) ∧
  -- standard_representation
  (∃ e :
      change.point.functor.obj (largeCotangent coh (Arrow.mk f)) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (coefficientMap g)).mapHomologicalComplex (.up ℤ)).obj
            (largeDifferentialComplex coh (coh.standard (Arrow.mk f)))),
    e.hom = change.point.counit.app
      (largeDifferentialComplex coh (coh.standard (Arrow.mk f))))

/-- The three bar terms have the specified canonical cotangent identifications,
including freeness, flatness, all comparison formulas, and the standard tensor model.
There is no flatness hypothesis on `g`. Source: Stacks 08QX, 08QW, 08PU, 08PN;
Sites Cohomology 08Q8 and 06YQ
(blueprint: lem-trf-cotangent-bar-term-identifications).

Proof:
1. For each polynomial presentation P = A[S], the polynomial Kahler basis followed
   by extension of scalars gives the basis dx_s of F1(P). Tensoring a short exact
   sequence gives its direct sum indexed by S; injectivity, kernels and surjectivity
   hold coordinatewise on finite supports. This proves free, flat, coordinates and
   tensor_exact, for arbitrary and empty S. Actual ULift transport gives largeFlat
   and scalarTransport, whose pure tensor formula is scalar_formula.
2. Precomposition is sectionwise: firstModule is literally the pullback of F1
   extended by C. The lower-shriek theorem gives the bar reindexing comparisons;
   its represented equation fixes each map on chains and coefficients.
3. Compose the bar model inverse, c2 or c3 and the full-site sheaf-model theta.
   This gives alpha2 and alpha3 with exactly the displayed equalities.
4. For the first term transport coefficient universes by scalarTransport, apply
   c1 to the extended presheaf, then the flat-presheaf comparison of
   lem-trf-derived-colimit-change-rings, then derived extension of theta1.
   Its flatBar computation counit is invertible. Composing with this counit gives
   alpha1_eq. The change-of-rings generator formula gives middle_formula verbatim.
   No step uses flatness of C over B.
5. Resolution coherence represents L[B/A] by the standard differential complex,
   zero in positive degrees. Every nonpositive term is a polynomial differential
   module, free by the arbitrary-variable polynomial Kahler basis. Zero terms are
   free too. Thus standard_bound, standard_free and standard_flat hold after ULift.
   On the one-point site, lem-trf-one-point-derived-ring-identification identifies
   tensor, K-flatness and the universal change-of-rings pair with ordinary modules.
   Apply lem-weil-pbc-independent-bounded-flat-kflat there: the standard complex
   is K-flat. Clause (2) of lem-pur-derived-change-of-rings computes the derived
   tensor on this identity resolution by its actual termwise scalar extension.
   Uniqueness of the universal counit identifies that computation with
   change.point.counit, giving exactly standard_representation. -/
theorem identifications_nonempty {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (coh : CotangentResolution.Coherence.{u}) (bar : CategoryColimitBarSystem.{u + 1})
    (low : LowerShriekData f g bar)
    (F1 : SiteCoefficients f) (F2 : SiteCoefficients (f ≫ g)) (F3 : SiteCoefficients g)
    (m1 : FullModel coh bar f F1) (m2 : FullModel coh bar (f ≫ g) F2)
    (m3 : FullModel coh bar g F3)
    (change : CategoryColimitChangeRings bar (Site f) (coefficientMap g)) :
    Identifications f g coh bar low F1 F2 F3 m1 m2 m3 change := by
  sorry

end Algebra.CotangentBarTerms
