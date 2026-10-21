module
public import Sheaf.Topology.TopologicalModuleCondensation
public import Sheaf.Paper.ProfiniteConstantDerivedFunctions
public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.RingTheory.TensorProduct.Finite
public import Sheaf.CategoryTheory.CondensedEquivariantBarData

/-!
# Canonical derived evaluation of profinite internal functions

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
agent expansion of the tame-boundary calculation.
(blueprint: def-sfb-derived-profinite-evaluation).

All coefficients retain every continuous function, including for incomplete algebraic closures.
All derived categories are ordinary and unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false

-- Keep the canonical sheaf tensor instance used by the pre-existing geometric APIs.
attribute [-instance] AlgebraicGeometry.ProEtale.ProfiniteFunctions.condensedSheafMonoidal
  AlgebraicGeometry.ProEtale.ProfiniteFunctions.schemeSheafMonoidal
  AlgebraicGeometry.ProEtale.ProfiniteFunctions.pointAbelian_braided
  AlgebraicGeometry.ProEtale.ProfiniteFunctions.pointPull_monoidal
  AlgebraicGeometry.ProEtale.ProfiniteFunctions.continuousPresheafRingMonObj
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.RootBoundary
variable (F : Type u) [NormedField F]
/-- The all-continuous condensed coefficient ring, with no completion or finite-stage restriction.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev coefficients := Profinite.continuousCoefficientRingObj F
/-- Internal modules on the profinite point in the coefficient universe.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev PointMod := Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (coefficients F)
/-- Internal modules over the pulled-back coefficient ring on the small pro-etale site.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev SiteMod (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (coefficients F) X)
/-- The recorded pullback from the profinite point on internal modules.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev pointPull (X : Scheme.{u}) : PointMod F ⥤ SiteMod F X :=
  (upperStarFromPoint X).mapMod (coefficients F)
/-- Exactness of point pullback: preservation of finite limits.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
instance pointPull_limits (X : Scheme.{u}) : PreservesFiniteLimits (pointPull F X) := by
  have : PreservesFiniteLimits pointUpperStar.{u} :=
    profinite_point_pullback.2.2.2.2.2.2.2.2.1
  change PreservesFiniteLimits ((upperStarFromPoint X).mapMod (coefficients F))
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  infer_instance
/-- Exactness of point pullback: preservation of finite colimits.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
instance pointPull_colimits (X : Scheme.{u}) : PreservesFiniteColimits (pointPull F X) := by
  have : PreservesFiniteColimits pointUpperStar.{u} :=
    profinite_point_pullback.2.2.2.2.2.2.2.2.2.1
  change PreservesFiniteColimits ((upperStarFromPoint X).mapMod (coefficients F))
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  infer_instance
/-- Additivity of point pullback.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
instance pointPull_additive (X : Scheme.{u}) : (pointPull F X).Additive := by
  change ((upperStarFromPoint X).mapMod (coefficients F)).Additive
  exact Functor.additive_of_preserves_binary_products _
set_option backward.isDefEq.respectTransparency false in
/-- The strong monoidal structure induced by the recorded point pullback.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
instance pointPull_monoidal (X : Scheme.{u}) : (pointPull F X).Monoidal := by
  letI : (upperStarFromPoint X).Braided :=
    { toMonoidal := { monoidal_upperStarFromPoint X with
        toLaxMonoidal := (laxBraided_upperStarFromPoint X).toLaxMonoidal },
      braided := (laxBraided_upperStarFromPoint X).braided }
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    have : PreservesFiniteColimits pointUpperStar.{u} :=
      profinite_point_pullback.2.2.2.2.2.2.2.2.2.1
    unfold upperStarFromPoint
    infer_instance
  change ((upperStarFromPoint X).mapMod (coefficients F)).Monoidal
  exact Functor.monoidal_mapMod (upperStarFromPoint X) (R := coefficients F)
/-- Exact point pullback on ordinary unbounded derived categories.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev pointPullD (X : Scheme.{u}) : DerivedCategory (PointMod F) ⥤
    DerivedCategory (SiteMod F X) := (pointPull F X).mapDerivedCategory
/-- The existing commutative ring object, bundled for the free-module interface.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev bundledCoefficients : CategoryTheory.CondensedBar.Ring.{u} :=
  { X := coefficients F }
/-- The existing free internal module on the represented profinite parameter.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev freeParameter (P : Profinite.{u}) : PointMod F :=
  CategoryTheory.CondensedBar.freeParameter (bundledCoefficients F) P
/-- Internal Hom from the free parameter, right derived in its second variable.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def parameterFunctions (P : Profinite.{u}) :
    DerivedCategory (PointMod F) ⥤ DerivedCategory (PointMod F) :=
  (ihom (freeParameter F P)).rightDerivedFunctor
/-- The continuous-functions condensation functor with its recorded sectionwise characterization.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def condensation : TopModuleCat.{u} F ⥤ PointMod F :=
  (Profinite.topologicalModule_condensation F).choose
variable (E M : Type u) [CommRing E] [Algebra E F] [AddCommGroup M] [Module E M]
/-- The tensor coefficient module with its canonical module topology; in finite dimension this is
the finite product norm topology, including when the coefficient field is incomplete.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def tensorModule : TopModuleCat.{u} F := by
  letI := moduleTopology F (F ⊗[E] M)
  letI := ModuleTopology.continuousSMul F (F ⊗[E] M)
  letI := ModuleTopology.continuousAdd F (F ⊗[E] M)
  exact TopModuleCat.of F (F ⊗[E] M)
/-- The condensed module of all continuous functions into the tensor coefficient module.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def model : PointMod F := (condensation F).obj (tensorModule F E M)
/-- The exact recorded inverse image on unbounded derived module categories.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev pullD {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (SiteMod F Y) ⥤ DerivedCategory (SiteMod F X) :=
  (CondensedRing.upperStar (coefficients F) f).mapDerivedCategory
/-- The recorded total right-derived direct image on unbounded module categories.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
abbrev pushD {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (SiteMod F X) ⥤ DerivedCategory (SiteMod F Y) :=
  CondensedRing.moduleObjectDerivedPushforward (coefficients F) f
/-- The recorded derived adjunction with its exact left adjoint.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def derivedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullD F f ⊣ pushD F f :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction (coefficients F) f).ofNatIsoLeft
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (coefficients F) f)
/-- Direct image preserves K-injectives because its left adjoint is exact.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
instance push_preservesKInjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar (coefficients F) f).PreservesKInjectiveComplexes :=
  (CondensedRing.upperStarLowerStarAdjunction (coefficients F) f).preservesKInjectiveComplexes
/-- The canonical comparison for composition of derived direct images on K-injectives.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def pushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushD F f ⋙ pushD F g ≅ pushD F (f ≫ g) :=
  Functor.rightDerivedFunctorCompIso' _ _
    (CondensedRing.lowerStarComp (coefficients F) f g)
/-- The canonical composition isomorphism for exact derived inverse images.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullD F (f ≫ g) ≅ pullD F g ⋙ pullD F f :=
  (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp (coefficients F) f g)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The composite inverse-image/direct-image adjunction from the profinite point.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def pointAbAdjunction (X : Scheme.{u}) :
    upperStarFromPoint X ⊣ (ProEtale.lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar) :=
  pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
/-- The universal parameter section corresponding to the identity of the represented profinite set.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def generator (P : Profinite.{u}) : (freeParameter F P).X.obj.obj (op P) :=
  ((((Sheaf.adjunction (coherentTopology Profinite.{u}) AddCommGrpCat.adj.{u + 1}).comp
    (Mod.freeForgetAdjunction (C := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (coefficients F))).unit.app
      ((GrothendieckTopology.uliftYoneda.{u + 1} (coherentTopology Profinite.{u})).obj P)).hom.app
        (op P)) (ULift.up (𝟙 P))
/-- The actual diagonal into the test object after base change to that test object.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def tautologicalDiagonal (X : Scheme.{u}) (P : Profinite.{u}) :
    Scheme.ProEt.mk (𝟙 ((profiniteToProEtOf X).obj P).left) ⟶
      (profiniteToProEtOf ((profiniteToProEtOf X).obj P).left).obj P :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst _ _) (𝟙 _)
      (by rw [Category.id_comp]; exact specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)
/-- The universal parameter generator pulled back and restricted along the actual diagonal.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def tautologicalSection (X : Scheme.{u}) (P : Profinite.{u}) :
    ((pointPull F ((profiniteToProEtOf X).obj P).left).obj (freeParameter F P)).X.obj.obj
      (op (Scheme.ProEt.mk (𝟙 ((profiniteToProEtOf X).obj P).left))) :=
  (((pointPull F ((profiniteToProEtOf X).obj P).left).obj (freeParameter F P)).X.obj.map
    (tautologicalDiagonal X P).op)
    (((pointAbAdjunction ((profiniteToProEtOf X).obj P).left).unit.app
      (freeParameter F P).X).hom.app (op P) (generator F P))
/-- The identity object is terminal in the small pro-etale site.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def terminalObject (X : Scheme.{u}) : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom (fun V ↦ MorphismProperty.Over.homMk V.hom)
    (fun V f ↦ MorphismProperty.Over.Hom.ext (by
      change f.left = V.hom
      rw [← MorphismProperty.Over.w f]
      exact (Category.comp_id _).symm))
/-- The regular-module arrow corresponding to the tautological global section.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def tautologicalElement (X : Scheme.{u}) (P : Profinite.{u}) :
    Mod.regular (condensedRingObj (coefficients F) ((profiniteToProEtOf X).obj P).left) ⟶
      (pointPull F ((profiniteToProEtOf X).obj P).left).obj (freeParameter F P) :=
  Mod.regularLift _
    ((((constantSheafAdj (Scheme.ProEt.topology ((profiniteToProEtOf X).obj P).left)
      Ab.{u + 1} (terminalObject ((profiniteToProEtOf X).obj P).left)).homAddEquiv _ _).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _)).symm (tautologicalSection F X P))
open MonoidalCategory in
/-- Evaluation of an internal function at the universal parameter, using tensor-Hom evaluation.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def evaluation (X : Scheme.{u}) (P : Profinite.{u}) (M : PointMod F) :
    (pointPull F ((profiniteToProEtOf X).obj P).left).obj ((ihom (freeParameter F P)).obj M)
      ⟶ (pointPull F ((profiniteToProEtOf X).obj P).left).obj M :=
  (ρ_ _).inv ≫
    (𝟙 _ ⊗ₘ tautologicalElement F X P) ≫
    Functor.LaxMonoidal.μ (pointPull F ((profiniteToProEtOf X).obj P).left) _ _ ≫
    (pointPull F ((profiniteToProEtOf X).obj P).left).map
      ((β_ _ (freeParameter F P)).hom ≫
        (ihom.ev (freeParameter F P)).app M)
/-- The canonical identification of composite point pullback on ordinary internal modules.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def pointPullComp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pointPull F Y ⋙ CondensedRing.upperStar (coefficients F) f ≅ pointPull F X :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapModCompIso (upperStarFromPoint Y) (ProEtale.upperStar Ab.{u + 1} f)
        (upperStarFromPointComp f).hom (coefficients F)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom (coefficients F) f)) ≪≫
      (Mod.comapEquivalenceOfIsIso (condensedPullbackHom (coefficients F) f)).unitIso.symm) ≪≫
    Functor.rightUnitor _
/-- The direct-image adjunct of evaluation at the tautological parameter.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def parameterEvaluation (X : Scheme.{u}) (P : Profinite.{u}) (M : PointMod F) :
    (pointPull F X).obj ((ihom (freeParameter F P)).obj M) ⟶
      (CondensedRing.lowerStar (coefficients F) ((profiniteToProEtOf X).obj P).hom).obj
        ((pointPull F ((profiniteToProEtOf X).obj P).left).obj M) :=
  (CondensedRing.upperStarLowerStarAdjunction (coefficients F)
    ((profiniteToProEtOf X).obj P).hom).homEquiv _ _
      ((pointPullComp F ((profiniteToProEtOf X).obj P).hom).hom.app _ ≫ evaluation F X P M)
/-- Naturality of the actual evaluation adjunct in the coefficient module.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation).

Proof: Internal tensor-Hom evaluation is natural in its value module. Whisker this
identity by exact point pullback and precompose with the tautological-element arrow.
The adjunction hom-equivalence is natural in its target; applying that naturality
gives precisely the displayed equality of adjuncts. -/
theorem evaluation_naturality (X : Scheme.{u}) (P : Profinite.{u})
    {M N : PointMod F} (f : M ⟶ N) :
    (pointPull F X).map ((ihom (freeParameter F P)).map f) ≫ parameterEvaluation F X P N =
      parameterEvaluation F X P M ≫
        (CondensedRing.lowerStar (coefficients F) ((profiniteToProEtOf X).obj P).hom).map
          ((pointPull F ((profiniteToProEtOf X).obj P).left).map f) := by
  sorry
/-- The natural transformation assembled from the actual evaluation adjuncts.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def evaluationTransformation (X : Scheme.{u}) (P : Profinite.{u}) :
    ihom (freeParameter F P) ⋙ pointPull F X ⟶
      pointPull F ((profiniteToProEtOf X).obj P).left ⋙
        CondensedRing.lowerStar (coefficients F) ((profiniteToProEtOf X).obj P).hom where
  app := parameterEvaluation F X P
  naturality _ _ f := evaluation_naturality F X P f
/-- The recorded canonical derived evaluation-adjoint transformation, specialized to C_F.
Its existing definition derives evaluation at the universal parameter and transposes by
rho_P pullback adjunction. No second comparison or arbitrary isomorphism is constructed.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def derivedEvaluation (X : Scheme.{u}) (P : Profinite.{u}) :
    parameterFunctions F P ⋙ pointPullD F X ⟶
      pointPullD F ((profiniteToProEtOf X).obj P).left ⋙
        pushD F ((profiniteToProEtOf X).obj P).hom :=
  ProfiniteFunctions.comparison (Mon.mk (coefficients F)) X P
/-- The covariant map of free internal modules induced by a continuous parameter map.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def freeParameterMap {P Q : Profinite.{u}} (f : P ⟶ Q) : freeParameter F P ⟶ freeParameter F Q :=
  (Sheaf.composeAndSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.free.{u + 1} ⋙
    Mod.free (coefficients F)).map
      ((GrothendieckTopology.uliftYoneda.{u + 1} (coherentTopology Profinite.{u})).map f)
/-- The contravariant derived internal-functions map induced by a parameter map.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def parameterFunctionsMap {P Q : Profinite.{u}} (f : P ⟶ Q) :
    parameterFunctions F Q ⟶ parameterFunctions F P :=
  Functor.rightDerivedFunctorNatTrans (MonoidalClosed.pre (freeParameterMap F f))
/-- Restriction of derived sections, given by the inverse-image adjunction unit and
the canonical direct-image composition comparison.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-derived-profinite-evaluation). -/
def sectionRestriction {X' X Y : Scheme.{u}} (a : X' ⟶ X) (q : X ⟶ Y)
    (K : DerivedCategory (SiteMod F X)) :
    (pushD F q).obj K ⟶ (pushD F (a ≫ q)).obj ((pullD F a).obj K) :=
  (pushD F q).map ((derivedAdjunction F a).unit.app K) ≫
    (pushComp F a q).hom.app ((pullD F a).obj K)
end AlgebraicGeometry.ProEtale.RootBoundary
