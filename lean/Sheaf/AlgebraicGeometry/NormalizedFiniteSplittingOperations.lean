module

public import Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedDescent
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Operations on normalized finite splittings

Source: Bhatt--Scholze Section 5.1, pp. 34--35, and the agent-formulated
finite-operation and pointed-refinement consequences of normalized descent
(blueprint: lem-sfb-normalized-finite-splitting-operations).

The universal sections and their normalization are the existing connected-cover
interfaces, specialized to a single cover. No inverse system is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.ProEtale

/-- The finite-constant subcategory for this cover, using the existing predicate.
Source: Bhatt--Scholze 5.1 (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
abbrev finiteSplittingObjects {U : Scheme.{u}} (W : U.ProEt) :
    ObjectProperty (Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) :=
  fun F ↦ abelianTowerConstantAt F W

/-- The stalk functor on the full finite-constant subcategory.
Source: Stacks 0F6B (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
abbrev finiteSplittingStalk {U : Scheme.{u}} (W : U.ProEt) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ W.left) :
    (finiteSplittingObjects W).FullSubcategory ⥤ Type (u + 1) :=
  ObjectProperty.ι (finiteSplittingObjects W) ⋙
    sheafToPresheaf (Scheme.ProEt.topology U) (Type (u + 1)) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ W.hom)).op ⋙ colim

/-- Exactly the supplied hypotheses: one connected covering torsor and its unique,
natural, fibre-normalized splittings. The descent equality is on the entire object
X[G times Q]; it includes variable group parameters and variable finite labels.
Source: Bhatt--Scholze 5.1 and the node's normalized-descent hypotheses
(blueprint: lem-sfb-normalized-finite-splitting-operations). -/
structure NormalizedFiniteSplittings {U : Scheme.{u}} (W : U.ProEt) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ W.left) (G : ProfiniteGrp.{u}) where
  connected : ConnectedSpace W.left
  cover : Presieve.singleton W.hom ∈ Scheme.proetalePrecoverage U
  commutative : ∀ g h : G, g * h = h * g
  action : G →* End W
  comparison : Scheme.UniversalCover.profiniteProduct W.left
    ((forget₂ ProfiniteGrp Profinite).obj G) ≅ pullback W.hom W.hom
  comparison_fst : comparison.hom ≫ pullback.fst _ _ =
    Scheme.UniversalCover.profiniteProductBase _ _
  comparison_action : ∀ g : G,
    Scheme.UniversalCover.profiniteProductSection _ _ g ≫
      comparison.hom ≫ pullback.snd _ _ = (action g).left
  fibre : (finiteSplittingObjects W).FullSubcategory ⥤ ContAction FintypeCat.{u} G
  fibreIso : fibre ⋙ forget₂ _ FintypeCat ⋙ forget FintypeCat ⋙ uliftFunctor.{u + 1, u} ≅
    finiteSplittingStalk W z
  splitting : ∀ F : (finiteSplittingObjects W).FullSubcategory,
    F.obj.obj.obj (op ((abelianTowerLabels W).obj
      (FintypeCat.toProfinite.obj (fibre.obj F).obj.V)))
  normalized : ∀ F,
    IsAbelianTowerNormalizedSection W (Over.homMk z) F.obj (fibre.obj F).obj.V
      (Equiv.ofBijective (fun q ↦ fibreIso.hom.app F q)
        (ConcreteCategory.bijective_of_isIso (fibreIso.hom.app F))) (splitting F)
  unique : ∀ F s,
    IsAbelianTowerNormalizedSection W (Over.homMk z) F.obj (fibre.obj F).obj.V
      (Equiv.ofBijective (fun q ↦ fibreIso.hom.app F q)
        (ConcreteCategory.bijective_of_isIso (fibreIso.hom.app F))) s → s = splitting F
  natural : ∀ (F F' : (finiteSplittingObjects W).FullSubcategory) (f : F ⟶ F'),
    F'.obj.obj.map ((abelianTowerLabels W).map
      (FintypeCat.toProfinite.map ((forget₂ _ FintypeCat).map (fibre.map f)))).op
        (splitting F') = f.hom.hom.app _ (splitting F)
  actionLabels : ∀ F : (finiteSplittingObjects W).FullSubcategory,
    Profinite.of (G × FintypeCat.toProfinite.obj (fibre.obj F).obj.V) ⟶
      FintypeCat.toProfinite.obj (fibre.obj F).obj.V
  actionLabels_apply : ∀ F (g : G) (q : (fibre.obj F).obj.V),
    actionLabels F (g, q) = ConcreteCategory.hom ((fibre.obj F).obj.ρ g) q
  descentLabel : ∀ F : (finiteSplittingObjects W).FullSubcategory,
    (abelianTowerLabels W).obj
      (Profinite.of (G × FintypeCat.toProfinite.obj (fibre.obj F).obj.V)) ⟶
        (abelianTowerLabels W).obj (FintypeCat.toProfinite.obj (fibre.obj F).obj.V)
  descentLabel_base : ∀ F,
    (descentLabel F).left ≫ Scheme.UniversalCover.profiniteProductBase _ _ =
      ((abelianTowerLabels W).map
        (ConcreteCategory.ofHom ⟨Prod.fst, continuous_fst⟩)).left ≫
          comparison.hom ≫ pullback.snd _ _
  descentLabel_label : ∀ F,
    (descentLabel F).left ≫ pullback.fst _ _ =
      ((abelianTowerLabels W).map
        (ConcreteCategory.ofHom ⟨Prod.snd, continuous_snd⟩)).left ≫ pullback.fst _ _
  descent : ∀ F : (finiteSplittingObjects W).FullSubcategory,
    F.obj.obj.map ((abelianTowerLabels W).map (actionLabels F)).op (splitting F) =
      F.obj.obj.map (descentLabel F).op (splitting F)

variable {U : Scheme.{u}} {W : U.ProEt} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {z : Spec (.of Ω) ⟶ W.left} {G : ProfiniteGrp.{u}}

/-- Relabelling finite copies by an arbitrary map of finite sets.
Source: Bhatt--Scholze 5.1 (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
def finiteSplittingLabelMap {A B : FintypeCat.{u}} (f : A → B) :
    FintypeCat.toProfinite.obj A ⟶ FintypeCat.toProfinite.obj B :=
  FintypeCat.toProfinite.map (FintypeCat.homMk f)

/-- Underlying finite object of a left module sheaf; coefficients need not commute.
Source: Stacks 03CZ (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
abbrev finiteSplittingModuleObject (R : Type (u + 1)) [Ring R]
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
    (hM : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M)) :
    (finiteSplittingObjects W).FullSubcategory := ⟨_, hM⟩

/-- Normalized finite labels in the actual module stalk, defined by their germs.
Source: Stacks 0F6B (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
def NormalizedFiniteSplittings.moduleLabel (D : NormalizedFiniteSplittings W z G)
    {R : Type (u + 1)} [Ring R]
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
    (hM : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M))
    (q : (D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V) :
    Scheme.proEtaleGeometricStalk (C := ModuleCat.{u + 1} R) (z ≫ W.hom) M :=
  (colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ W.hom) M)
    (op (abelianTowerLabelNeighbourhood W (Over.homMk z) _ q)))
      (D.splitting (finiteSplittingModuleObject R M hM))

/-- The linear stalk action is fixed on every normalized finite label.
Source: Bhatt--Scholze 5.1 (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
structure FiniteSplittingModuleAction (D : NormalizedFiniteSplittings W z G)
    {R : Type (u + 1)} [Ring R]
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
    (hM : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M)) where
  action : G →* End (Scheme.proEtaleGeometricStalk (C := ModuleCat.{u + 1} R) (z ≫ W.hom) M)
  normalized : ∀ g q,
    ConcreteCategory.hom (action g) (D.moduleLabel M hM q) =
      D.moduleLabel M hM
        (ConcreteCategory.hom ((D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.ρ g) q)

/-- Finite products, including the empty product, are preserved by the inclusion and
by normalized fibre labels. Naturality with projections is the given `natural`
equation, so this also identifies the product and terminal splitting maps.
Source: Bhatt--Scholze 5.1, finite-operation consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations).
Proof: Steps 1--2. Inverse image and set sheafification preserve finite products.
Filtered stalk colimits commute with finite products. The product splitting is
normalized at z, hence uniqueness identifies it with the supplied splitting.
For an empty family the unique map to the terminal object gives the same result. -/
theorem normalizedFiniteSplittings_products (D : NormalizedFiniteSplittings W z G) :
    HasFiniteProducts (finiteSplittingObjects W).FullSubcategory ∧
      PreservesFiniteProducts (ObjectProperty.ι (finiteSplittingObjects W)) ∧
      PreservesFiniteProducts D.fibre := by
  classical
  let P := finiteSplittingObjects W
  let L := Scheme.proEtaleSheafInverseImage W.hom (Type (u + 1))
  have : PreservesFiniteLimits L :=
    (toposFunctorialityInverseImage W.hom (𝟙 U)).2.2.2.1
  let C := forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ⋙
    constantSheaf (Scheme.ProEt.topology W.left) (Type (u + 1))
  have : PreservesFiniteLimits C := by
    dsimp [C, constantSheaf]
    infer_instance
  have : P.IsClosedUnderIsomorphisms := ⟨by
    intro F F' e hF
    obtain ⟨A, ⟨i⟩⟩ := hF
    exact ⟨A, ⟨L.mapIso e.symm ≪≫ i⟩⟩⟩
  have : P.IsClosedUnderFiniteProducts :=
    .of_isClosedUnderLimitsOfShape (fun (J : Type) _ ↦ by
      apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
      rintro _ ⟨F, hF⟩
      choose A hA using hF
      let K : Discrete J ⥤ FintypeCat.{u} := Discrete.functor (fun j ↦ A ⟨j⟩)
      let e : K ⋙ C ≅ F ⋙ L := Discrete.natIso (fun j ↦ (hA j).some.symm)
      exact ⟨limit K, ⟨preservesLimitIso L F ≪≫
        (HasLimit.isoOfNatIso e).symm ≪≫ (preservesLimitIso C K).symm⟩⟩)
  have : HasFiniteProducts P.FullSubcategory := inferInstance
  have : PreservesFiniteProducts P.ι := ⟨fun _ ↦ inferInstance⟩
  refine ⟨inferInstance, inferInstance, ⟨fun n ↦ ?_⟩⟩
  let H := forget₂ (ContAction FintypeCat.{u} G) FintypeCat ⋙
    forget FintypeCat ⋙ uliftFunctor.{u + 1, u}
  have : ReflectsLimitsOfShape (Discrete (Fin n)) H := by
    change ReflectsLimitsOfShape (Discrete (Fin n))
      (ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) ⋙
        Action.forget FintypeCat G ⋙ forget FintypeCat ⋙ uliftFunctor.{u + 1, u})
    infer_instance
  have : PreservesLimitsOfShape (Discrete (Fin n)) (finiteSplittingStalk W z) := by
    dsimp [finiteSplittingStalk]
    infer_instance
  have : PreservesLimitsOfShape (Discrete (Fin n)) (D.fibre ⋙ H) :=
    preservesLimitsOfShape_of_natIso D.fibreIso.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves D.fibre H

/-- Normalized splittings respect all left-module operations on local sections.
The equations are on universal finite labelled test objects, and therefore on all
sections after arbitrary restriction, by `D.normalized`'s bijectivity clause.
Source: Bhatt--Scholze 5.1, finite-module consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations).
Proof: Step 3. The stalk is the module colimit. Forgetting preserves its filtered
colimit, so moduleLabel is bijective. Transport the module operations to its finite
labels. Naturality for zero, addition, negation and each scalar map identifies
those universal sections, using the product comparison of Steps 1--2. Apply the
same naturality to the full descent arrow: its permutations preserve every
operation, hence give the asserted linear action. -/
theorem normalizedFiniteSplittings_module (D : NormalizedFiniteSplittings W z G)
    (R : Type (u + 1)) [Ring R] [Finite R]
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
    (hM : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M)) :
    ∃ e : (D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V ≃
        Scheme.proEtaleGeometricStalk (C := ModuleCat.{u + 1} R) (z ≫ W.hom) M,
      (∀ q, e q = D.moduleLabel M hM q) ∧
      Nonempty (FiniteSplittingModuleAction D M hM) ∧
      (M.obj.map ((abelianTowerLabels W).map
        (finiteSplittingLabelMap (A := FintypeCat.of PUnit)
          (fun _ ↦ e.symm 0))).op (D.splitting (finiteSplittingModuleObject R M hM)) = 0) ∧
      (M.obj.map ((abelianTowerLabels W).map
        (finiteSplittingLabelMap (A := FintypeCat.of
          ((D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V ×
            (D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V))
          (fun q ↦ e.symm (e q.1 + e q.2)))).op
            (D.splitting (finiteSplittingModuleObject R M hM)) =
        M.obj.map ((abelianTowerLabels W).map
          (finiteSplittingLabelMap (A := FintypeCat.of
            ((D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V ×
              (D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V))
            (fun q ↦ q.1))).op
            (D.splitting (finiteSplittingModuleObject R M hM)) +
        M.obj.map ((abelianTowerLabels W).map
          (finiteSplittingLabelMap (A := FintypeCat.of
            ((D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V ×
              (D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V))
            (fun q ↦ q.2))).op
            (D.splitting (finiteSplittingModuleObject R M hM))) ∧
      (M.obj.map ((abelianTowerLabels W).map
        (finiteSplittingLabelMap (fun q ↦ e.symm (-e q)))).op
          (D.splitting (finiteSplittingModuleObject R M hM)) =
        -(@id (M.obj.obj _) (D.splitting (finiteSplittingModuleObject R M hM)))) ∧
      ∀ r : R, M.obj.map ((abelianTowerLabels W).map
        (finiteSplittingLabelMap (fun q ↦ e.symm (r • e q)))).op
          (D.splitting (finiteSplittingModuleObject R M hM)) =
        r • (@id (M.obj.obj _) (D.splitting (finiteSplittingModuleObject R M hM))) := by
  sorry

/-- Restriction of coefficients keeps the same normalized universal section, including
all scalar operations with r acting through a(r).
Source: Bhatt--Scholze 5.1, finite-module consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations).
Proof: Step 4. Restriction leaves the underlying sheaf, its stalk labels, zero,
addition and negation unchanged. Its r-operation is the original a(r)-operation.
Apply the operation identities of Step 3 to a(r). -/
theorem normalizedFiniteSplittings_restrict (D : NormalizedFiniteSplittings W z G)
    (R S : Type (u + 1)) [Ring R] [Ring S] [Finite R] [Finite S] (a : R →+* S)
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} S))
    (hM : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} S))).obj M)) :
    ∃ hRes : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj
        ((sheafCompose (Scheme.ProEt.topology U) (ModuleCat.restrictScalars.{u + 1} a)).obj M)),
      HEq (D.splitting (finiteSplittingModuleObject R
        ((sheafCompose (Scheme.ProEt.topology U)
          (ModuleCat.restrictScalars.{u + 1} a)).obj M) hRes))
        (D.splitting (finiteSplittingModuleObject S M hM)) ∧
    ∃ e : (D.fibre.obj (finiteSplittingModuleObject S M hM)).obj.V ≃
        Scheme.proEtaleGeometricStalk (C := ModuleCat.{u + 1} S) (z ≫ W.hom) M,
      (∀ q, e q = D.moduleLabel M hM q) ∧
      ∀ r : R, M.obj.map ((abelianTowerLabels W).map
        (finiteSplittingLabelMap (fun q ↦ e.symm (a r • e q)))).op
          (D.splitting (finiteSplittingModuleObject S M hM)) =
        a r • (@id (M.obj.obj _) (D.splitting (finiteSplittingModuleObject S M hM))) := by
  refine ⟨hM, HEq.rfl, ?_⟩
  obtain ⟨e, he, _, _, _, _, hscalar⟩ := normalizedFiniteSplittings_module D S M hM
  exact ⟨e, he, fun r ↦ hscalar (a r)⟩

/-- The canonical scalar comparison, including its germ and universal-section formulas.
The latter is an equality on X[Q], for every coefficient b, and determines the
comparison on all local pure tensors. The equivariance equation is linear.
Source: Bhatt--Scholze 5.1, scalar consequence; Stacks 03CZ
(blueprint: lem-sfb-normalized-finite-splitting-operations). -/
structure FiniteSplittingScalarComparison (D : NormalizedFiniteSplittings W z G)
    {R S : Type (u + 1)} [Ring R] [Ring S] (a : R →+* S)
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
    (hM : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M)) where
  finiteN : finiteSplittingObjects W
    ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} S))).obj
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M))
  comparison : (ModuleCat.ringExtendScalars.{u + 1, u + 1} a).obj
      (Scheme.proEtaleGeometricStalk (z ≫ W.hom) M) ≅
    Scheme.proEtaleGeometricStalk (z ≫ W.hom)
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M)
  germ : ∀ V : Scheme.ProEtaleGeometricNeighbourhood (z ≫ W.hom),
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} a).map
      (colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ W.hom) M) (op V)) ≫
        comparison.hom =
      (toSheafify (Scheme.ProEt.topology U)
        (M.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} a)).app
        (op V.right) ≫ colimit.ι
          (Scheme.proEtaleGeometricStalkDiagram (z ≫ W.hom)
            ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M)) (op V)
  labelEquiv : (D.fibre.obj (finiteSplittingModuleObject S
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M) finiteN)).obj.V ≃
    ↥(Scheme.proEtaleGeometricStalk (C := ModuleCat.{u + 1} S) (z ≫ W.hom)
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M))
  labelEquiv_eq : ∀ q, labelEquiv q = D.moduleLabel
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M) finiteN q
  constant : ∀ b : S,
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M).obj.map
      ((abelianTowerLabels W).map (finiteSplittingLabelMap
        (fun q ↦ labelEquiv.symm (comparison.hom
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1} a _ b (D.moduleLabel M hM q)))))).op
        (D.splitting (finiteSplittingModuleObject S
          ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M) finiteN)) =
      (toSheafify (Scheme.ProEt.topology U)
        (M.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} a)).app
        (op ((abelianTowerLabels W).obj
          (FintypeCat.toProfinite.obj
            (D.fibre.obj (finiteSplittingModuleObject R M hM)).obj.V)))
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} a _ b
          (D.splitting (finiteSplittingModuleObject R M hM)))
  sourceAction : FiniteSplittingModuleAction D M hM
  targetAction : FiniteSplittingModuleAction D
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M) finiteN
  equivariant : ∀ g : G,
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} a).map (sourceAction.action g) ≫ comparison.hom =
      comparison.hom ≫ targetAction.action g

/-- Scalar extension stays finite constant and has the specified canonical comparison.
Source: Bhatt--Scholze 5.1, finite-coefficient consequence; Stacks 03CZ
(blueprint: lem-sfb-normalized-finite-splitting-operations).
Proof: Steps 5--8. Geometric inverse image commutes with left scalar extension
by adjoint uniqueness (lem-sfb-geometric-constant-left-scalar-extension), as do
constant modules. The extended fibre is finite: it is a quotient of S^Q by
sending (b_q) to the sum of b_q tensor q. Scalar extension preserves colimits,
and stalks are preserved by sheafification, giving the linear comparison with
the displayed coprojection equation. On pure tensors this is b tensor germ(m)
mapping to germ(b tensor m). Its constant comparison has that same germ;
uniqueness makes it the normalized splitting. Apply scalar extension to the full
overlap arrow: it sends b tensor q to b tensor gq, on every local section.
No flatness, commutativity, or freeness is required. -/
theorem normalizedFiniteSplittings_scalar (D : NormalizedFiniteSplittings W z G)
    (R S : Type (u + 1)) [Ring R] [Ring S] [Finite R] [Finite S] (a : R →+* S)
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
    (hM : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M)) :
    Nonempty (FiniteSplittingScalarComparison D a M hM) := by
  sorry

/-- Naturality of the canonical stalk scalar comparison, for every module map.
Source: Bhatt--Scholze 5.1, finite-coefficient consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations).
Proof: Steps 6 and 8. Both composites take b tensor germ(m) to
b tensor germ(t(m)), by the coprojection equation. Those generators span the
extended stalk, so the two linear maps agree. Their constant comparisons are
natural for the same reason on universal labelled test objects. -/
theorem normalizedFiniteSplittings_scalar_natural
    (D : NormalizedFiniteSplittings W z G)
    (R S : Type (u + 1)) [Ring R] [Ring S] [Finite R] [Finite S] (a : R →+* S)
    (M M' : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
    (hM : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M))
    (hM' : finiteSplittingObjects W
      ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M'))
    (c : FiniteSplittingScalarComparison D a M hM)
    (c' : FiniteSplittingScalarComparison D a M' hM') (t : M ⟶ M') :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} a).map (colim.map
      (Functor.whiskerLeft (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ W.hom)).op
        t.hom)) ≫ c'.comparison.hom =
      c.comparison.hom ≫ colim.map
        (Functor.whiskerLeft (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ W.hom)).op
          ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).map t).hom) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} a
  have : E.IsLeftAdjoint := (ModuleCat.ringExtendScalarsAdj a).isLeftAdjoint
  apply (isColimitOfPreserves E
    (colimit.isColimit (Scheme.proEtaleGeometricStalkDiagram (z ≫ W.hom) M))).hom_ext
  intro j
  change E.map (colimit.ι _ j) ≫ _ = E.map (colimit.ι _ j) ≫ _
  rw [← Category.assoc, ← E.map_comp, colimit.ι_map, E.map_comp, Category.assoc]
  change E.map (t.hom.app (op j.unop.right)) ≫
      E.map (colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ W.hom) M') j) ≫
        c'.comparison.hom = _
  erw [c'.germ j.unop]
  rw [← Category.assoc]
  change _ = (E.map (colimit.ι
    (Scheme.proEtaleGeometricStalkDiagram (z ≫ W.hom) M) j) ≫ c.comparison.hom) ≫ _
  erw [c.germ j.unop]
  simp only [Category.assoc]
  erw [colimit.ι_map]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact congr_app (toSheafify_naturality (Scheme.ProEt.topology U)
    (Functor.whiskerRight t.hom E)) (op j.unop.right)

/-- Coefficient composition uses the canonical balanced associator. The sheaf
comparison is pinned on every sheafified nested pure tensor, including its order
c d(b) in the noncommutative case.
Source: Bhatt--Scholze 5.1, coefficient consequence; Stacks 03CZ
(blueprint: lem-sfb-normalized-finite-splitting-operations).
Proof: Step 8. Both coefficient composites send c tensor (b tensor m) to
c d(b) tensor m. These tensors locally generate, so the sheafification universal
property gives the unique natural isomorphism k. The germ equations for the
three stalk comparisons give the same formula. Generation proves the square. -/
theorem normalizedFiniteSplittings_scalar_comp
    (D : NormalizedFiniteSplittings W z G)
    (R S T : Type (u + 1)) [Ring R] [Ring S] [Ring T]
    [Finite R] [Finite S] [Finite T] (a : R →+* S) (b : S →+* T) :
    ∃ k : Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a ⋙
        Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) b ≅
          Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) (b.comp a),
      (∀ (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
        (V : U.ProEt) (c : T) (d : S) (m : M.obj.obj (op V)),
        (k.hom.app M).hom.app (op V)
          ((toSheafify (Scheme.ProEt.topology U)
            (((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M).obj ⋙
              ModuleCat.ringExtendScalars.{u + 1, u + 1} b)).app (op V)
            (ModuleCat.ringExtensionTmul.{u + 1, u + 1} b _ c
              ((toSheafify (Scheme.ProEt.topology U)
                (M.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} a)).app (op V)
                (ModuleCat.ringExtensionTmul.{u + 1, u + 1} a _ d m)))) =
          (toSheafify (Scheme.ProEt.topology U)
            (M.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} (b.comp a))).app (op V)
              (ModuleCat.ringExtensionTmul.{u + 1, u + 1} (b.comp a) _ (c * b d) m)) ∧
      ∀ (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
        (hM : finiteSplittingObjects W
          ((sheafCompose (Scheme.ProEt.topology U) (forget (ModuleCat.{u + 1} R))).obj M))
        (ca : FiniteSplittingScalarComparison D a M hM)
        (cb : FiniteSplittingScalarComparison D b
          ((Sheaf.ringExtendScalars.{u + 1, u + 1} (Scheme.ProEt.topology U) a).obj M) ca.finiteN)
        (cab : FiniteSplittingScalarComparison D (b.comp a) M hM),
        (ModuleCat.ringExtensionComp.{u + 1, u + 1} a b).hom.app
          (Scheme.proEtaleGeometricStalk (z ≫ W.hom) M) ≫ cab.comparison.hom =
        (ModuleCat.ringExtendScalars.{u + 1, u + 1} b).map ca.comparison.hom ≫ cb.comparison.hom ≫
          colim.map (Functor.whiskerLeft
            (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ W.hom)).op
              (k.hom.app M).hom) := by
  sorry

/-- A pointed equivariant refinement. Its overlap map commutes with both torsor
projections, as an equation of scheme morphisms on the whole parameter space.
Source: Bhatt--Scholze 5.1, pointed refinement consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations). -/
structure FiniteSplittingRefinement {U' : Scheme.{u}} {W' : U'.ProEt}
    {z' : Spec (.of Ω) ⟶ W'.left} {G' : ProfiniteGrp.{u}}
    (D : NormalizedFiniteSplittings W z G) (D' : NormalizedFiniteSplittings W' z' G') where
  base : U' ⟶ U
  coverMap : W'.left ⟶ W.left
  over_base : coverMap ≫ W.hom = W'.hom ≫ base
  point : z' ≫ coverMap = z
  groupMap : G' ⟶ G
  equivariant : ∀ g : G', (D'.action g).left ≫ coverMap =
    coverMap ≫ (D.action (groupMap g)).left
  overlap_fst : Scheme.UniversalCover.profiniteProductMap coverMap
      ((forget₂ ProfiniteGrp Profinite).map groupMap) ≫ D.comparison.hom ≫
        pullback.fst _ _ = D'.comparison.hom ≫ pullback.fst _ _ ≫ coverMap
  overlap_snd : Scheme.UniversalCover.profiniteProductMap coverMap
      ((forget₂ ProfiniteGrp Profinite).map groupMap) ≫ D.comparison.hom ≫
        pullback.snd _ _ = D'.comparison.hom ≫ pullback.snd _ _ ≫ coverMap

/-- Relabel the group coordinate and then apply the given continuous action.
Source: Bhatt--Scholze 5.1 (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
def finiteSplittingRefinedAction {G' : ProfiniteGrp.{u}}
    (D : NormalizedFiniteSplittings W z G)
    (F : (finiteSplittingObjects W).FullSubcategory) (t : G' ⟶ G)
    {B : FintypeCat.{u}} (a : (D.fibre.obj F).obj.V ⟶ B) :
    Profinite.of (G' × FintypeCat.toProfinite.obj (D.fibre.obj F).obj.V) ⟶
      FintypeCat.toProfinite.obj B :=
  ConcreteCategory.ofHom ⟨fun p ↦ a (D.actionLabels F (t p.1, p.2)),
    (FintypeCat.toProfinite.map a).hom.hom.continuous.comp
      ((D.actionLabels F).hom.hom.continuous.comp
        (((forget₂ ProfiniteGrp Profinite).map t).hom.hom.continuous.prodMap continuous_id))⟩

/-- Keep the group parameter and relabel the finite coordinate.
Source: Bhatt--Scholze 5.1 (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
def finiteSplittingRefinedLabels (G' : ProfiniteGrp.{u}) {A B : FintypeCat.{u}}
    (a : A ⟶ B) :
    Profinite.of (G' × FintypeCat.toProfinite.obj A) ⟶
      Profinite.of (G' × FintypeCat.toProfinite.obj B) :=
  ConcreteCategory.ofHom ⟨fun p ↦ (p.1, a p.2),
    continuous_fst.prodMk ((FintypeCat.toProfinite.map a).hom.hom.continuous.comp
      continuous_snd)⟩

/-- The overlap parameter map sends (g', q) to (theta(g'), q).
Source: Bhatt--Scholze 5.1, pointed refinement consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations). -/
def finiteSplittingRefinedParameters {G' : ProfiniteGrp.{u}}
    (G : ProfiniteGrp.{u}) (t : G' ⟶ G) (A : FintypeCat.{u}) :
    Profinite.of (G' × FintypeCat.toProfinite.obj A) ⟶
      Profinite.of (G × FintypeCat.toProfinite.obj A) :=
  ConcreteCategory.ofHom ⟨fun p ↦ (t p.1, p.2),
    ((forget₂ ProfiniteGrp Profinite).map t).hom.hom.continuous.prodMap continuous_id⟩

/-- Equality of the pulled-back normalized universal section. The comparison t is
specified by both projections, hence is the canonical map on labelled schemes.
The overlap comparison o is likewise specified by both projections, using
(v, theta, id) on the labelled overlap. The last equation pulls F's actual
D.descentLabel section through g and o and compares it with the refined descent section.
Source: Bhatt--Scholze 5.1, pointed refinement consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations). -/
def FiniteSplittingRefinement.Identifies {U' : Scheme.{u}} {W' : U'.ProEt}
    {z' : Spec (.of Ω) ⟶ W'.left} {G' : ProfiniteGrp.{u}}
    {D : NormalizedFiniteSplittings W z G} {D' : NormalizedFiniteSplittings W' z' G'}
    (r : FiniteSplittingRefinement D D')
    (F : (finiteSplittingObjects W).FullSubcategory)
    (F' : (finiteSplittingObjects W').FullSubcategory)
    (g : F.obj ⟶ (Scheme.proEtaleSheafDirectImage r.base (Type (u + 1))).obj F'.obj)
    (a : (D.fibre.obj F).obj.V ≅ (D'.fibre.obj F').obj.V) : Prop :=
  (∀ (x : G') (q : (D.fibre.obj F).obj.V),
    a.hom (ConcreteCategory.hom ((D.fibre.obj F).obj.ρ (r.groupMap x)) q) =
      ConcreteCategory.hom ((D'.fibre.obj F').obj.ρ x) (a.hom q)) ∧
  ∃ t : (abelianTowerLabels W').obj
      (FintypeCat.toProfinite.obj (D.fibre.obj F).obj.V) ⟶
    (Scheme.proEtaleBaseChange r.base).obj ((abelianTowerLabels W).obj
      (FintypeCat.toProfinite.obj (D.fibre.obj F).obj.V)),
    t.left ≫ pullback.fst _ _ = Scheme.UniversalCover.profiniteProductMap
      r.coverMap (𝟙 _) ∧
    t.left ≫ pullback.snd _ _ = ((abelianTowerLabels W').obj
      (FintypeCat.toProfinite.obj (D.fibre.obj F).obj.V)).hom ∧
    F'.obj.obj.map t.op (g.hom.app _ (D.splitting F)) =
      F'.obj.obj.map ((abelianTowerLabels W').map
        (FintypeCat.toProfinite.map a.hom)).op (D'.splitting F') ∧
    ∃ o : (abelianTowerLabels W').obj
        (Profinite.of (G' × FintypeCat.toProfinite.obj (D.fibre.obj F).obj.V)) ⟶
      (Scheme.proEtaleBaseChange r.base).obj ((abelianTowerLabels W).obj
        (Profinite.of (G × FintypeCat.toProfinite.obj (D.fibre.obj F).obj.V))),
      o.left ≫ pullback.fst _ _ = Scheme.UniversalCover.profiniteProductMap
        r.coverMap (finiteSplittingRefinedParameters G r.groupMap (D.fibre.obj F).obj.V) ∧
      o.left ≫ pullback.snd _ _ = ((abelianTowerLabels W').obj
        (Profinite.of (G' × FintypeCat.toProfinite.obj (D.fibre.obj F).obj.V))).hom ∧
      F'.obj.obj.map o.op
        (g.hom.app _ (F.obj.obj.map (D.descentLabel F).op (D.splitting F))) =
        F'.obj.obj.map ((abelianTowerLabels W').map
          (finiteSplittingRefinedLabels G' a.hom)).op
            (F'.obj.obj.map (D'.descentLabel F').op (D'.splitting F'))

/-- Every pointed refinement pulls back both the normalized splitting and its full
continuous descent arrow. The unique finite-label identification is the pointed
stalk identification, because the universal sections have their prescribed germs.
Source: Bhatt--Scholze 5.1, pointed consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations).
Proof: Steps 9--10. The square gives u' inverse h inverse F = v inverse u inverse F
via canonical inverse-image compositors. Constants remain constant since inverse
image preserves terminal objects and coproducts. The pointed stalk comparison
identifies the pulled splitting's germ with the original one since v(z')=z.
Uniqueness identifies the normalized sections. Substitution of the two overlap
projection identities in the entire descent arrow replaces g' by theta(g').
This proves the displayed whole-arrow equation and equivariance, not merely an
equality at geometric stalks. A fibre bijection is uniquely determined by the
normalized universal section on the nonempty connected refined cover. -/
theorem normalizedFiniteSplittings_refinement
    {U' : Scheme.{u}} {W' : U'.ProEt} {z' : Spec (.of Ω) ⟶ W'.left}
    {G' : ProfiniteGrp.{u}} (D : NormalizedFiniteSplittings W z G)
    (D' : NormalizedFiniteSplittings W' z' G') (r : FiniteSplittingRefinement D D')
    (F : (finiteSplittingObjects W).FullSubcategory) :
    finiteSplittingObjects W'
      ((Scheme.proEtaleSheafInverseImage r.base (Type (u + 1))).obj F.obj) ∧
    ∀ (F' : (finiteSplittingObjects W').FullSubcategory)
      (g : F.obj ⟶ (Scheme.proEtaleSheafDirectImage r.base (Type (u + 1))).obj F'.obj),
      IsIso (((Scheme.proEtaleSheafAdjunction r.base (Type (u + 1))).homEquiv _ _).symm g) →
      ∃! a : (D.fibre.obj F).obj.V ≅ (D'.fibre.obj F').obj.V,
        r.Identifies F F' g a := by
  sorry

/-- The canonical direct-image compositor for sets, from pullback pasting.
Source: Stacks 09A5 (blueprint: lem-sfb-normalized-finite-splitting-operations). -/
def finiteSplittingDirectImageComp {U₀ U₁ U₂ : Scheme.{u}}
    (h : U₁ ⟶ U₀) (h' : U₂ ⟶ U₁) :
    Scheme.proEtaleSheafDirectImage h' (Type (u + 1)) ⋙
      Scheme.proEtaleSheafDirectImage h (Type (u + 1)) ≅
        Scheme.proEtaleSheafDirectImage (h' ≫ h) (Type (u + 1)) :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
      (Q := ⊤) h' h).symm) (Type (u + 1))
    (Scheme.ProEt.topology U₀) (Scheme.ProEt.topology U₁) (Scheme.ProEt.topology U₂)

/-- Pointed-refinement identifications compose, for the canonical direct-image
compositor, and therefore for its adjunction-compatible inverse-image mate.
The result includes the full descent-arrow equation through `Identifies`.
Source: Bhatt--Scholze 5.1, pointed-refinement consequence
(blueprint: lem-sfb-normalized-finite-splitting-operations).
Proof: Step 11. Compose the base maps, covering maps and continuous group maps.
Their point, equivariance and two projection identities compose by associativity.
Pulling a normalized splitting twice has the same germ as pulling once by the
composite. Uniqueness therefore identifies the two universal sections. On overlaps
both substitutions send g'' to theta(theta'(g'')); hence the full descent arrows
agree. Adjunction units give the displayed direct-image composite, so this also
states coherence for the canonical inverse-image compositor. -/
theorem normalizedFiniteSplittings_refinement_comp
    {U' U'' : Scheme.{u}} {W' : U'.ProEt} {W'' : U''.ProEt}
    {z' : Spec (.of Ω) ⟶ W'.left} {z'' : Spec (.of Ω) ⟶ W''.left}
    {G' G'' : ProfiniteGrp.{u}} (D : NormalizedFiniteSplittings W z G)
    (D' : NormalizedFiniteSplittings W' z' G')
    (D'' : NormalizedFiniteSplittings W'' z'' G'')
    (r : FiniteSplittingRefinement D D') (r' : FiniteSplittingRefinement D' D'') :
    ∃ rc : FiniteSplittingRefinement D D'',
      ∃ hb : rc.base = r'.base ≫ r.base,
        rc.coverMap = r'.coverMap ≫ r.coverMap ∧
        rc.groupMap = r'.groupMap ≫ r.groupMap ∧
        ∀ (F : (finiteSplittingObjects W).FullSubcategory)
          (F' : (finiteSplittingObjects W').FullSubcategory)
          (F'' : (finiteSplittingObjects W'').FullSubcategory)
          (g : F.obj ⟶ (Scheme.proEtaleSheafDirectImage r.base (Type (u + 1))).obj F'.obj)
          (g' : F'.obj ⟶
            (Scheme.proEtaleSheafDirectImage r'.base (Type (u + 1))).obj F''.obj)
          (a : (D.fibre.obj F).obj.V ≅ (D'.fibre.obj F').obj.V)
          (b : (D'.fibre.obj F').obj.V ≅ (D''.fibre.obj F'').obj.V),
          r.Identifies F F' g a → r'.Identifies F' F'' g' b →
          rc.Identifies F F''
            (g ≫ (Scheme.proEtaleSheafDirectImage r.base (Type (u + 1))).map g' ≫
              (finiteSplittingDirectImageComp r.base r'.base).hom.app F''.obj ≫
                eqToHom (congrArg
                  (fun f ↦ (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj F''.obj)
                  hb.symm)) (a ≪≫ b) := by
  sorry

end AlgebraicGeometry.ProEtale
