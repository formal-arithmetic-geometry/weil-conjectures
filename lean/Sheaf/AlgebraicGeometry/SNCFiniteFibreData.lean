module

public import Sheaf.AlgebraicGeometry.SNCFiniteTameSheaves
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
public import Sheaf.CategoryTheory.InternalModule
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings


/-!
# Normalized finite-fibre classification on a residual SNC chart

Source: ILO, Expose IX, Proposition 2.1(i)-(iii), printed pages 133-134;
Stacks 09ZS; Bhatt--Scholze, Corollary 5.1.5 and Lemma 7.4.3.
(blueprint: def-sfb-snc-finite-fibre-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.ProEtale

variable {p : ℕ} {Y : Scheme.{u}} {a : ℕ}
  {C : Fin a → Y.IdealSheafData} {I : Finset (Fin a)}

/-- Regard the already supplied covering projection as an object of the small site.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-fibre-data). -/
def SNCResidualChart.towerObject (Q : SNCResidualChart p C I) :
    Q.puncturedResidual.ProEt :=
  @Scheme.ProEt.mk _ _ Q.towerMap
    ((MorphismProperty.singleton_mem_precoverage _).mp
      (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _
        Q.tower.puncturedFull_cover))

/-- Profinite copies of the root tower, viewed over the residual puncture.
Source: Stacks 097D (blueprint: def-sfb-snc-finite-fibre-data). -/
def SNCResidualChart.towerProduct (Q : SNCResidualChart p C I) :
    Profinite.{u} ⥤ Q.puncturedResidual.ProEt :=
  profiniteToProEtOf Q.puncturedTower ⋙ MorphismProperty.Over.map ⊤ Q.towerObject.prop

/-- The identity on the root-tower coordinate and a continuous change of labels.
Source: Stacks 097D (blueprint: def-sfb-snc-finite-fibre-data). -/
abbrev SNCResidualChart.towerLabelMap (Q : SNCResidualChart p C I)
    {P P' : Profinite.{u}} (f : P ⟶ P') :
    (Q.towerProduct.obj P ⟶ Q.towerProduct.obj P') := Q.towerProduct.map f

/-- The pointed neighborhood used to normalize a finite label to its actual stalk germ.
Source: Stacks 0F6B (blueprint: def-sfb-snc-finite-fibre-data). -/
def SNCResidualChart.labelNeighbourhood (Q : SNCResidualChart p C I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Q.puncturedTower)
    (P : Profinite.{u}) (q : P) :
    Scheme.ProEtaleGeometricNeighbourhood (z ≫ Q.towerMap) :=
  StructuredArrow.mk (Y := Q.towerProduct.obj P)
    (Over.homMk (z ≫ Scheme.UniversalCover.profiniteProductSection _ P q) (by
      change z ≫ pullback.lift _ (𝟙 _) _ ≫
        (pullback.snd _ _ ≫ Q.towerMap) = _
      simp only [pullback.lift_snd_assoc, Category.id_comp, Over.mk_hom]))

/-- The permutation map on the whole profinite space G times the finite fibre.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-fibre-data). -/
def sncActionLabels {G : Type u} [Group G] [TopologicalSpace G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : ContAction FintypeCat.{u} G) :
    Profinite.of (G × FintypeCat.toProfinite.obj A.obj.V) ⟶
      FintypeCat.toProfinite.obj A.obj.V :=
  ConcreteCategory.ofHom ⟨fun x ↦ ConcreteCategory.hom (A.obj.ρ x.1) x.2, A.property.1⟩

/-- First projection of two profinite label spaces.
Source: Stacks 097D (blueprint: def-sfb-snc-finite-fibre-data). -/
def sncFirstLabels (P P' : Profinite.{u}) : Profinite.of (P × P') ⟶ P :=
  ConcreteCategory.ofHom ⟨Prod.fst, continuous_fst⟩

/-- Second projection of two profinite label spaces.
Source: Stacks 097D (blueprint: def-sfb-snc-finite-fibre-data). -/
def sncSecondLabels (P P' : Profinite.{u}) : Profinite.of (P × P') ⟶ P' :=
  ConcreteCategory.ofHom ⟨Prod.snd, continuous_snd⟩

/-- A deck map is specified on the entire profinite product and on the prime-power root
coordinates. Prime-power residues determine every tame root rotation by CRT.
Source: ILO IX 2.1, Stacks 097D
(blueprint: def-sfb-snc-finite-fibre-data). -/
structure SNCRootDeck (Q : SNCResidualChart p C I) where
  deck : (Q.towerProduct.obj (Profinite.of (SNCInertia.{u} p (Fintype.card I)))).left ⟶
    Q.puncturedTower
  over_base : deck ≫ Q.towerMap =
    Scheme.UniversalCover.profiniteProductBase _ _ ≫ Q.towerMap
  comparison_isIso : IsIso
    (pullback.lift (Scheme.UniversalCover.profiniteProductBase _ _) deck over_base.symm)
  rotation : SNCInertia.{u} p (Fintype.card I) → Q.puncturedTowerRing →+* Q.puncturedTowerRing
  rotation_base : ∀ g (h : Q.H),
    rotation g (algebraMap (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)))
        Q.puncturedTowerRing
        (algebraMap Q.H (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i))) h)) =
      algebraMap (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)))
        Q.puncturedTowerRing
        (algebraMap Q.H (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i))) h)
  rotation_root : ∀ (g : SNCInertia.{u} p (Fintype.card I))
      (q : {q : ℕ // q.Prime ∧ q ≠ p}) (e : ℕ)
      (n : TameRootOrder p) (_hn : n.val = q.val ^ e) (i : Fin (Fintype.card I)),
    rotation g (algebraMap (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)))
      Q.puncturedTowerRing
      (sncFullRootCoordinate p (fun i ↦ Q.b.hom (Q.t i)) n i)) =
        algebraMap (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)))
          Q.puncturedTowerRing (algebraMap Q.H _
          (Q.zeta n ^ (@PadicInt.toZModPow q.val (Fact.mk q.2.1) e
            (g.down.toAdd i q)).val)) *
          algebraMap (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)))
          Q.puncturedTowerRing (sncFullRootCoordinate p (fun i ↦ Q.b.hom (Q.t i)) n i)
  rotation_deck : ∀ g,
    Scheme.UniversalCover.profiniteProductSection _ _ g ≫ deck =
      Spec.map (CommRingCat.ofHom (rotation g))

/-- Finite-fibre classification data. The universal section `splitting` represents the
restriction to the root tower: its restrictions give bijections on every site object.
Its germs fix its normalization. The last equality is over the whole space X[G times Q],
so it specifies the descent arrow on profinite parameters, not only individual deck maps.
Source: ILO IX 2.1, Stacks 09ZS, Bhatt--Scholze 5.1.5 and 7.4.3
(blueprint: def-sfb-snc-finite-fibre-data). -/
structure SNCFiniteFibreClassification (Q : SNCResidualChart p C I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Q.puncturedTower) where
  rootDeck : SNCRootDeck Q
  fibre : Q.FiniteTame ⥤ ContAction FintypeCat.{u} (SNCInertia.{u} p (Fintype.card I))
  fullyFaithful : fibre.FullyFaithful
  fibreIso : fibre ⋙ forget₂ _ FintypeCat ⋙ forget FintypeCat ⋙ uliftFunctor.{u + 1, u} ≅
    Q.finiteTameStalk z
  splitting : ∀ F : Q.FiniteTame,
    F.obj.obj.obj (op (Q.towerProduct.obj
      (FintypeCat.toProfinite.obj (fibre.obj F).obj.V)))
  splitting_bijective : ∀ (F : Q.FiniteTame) (W : Q.puncturedTower.ProEt),
    Function.Bijective (fun f : W ⟶
        (profiniteToProEtOf Q.puncturedTower).obj
          (FintypeCat.toProfinite.obj (fibre.obj F).obj.V) ↦
      F.obj.obj.map
        ((MorphismProperty.Over.map ⊤ Q.towerObject.prop).map f).op (splitting F))
  normalized : ∀ (F : Q.FiniteTame) (q : (fibre.obj F).obj.V),
    (colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) F.obj)
      (op (Q.labelNeighbourhood z _ q))) (splitting F) =
        fibreIso.hom.app F (ULift.up q)
  natural : ∀ (F F' : Q.FiniteTame) (f : F ⟶ F'),
    F'.obj.obj.map
      (Q.towerLabelMap
        (FintypeCat.toProfinite.map ((forget₂ _ FintypeCat).map (fibre.map f)))).op
        (splitting F') =
      f.hom.hom.app _ (splitting F)
  products : HasFiniteProducts Q.FiniteTame
  inclusion_preserves_products :
    PreservesFiniteProducts (ObjectProperty.ι Q.finiteTame)
  preserves_products : @PreservesFiniteProducts _ _ _ _ fibre
  descentLabel : ∀ F : Q.FiniteTame,
    (Q.towerProduct.obj (Profinite.of
      (SNCInertia.{u} p (Fintype.card I) ×
        FintypeCat.toProfinite.obj (fibre.obj F).obj.V))) ⟶
      Q.towerProduct.obj (FintypeCat.toProfinite.obj (fibre.obj F).obj.V)
  descentLabel_base : ∀ F,
    (descentLabel F).left ≫ Scheme.UniversalCover.profiniteProductBase _ _ =
      (Q.towerLabelMap (sncFirstLabels
        (Profinite.of (SNCInertia.{u} p (Fintype.card I)))
        (FintypeCat.toProfinite.obj (fibre.obj F).obj.V))).left ≫
        rootDeck.deck
  descentLabel_label : ∀ F,
    (descentLabel F).left ≫ pullback.fst _ _ =
      (Q.towerLabelMap (sncSecondLabels
        (Profinite.of (SNCInertia.{u} p (Fintype.card I)))
        (FintypeCat.toProfinite.obj (fibre.obj F).obj.V))).left ≫
        pullback.fst _ _
  descent : ∀ F : Q.FiniteTame,
    F.obj.obj.map (Q.towerLabelMap (sncActionLabels (fibre.obj F))).op (splitting F) =
      F.obj.obj.map (descentLabel F).op (splitting F)

/-- Evaluation of a morphism by its finite fibre functor.
Source: Bhatt--Scholze 5.1.5
(blueprint: def-sfb-snc-finite-fibre-data). -/
abbrev SNCFiniteFibreClassification.eval {Q : SNCResidualChart p C I}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {z : Spec (.of Ω) ⟶ Q.puncturedTower}
    (d : SNCFiniteFibreClassification Q z) {F F' : Q.FiniteTame} (f : F ⟶ F') :
    (d.fibre.obj F).obj.V → (d.fibre.obj F').obj.V :=
  ConcreteCategory.hom ((d.fibre.map f).hom.hom)

/-- The finite linear fibre, with its operations fixed by all generalized elements.
The underlying action is precisely the root monodromy action already constructed.
Source: ILO IX 2.1 and Stacks 0DV5
(blueprint: def-sfb-snc-finite-fibre-data). -/
structure SNCFiniteLinearFibre {Q : SNCResidualChart p C I}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {z : Spec (.of Ω) ⟶ Q.puncturedTower}
    (d : SNCFiniteFibreClassification Q z) (R : Type v) [Ring R]
    [HasFiniteProducts Q.FiniteTame] (M : InternalModule R Q.FiniteTame) where
  linear : FiniteContinuousModule.{v, u, u} R (SNCInertia.{u} p (Fintype.card I))
  identify : (d.fibre.obj M.X).obj.V ≃ linear.obj.obj.V
  equivariant : ∀ g q,
    identify (ConcreteCategory.hom ((d.fibre.obj M.X).obj.ρ g) q) =
      linear.obj.obj.ρ g (identify q)
  operations : ∀ (T : Q.FiniteTame) (x y : T ⟶ M.X) (t : (d.fibre.obj T).obj.V),
    identify (d.eval (prod.lift x y ≫ M.add) t) =
      identify (d.eval x t) + identify (d.eval y t) ∧
    identify (d.eval (terminal.from T ≫ M.zero) t) = 0 ∧
    identify (d.eval (x ≫ M.neg) t) = -identify (d.eval x t) ∧
    ∀ b : R, identify (d.eval (x ≫ M.smul b) t) =
      b • identify (d.eval x t)


/-- A finite label as an element of the actual module stalk, using its normalized
universal section and the canonical neighborhood coprojection.
Source: ILO IX 2.1 and Stacks 0F6B
(blueprint: def-sfb-snc-finite-fibre-data). -/
def SNCFiniteFibreClassification.moduleStalkLabel {Q : SNCResidualChart p C I}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {z : Spec (.of Ω) ⟶ Q.puncturedTower}
    (d : SNCFiniteFibreClassification Q z) {R : Type (u + 1)} [Ring R]
    (M : Sheaf (Scheme.ProEt.topology Q.puncturedResidual) (ModuleCat.{u + 1} R))
    (hM : Q.finiteTame ((sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (forget (ModuleCat.{u + 1} R))).obj M))
    (q : (d.fibre.obj ⟨_, hM⟩).obj.V) :
    ↥(Scheme.proEtaleGeometricStalk (C := ModuleCat.{u + 1} R)
      (z ≫ Q.towerMap) M) :=
  (colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) M)
    (op (Q.labelNeighbourhood z _ q))) (d.splitting ⟨_, hM⟩)

/-- The module stalk action is pinned on every normalized finite-fibre label.
These labels exhaust the stalk, so this condition determines the action uniquely.
Source: ILO IX 2.1 and Stacks 0DV5
(blueprint: def-sfb-snc-finite-fibre-data). -/
structure SNCFiniteModuleStalkAction {Q : SNCResidualChart p C I}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {z : Spec (.of Ω) ⟶ Q.puncturedTower}
    (d : SNCFiniteFibreClassification Q z) {R : Type (u + 1)} [Ring R]
    (M : Sheaf (Scheme.ProEt.topology Q.puncturedResidual) (ModuleCat.{u + 1} R))
    (hM : Q.finiteTame ((sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (forget (ModuleCat.{u + 1} R))).obj M)) where
  action : SNCInertia.{u} p (Fintype.card I) →*
    End (Scheme.proEtaleGeometricStalk (z ≫ Q.towerMap) M)
  normalized : ∀ g q,
    ConcreteCategory.hom (action g) (d.moduleStalkLabel M hM q) =
      d.moduleStalkLabel M hM
        (ConcreteCategory.hom ((d.fibre.obj ⟨_, hM⟩).obj.ρ g) q)

end AlgebraicGeometry.ProEtale
