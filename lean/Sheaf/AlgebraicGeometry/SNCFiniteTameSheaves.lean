module

public import Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.Paper.FullParameterRootTower
public import Sheaf.CategoryTheory.FiniteContinuousModule
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Finite tame set sheaves on a residual normal crossings chart

Source: ILO, Expose IX, Proposition 2.1(i)-(iii), printed pages 133-134;
Bhatt--Scholze, Corollary 5.1.5 and Lemma 7.4.3.
(blueprint: def-sfb-snc-finite-tame-sheaves).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.ProEtale

/-- Set-valued sheaves with the site's coefficient universe.
Source: Bhatt--Scholze, Definition 4.1.1
(blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCSetSheaf (X : Scheme.{u}) := Sheaf (Scheme.ProEt.topology X) (Type (u + 1))

/-- Locally a finite constant set on an actual pro-etale covering family. The finite set
may vary with the member of the cover, and may be empty.
Source: Bhatt--Scholze, finite-set form of Corollary 5.1.5
(blueprint: def-sfb-snc-finite-tame-sheaves). -/
def SNCFiniteLocallyConstant {X : Scheme.{u}} (F : SNCSetSheaf X) : Prop :=
  ∃ (A : Type (u + 1)) (U : A → X.ProEt)
    (f : ∀ i, U i ⟶ Scheme.ProEt.mk (𝟙 X)),
    Presieve.ofArrows U f ∈ Scheme.ProEt.precoverage X (Scheme.ProEt.mk (𝟙 X)) ∧
      ∀ i, ∃ Q : FintypeCat.{u}, Nonempty
        (F.over (U i) ≅
          ((constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
            (ULift.{u + 1, u} Q)).over (U i))

/-- Tameness on every punctured strict-local parameter-root tower. The existing
boundary-parameter predicate selects precisely the vanishing local branches.
Source: ILO IX, Proposition 2.1(i)-(iii)
(blueprint: def-sfb-snc-finite-tame-sheaves). -/
def SNCStrictLocalTame (p : ℕ) {Y W : Scheme.{u}} (D : Y.IdealSheafData)
    (w : W ⟶ Y) (F : SNCSetSheaf W) : Prop :=
  ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (s : Spec (.of κ) ⟶ Y)
    (r : ℕ) (t : Fin r → Scheme.strictHenselizationRing s),
    IsStrictLocalBoundaryParameters D s t →
      ∃ Q : FintypeCat.{u}, Nonempty
        ((Scheme.proEtaleSheafInverseImage (strictLocalTameRootProjection p w s t)
          (Type (u + 1))).obj F ≅
          (constantSheaf (Scheme.ProEt.topology _) (Type (u + 1))).obj
            (ULift.{u + 1, u} Q))

/-- The indicated finite product of prime-to-p adic integers, lifted only to the site's
universe. Its topology is the product topology, not the discrete topology.
Source: ILO IX 2.1 and the tame-root CRT identification
(blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCInertia (p r : ℕ) := ULift.{u} (ParameterRootDeckGroup p (Fin r))

/-- Hausdorffness is unchanged by the additive-to-multiplicative type tag.
Source: the adic product topology
(blueprint: def-sfb-snc-finite-tame-sheaves). -/
instance sncInertiaT2 (p r : ℕ) : T2Space (SNCInertia.{u} p r) := by
  change T2Space (ULift.{u} (Fin r →
    ∀ q : {q : ℕ // q.Prime ∧ q ≠ p}, @PadicInt q.1 (Fact.mk q.2.1)))
  have (q : {q : ℕ // q.Prime ∧ q ≠ p}) :
      T2Space (@PadicInt q.1 (Fact.mk q.2.1)) := by
    let : Fact q.1.Prime := ⟨q.2.1⟩
    infer_instance
  infer_instance

/-- Total disconnectedness of the adic product.
Source: the adic product topology
(blueprint: def-sfb-snc-finite-tame-sheaves). -/
instance sncInertiaTotallyDisconnected (p r : ℕ) :
    TotallyDisconnectedSpace (SNCInertia.{u} p r) := by
  have (q : {q : ℕ // q.Prime ∧ q ≠ p}) :
      TotallyDisconnectedSpace (@PadicInt q.1 (Fact.mk q.2.1)) := by
    let : Fact q.1.Prime := ⟨q.2.1⟩
    infer_instance
  have : TotallyDisconnectedSpace (Fin r →
      ∀ q : {q : ℕ // q.Prime ∧ q ≠ p}, @PadicInt q.1 (Fact.mk q.2.1)) :=
    inferInstance
  exact Homeomorph.ulift.symm.totallyDisconnectedSpace

variable {p : ℕ} {Y : Scheme.{u}} {a : ℕ}
  {C : Fin a → Y.IdealSheafData} {I : Finset (Fin a)}

/-- The punctured affine chart.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCResidualChart.puncturedChart (Q : SNCResidualChart p C I) : Scheme.{u} :=
  Spec (.of (Localization.Away (∏ i, Q.t i)))

/-- The localization map to the affine chart.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCResidualChart.puncturedChartMap (Q : SNCResidualChart p C I) :
    Q.puncturedChart ⟶ Spec Q.B :=
  Spec.map (CommRingCat.ofHom (algebraMap Q.B (Localization.Away (∏ i, Q.t i))))

/-- The punctured universal residual neighborhood.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCResidualChart.puncturedResidual (Q : SNCResidualChart p C I) : Scheme.{u} :=
  Spec (.of (Localization.Away (∏ i, Q.b.hom (Q.t i))))

/-- The actual localization of the full compatible-root algebra.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCResidualChart.puncturedTowerRing (Q : SNCResidualChart p C I) :=
  Localization.Away (algebraMap Q.H (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)))
    (∏ i, Q.b.hom (Q.t i)))

/-- The full punctured parameter-root tower, using the existing algebra and colimit.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCResidualChart.puncturedTower (Q : SNCResidualChart p C I) : Scheme.{u} :=
  Spec (.of Q.puncturedTowerRing)

/-- The existing root-tower covering projection.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCResidualChart.towerMap (Q : SNCResidualChart p C I) :
    Q.puncturedTower ⟶ Q.puncturedResidual :=
  Spec.map (CommRingCat.ofHom Q.tower.puncturedFull)

/-- The map of punctured affine schemes induced by B to H.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
def SNCResidualChart.puncturedMap (Q : SNCResidualChart p C I) :
    Q.puncturedResidual ⟶ Q.puncturedChart := by
  let f := Q.b.hom
  let : IsLocalization.Away (f (∏ i, Q.t i))
      (Localization.Away (∏ i, Q.b.hom (Q.t i))) := by
    simpa only [map_prod] using
      (inferInstance : IsLocalization.Away (∏ i, Q.b.hom (Q.t i))
        (Localization.Away (∏ i, Q.b.hom (Q.t i))))
  exact Spec.map (CommRingCat.ofHom (IsLocalization.Away.map _ _ f (∏ i, Q.t i)))

/-- The principal boundary on the affine chart, including the empty boundary.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
def SNCResidualChart.chartBoundary (Q : SNCResidualChart p C I) :
    (Spec Q.B).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {(Scheme.ΓSpecIso Q.B).inv (∏ i, Q.t i)})

/-- Exactly the essential image stipulated in the finite-fibre classification: first
choose a finite locally constant tame sheaf on Vcirc, then pull it back to Ucirc.
This is a property of sheaves, so its category is the full subcategory.
Source: ILO IX 2.1 and Bhatt--Scholze 5.1.5
(blueprint: def-sfb-snc-finite-tame-sheaves). -/
def SNCResidualChart.finiteTame (Q : SNCResidualChart p C I)
    (F : SNCSetSheaf Q.puncturedResidual) : Prop :=
  ∃ F₀ : SNCSetSheaf Q.puncturedChart,
    SNCFiniteLocallyConstant F₀ ∧
      SNCStrictLocalTame p Q.chartBoundary Q.puncturedChartMap F₀ ∧
        Nonempty ((Scheme.proEtaleSheafInverseImage Q.puncturedMap (Type (u + 1))).obj F₀ ≅ F)

/-- The full category of finite tame sheaves in the node.
Source: ILO IX 2.1 (blueprint: def-sfb-snc-finite-tame-sheaves). -/
abbrev SNCResidualChart.FiniteTame (Q : SNCResidualChart p C I) :=
  ObjectProperty.FullSubcategory Q.finiteTame

/-- The actual geometric stalk as a functor, restricted to the full tame subcategory.
Source: Stacks 0F6B (blueprint: def-sfb-snc-finite-tame-sheaves). -/
def SNCResidualChart.finiteTameStalk (Q : SNCResidualChart p C I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Q.puncturedTower) :
    Q.FiniteTame ⥤ Type (u + 1) :=
  ObjectProperty.ι Q.finiteTame ⋙
    sheafToPresheaf (Scheme.ProEt.topology Q.puncturedResidual) (Type (u + 1)) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ Q.towerMap)).op ⋙ colim

end AlgebraicGeometry.ProEtale
