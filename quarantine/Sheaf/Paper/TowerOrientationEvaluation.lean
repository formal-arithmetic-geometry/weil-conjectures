module

public import Sheaf.Paper.SmoothPurityCompositionFactors
public import Sheaf.Paper.CompositionComparisons
public import Sheaf.Paper.TowerTensorTransposeWords
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.TensorWordComparison
import Sheaf.Paper.TowerOrientationWordNormalization
import Sheaf.Paper.TowerMuEvaluation
import Sheaf.Paper.TowerTateSplitNormalized
import Sheaf.Paper.OrderedTateTowerCohomology

/-! # Evaluation and concentration of composite tower orientations

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, (1), tower paragraph
(blueprint: lem-sp-tower-orientation-evaluation).

The published composition-factor definitions are reused, without invoking their
composition theorem. Every natural level index n represents the positive exponent n+1.
All objects and arrows belong to ordinary derived categories of strict systems.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpCompositionFactors

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AlgebraicGeometry.ProEtale.ModuleDerivedCategory._proof_1
  AlgebraicGeometry.ProEtale.ModuleDerivedCategory._proof_2
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- A finite diagonal orientation and the normalized coefficient-unit identification.
Both comparison squares use the actual units and counits of the given adjunction.
Source: tower paragraph (1), using tower-gamma (1)
(blueprint: lem-sp-tower-orientation-evaluation). -/
structure TowerOrientationLevel {X V Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ V) [IsOpenImmersion j] (p : V ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) (w : SpChartAdmissibility.Twists l E X)
    (P : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization j p))
    (a : SpTowerGamma.Purity l E b o q j p d w P.closed P.right P.adj P.levels)
    (n : ℕ) where
  geometry : Etale.FiniteRingSectionDeformation.Geometry d
    (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p))
  orientation : Etale.dualizingComplex (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n))
    (j ≫ p) ≅ Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n)
      (l ^ (n + 1)) (SpTowerP1.levelAnnihilates l E n) X d
  diagonal : Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E n)
    (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
    (SpTowerP1.levelAnnihilates l E n) (j ≫ p) d geometry (a.unitsX n) orientation
  unit : (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p)
    P.closed P.right P.adj P.levels n
      ⟨SpTowerGamma.originalUnit l E b q Y, a.unit_mem⟩).etale ≅
        Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Y
  unit_normalized : (SpTowerP1.nu l E n Y).map unit.hom ≫
      (SpTowerP1.unitWord l E n Y (a.coefficientsY n)).comparison =
    (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p)
      P.closed P.right P.adj P.levels n
        ⟨SpTowerGamma.originalUnit l E b q Y, a.unit_mem⟩).comparison ≫
      (SpTowerShriek.Ev l E Y n).map
        ((SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso.hom.app
          (SpTowerGamma.unit l E Y))
  evaluated : SpTowerP1.WordComparison l E n
    (SpTowerGamma.coefficientWord l E b X w a.roots n (a.unitsX n)
      (a.coefficientsX n) (a.tensors n) d)
    (SpTensorTranspose.dualizingWord l E b o q j p
      P.closed P.right P.adj P.levels a.unit_mem n unit)
    a.orientation.hom orientation.inv

private theorem word_comp {T : Scheme.{u}} (n : ℕ)
    {K L M : SpTowerP1.LevelWord l E n T}
    {f : K.tower ⟶ L.tower} {g : L.tower ⟶ M.tower}
    {f' : K.etale ⟶ L.etale} {g' : L.etale ⟶ M.etale}
    (hf : SpTowerP1.WordComparison l E n K L f f')
    (hg : SpTowerP1.WordComparison l E n L M g g') :
    SpTowerP1.WordComparison l E n K M (f ≫ g) (f' ≫ g') := by
  refine ⟨hf.1, hg.2.1, ?_⟩
  rw [Functor.map_comp, reassoc_of% hf.2.2, hg.2.2, Functor.map_comp]
  simp only [Category.assoc, Functor.comp_map]

private theorem word_pull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (g : SpTowerShriek.Geometry l E b f)
    (gc : SpTowerP1.GeometricCoordinates l E n f)
    {K L : SpTowerP1.LevelWord l E n Y}
    {v : K.tower ⟶ L.tower} {v' : K.etale ⟶ L.etale}
    (h : SpTowerP1.WordComparison l E n K L v v') :
    SpTowerP1.WordComparison l E n
      (SpTowerP1.pullWord l E n b g gc K) (SpTowerP1.pullWord l E n b g gc L)
      ((SpTowerShriek.pull l E b g).map v)
      ((Etale.ordinaryFinitePullback (SpTowerP1.levelRing l E n) f).map v') := by
  letI : Finite (SpTowerShriek.R l E n) := b.finite n
  letI : (SpTowerP1.realization l E n X).Additive := SpTowerP1.realizationAdditive l E n X
  letI : PreservesFiniteLimits (SpTowerP1.realization l E n X) :=
    SpTowerP1.realizationLimits l E n X
  letI : PreservesFiniteColimits (SpTowerP1.realization l E n X) :=
    SpTowerP1.realizationColimits l E n X
  haveI := h.1
  haveI := h.2.1
  refine ⟨by dsimp only [SpTowerP1.pullWord]; infer_instance,
    by dsimp only [SpTowerP1.pullWord]; infer_instance, ?_⟩
  have hd := (g.pullEvaluation n).inv.naturality v
  have hp := gc.pull.inv.naturality
    ((comparisonUpperStar (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n))
      Y).mapDerivedCategory.map v')
  have hs := (SpTowerP1.exactSitePull l E n f).hom.naturality v'
  simp only [Functor.comp_map] at hd hp hs
  dsimp only [SpTowerP1.pullWord]
  simp only [SpTowerP1.nu, Functor.comp_map, Category.assoc] at h ⊢
  rw [← hd, ← Functor.map_comp_assoc, h.2.2, Functor.map_comp_assoc]
  simp only [SpTowerP1.nu, Functor.comp_map]
  have hpaste := congrArg
    (fun k => (SpTowerP1.realization l E n X).mapDerivedCategory.map
      ((SpTowerP1.exactSitePull l E n f).hom.app K.etale) ≫ k ≫
        (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).map
          L.comparison ≫ (g.pullEvaluation n).inv.app L.tower) hp.symm
  simp only [Category.assoc] at hpaste
  have hsite := congrArg
    (fun k => (SpTowerP1.realization l E n X).mapDerivedCategory.map k) hs.symm
  have hfinish := congrArg
    (fun k => k ≫ gc.pull.inv.app
      ((comparisonUpperStar (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n))
        Y).mapDerivedCategory.obj L.etale) ≫
        (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).map
          L.comparison ≫ (g.pullEvaluation n).inv.app L.tower) hsite
  simp only [Functor.map_comp, Category.assoc] at hfinish
  exact hpaste.trans hfinish

private theorem orientation_level_exists {X V Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ V) [IsOpenImmersion j] (p : V ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) (w : SpChartAdmissibility.Twists l E X)
    (P : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization j p))
    (a : SpTowerGamma.Purity l E b o q j p d w P.closed P.right P.adj P.levels)
    (n : ℕ) : Nonempty (TowerOrientationLevel l E b o q j p d w P a n) := by
  obtain ⟨dg, alpha, hd, ui, hu, ha, _⟩ := a.finite_levels n
  refine ⟨⟨dg, alpha, hd, ui, hu, ?_⟩⟩
  exact tower_orientation_word_normalized l E b o q j p
    P.closed P.right P.adj P.levels a.unit_mem n ui
    (SpTowerGamma.coefficientWord l E b X w a.roots n (a.unitsX n)
      (a.coefficientsX n) (a.tensors n) d) a.orientation.hom alpha.inv ha

private theorem concentrated_of_iso {X : Scheme.{u}} (d e : ℕ)
    {M N : SpTowerShriek.D l E X} (v : M ≅ N)
    (h : (∀ i : ℤ, i ≠ -2 * ((d + e : ℕ) : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor (SpTowerShriek.S l E X) i).obj M)) ∧
      ∀ n : ℕ, ((SpTowerShriek.ev l E X n).obj
        ((DerivedCategory.homologyFunctor (SpTowerShriek.S l E X)
          (-2 * ((d + e : ℕ) : ℤ))).obj M)).IsFiniteLocallyFreeOfRank 1) :
    (∀ i : ℤ, i ≠ -2 * ((d + e : ℕ) : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor (SpTowerShriek.S l E X) i).obj N)) ∧
      ∀ n : ℕ, ((SpTowerShriek.ev l E X n).obj
        ((DerivedCategory.homologyFunctor (SpTowerShriek.S l E X)
          (-2 * ((d + e : ℕ) : ℤ))).obj N)).IsFiniteLocallyFreeOfRank 1 := by
  refine ⟨fun i hi ↦ (h.1 i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso v).symm, ?_⟩
  intro n
  letI := h.2 n
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    ((SpTowerShriek.ev l E X n).mapIso
      ((DerivedCategory.homologyFunctor _ _).mapIso v))

section Composite
variable {X Y Z V W U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  (jf : X ⟶ V) [IsOpenImmersion jf] (pf : V ⟶ Y) [IsProper pf]
  (jg : Y ⟶ W) [IsOpenImmersion jg] (pg : W ⟶ Z) [IsProper pg]
  (jh : X ⟶ U) [IsOpenImmersion jh] (ph : U ⟶ Z) [IsProper ph]
  [QuasiCompact (jf ≫ pf)] [QuasiCompact (jg ≫ pg)] [QuasiCompact (jh ≫ ph)]
  [HasCompactification (jf ≫ pf)] [HasCompactification (jg ≫ pg)]
  [HasCompactification (jh ≫ ph)]
  (d e : ℕ) (wf : SpChartAdmissibility.Twists l E X)
  (wg : SpChartAdmissibility.Twists l E Y) (wh : SpChartAdmissibility.Twists l E X)
  (Pf : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jf pf))
  (Pg : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jg pg))
  (Ph : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jh ph))
  (af : SpTowerGamma.Purity l E b o q jf pf d wf Pf.closed Pf.right Pf.adj Pf.levels)
  (ag : SpTowerGamma.Purity l E b o q jg pg e wg Pg.closed Pg.right Pg.adj Pg.levels)
  (ah : SpTowerGamma.Purity l E b o q jh ph (d + e) wh
    Ph.closed Ph.right Ph.adj Ph.levels)
  (c : Ph.right ≅ Pg.right ⋙ Pf.right)

private theorem tower_rho_isIso :
    IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag) := by
  let K := towerOmegaG l E b o q jg pg e wg Pg ag
  let t := (SpTowerShriek.tensor l E b X).mapIso
    (Iso.prod (Iso.refl
      ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
        ((SpTowerGamma.realization l E b q Y).obj K))) af.orientation)
  haveI := af.purity_iso K
  exact IsIso.of_isIso_fac_left (f := t.hom)
    (h := SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jf pf) wf d
      af.tensorX af.tensorY Pf.closed Pf.right Pf.adj af.unit_mem af.orientation K
      (af.tensor_mem K) (af.projection_iso K)) rfl

/-- The common target W=f*omega_g tensor omega_f, in ordinary system coordinates.
Source: tower paragraph (1) (blueprint: lem-sp-tower-orientation-evaluation). -/
abbrev towerOrientationTarget :=
  (SpTowerGamma.tensorSource l E b o q (jf ≫ pf)
    ((SpTowerGamma.exceptional l E b q Pf.right).obj
      ⟨SpTowerGamma.originalUnit l E b q Y, af.unit_mem⟩)).obj
        (towerOmegaG l E b o q jg pg e wg Pg ag)

/-- Phi is the diagonal orientation followed by the specified mu, before evaluation.
Source: tower paragraph (1) (blueprint: lem-sp-tower-orientation-evaluation). -/
def towerOrientationPhi
    (hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag)) :=
  ah.orientation.hom ≫
    (towerMu l E b o q jf pf jg pg jh ph d e wf wg Pf Pg Ph af ag c hR).hom

/-- Psi is the pullback/tensor of the specified orientations, after Tate splitting.
Source: tower paragraph (1) (blueprint: lem-sp-tower-orientation-evaluation). -/
def towerOrientationPsi
    (s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d)) :=
  s.hom ≫ (SpTowerShriek.tensor l E b X).map
    (Prod.mkHom ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map ag.orientation.hom)
      af.orientation.hom)

/-- The finite target comparison is built from the actual right-adjoint, pullback,
and tensor comparison words, fixing both endpoints of every evaluated arrow.
Source: tower paragraph (1) (blueprint: lem-sp-tower-orientation-evaluation). -/
def towerOrientationTargetWord (n : ℕ)
    (F : TowerOrientationLevel l E b o q jf pf d wf Pf af n)
    (G : TowerOrientationLevel l E b o q jg pg e wg Pg ag n) :=
  SpTowerP1.tensorWord l E n b (af.tensors n)
    (SpTowerP1.pullWord l E n b (o.geometry (jf ≫ pf)) (af.geometry n)
      (SpTensorTranspose.dualizingWord l E b o q jg pg
        Pg.closed Pg.right Pg.adj Pg.levels ag.unit_mem n G.unit))
    (SpTensorTranspose.dualizingWord l E b o q jf pf
      Pf.closed Pf.right Pf.adj Pf.levels af.unit_mem n F.unit)

/-- Concentration is asserted in the ambient ordinary tower category. The surviving
cohomology system has locally free rank-one evaluation at every positive level.
Source: tower paragraph (1) (blueprint: lem-sp-tower-orientation-evaluation). -/
def TowerOrientationConcentrated (M : SpTowerShriek.D l E X) : Prop :=
  (∀ i : ℤ, i ≠ -2 * ((d + e : ℕ) : ℤ) →
    IsZero ((DerivedCategory.homologyFunctor (SpTowerShriek.S l E X) i).obj M)) ∧
  ∀ n : ℕ, ((SpTowerShriek.ev l E X n).obj
    ((DerivedCategory.homologyFunctor (SpTowerShriek.S l E X)
      (-2 * ((d + e : ℕ) : ℤ))).obj M)).IsFiniteLocallyFreeOfRank 1

/-- The reduction square of one of the constructed maps, transported back by the
section-preserving equivalence to the original strict coefficient-tower category.
Source: tower paragraph (1), quotient transitions
(blueprint: lem-sp-tower-orientation-evaluation). -/
def TowerOrientationReduction {M N : SpTowerShriek.D l E X} (v : M ⟶ N) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
          ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map v)) ≫
      SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h)
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj N) =
    SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h)
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj M) ≫
      (spDerivedCoefficientEvaluation l E X (q.abelian X) m).map
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map v)

/-- Evaluation and concentration of the two composite orientation arrows. This does
not assert equality of Phi and Psi, or faithfulness on arbitrary derived Hom groups.
Source: composition-factors proof (1), tower paragraph and unit proof tower paragraph
(blueprint: lem-sp-tower-orientation-evaluation).

Proof:
1. Smooth relative dimensions add, and separated morphisms compose. Apply tower-gamma
and tower-gluing to f,g,h. The degree-zero coefficient tower has uniform intervals
[0,0]; its exceptional images, including omega_g, are admissible unnormalized inputs.
Finite-general-ring identifies the diagonal orientations with scalar extension.
2. Twisted-pullback-tower-domain supplies the tensor-source and projection domains at
omega_g. Gamma factors as rho after tensoring the orientation. Gamma and that tensor
factor are invertible; hence the actual rho is invertible.
3. Tower-tensor-transpose-evaluation identifies rho with the finite counit tensor map.
Composition-comparisons identifies c with the finite exceptional compositor, preserving
units, counits and reductions. Functors preserve composition and inverses, giving Phi's
finite formula. No equality is detected by evaluating arbitrary derived morphisms.
4. Semilinear-derived-sections gives actual ordinary pullback/tensor tower functors.
Finite-twist-pullback and diagram-pullback-monoidal-shift-models give the Tate splitting
with quotient transitions. Both shifts are even, so the interchange sign is +1.
Bifunctoriality gives Psi's finite formula. Naturality gives both reduction squares,
including equal indices, where reduction is the tensor unitor.
5. Twist-sheaf-locally-free makes every finite Tate line locally free of rank one.
Use ell=unit times uniformizer^a and level a(n+1), also for ramified E. Positive
powers stay lines; the zeroth power is the coefficient unit. Tensor with these lines
is levelwise exact, hence exact on towers by coefficient-towers-abelian.
6. The shifted Tate tower has cohomology only in degree -2(d+e). The isomorphism Psi
transports this concentration to W. Exact evaluation of the surviving cohomology
system is the finite Tate line. The empty scheme gives zero systems and vacuous
local rank-one assertions; no normalization of input towers is used. -/
theorem tower_orientation_evaluation
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [(jf ≫ pf).IsOver (Spec (.of D.k))] [(jg ≫ pg).IsOver (Spec (.of D.k))]
    [IsSeparated (jf ≫ pf)] [IsSeparated (jg ≫ pg)]
    [SmoothOfRelativeDimension d (jf ≫ pf)] [SmoothOfRelativeDimension e (jg ≫ pg)]
    (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (pres : SpTowerCalculus.Preservation l E D.k b o q)
    (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
    (alpha : TowerAdjointCompositor.left l E b o q Pf ⋙
      TowerAdjointCompositor.left l E b o q Pg ≅ TowerAdjointCompositor.left l E b o q Ph)
    (_ha : ∀ M, (alpha.hom.app M).hom =
      (cal.composition.composition (jf ≫ pf) (jg ≫ pg) (jh ≫ ph) hcomp
        (SpTowerGamma.factorization jf pf) (SpTowerGamma.factorization jg pg)
        (SpTowerGamma.factorization jh ph)).hom.app M)
    (_hc : ∀ K,
      (TowerAdjointCompositor.left l E b o q Pf ⋙
        TowerAdjointCompositor.left l E b o q Pg).map (c.hom.app K) ≫
          (Pf.adj.comp Pg.adj).counit.app K =
        alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K) :
    ∃ hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag),
    ∃ s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d),
      TowerSplitNormalized l E b o q jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah s ∧
      TowerOrientationConcentrated l E d e (SpTowerGamma.orderedLine l E b X wh (d + e)) ∧
      TowerOrientationConcentrated l E d e
        (towerOrientationTarget l E b o q jf pf jg pg d e wf wg Pf Pg af ag) ∧
      TowerOrientationReduction l E b q
        (towerOrientationPhi l E b o q jf pf jg pg jh ph d e wf wg wh
          Pf Pg Ph af ag ah c hR) ∧
      TowerOrientationReduction l E b q
        (towerOrientationPsi l E b o q jf pf jg pg d e wf wg wh Pf Pg af ag s) ∧
      ∀ n : ℕ,
        ∃ F : TowerOrientationLevel l E b o q jf pf d wf Pf af n,
        ∃ G : TowerOrientationLevel l E b o q jg pg e wg Pg ag n,
        ∃ H : TowerOrientationLevel l E b o q jh ph (d + e) wh Ph ah n,
        ∃ hr : IsIso (finiteRho (SpTowerP1.levelRing l E n) (jf ≫ pf) (jg ≫ pg)),
          SpTowerP1.WordComparison l E n
            (SpTowerGamma.coefficientWord l E b X wh ah.roots n (ah.unitsX n)
              (ah.coefficientsX n) (ah.tensors n) (d + e))
            (towerOrientationTargetWord l E b o q jf pf jg pg d e wf wg Pf Pg af ag n F G)
            (towerOrientationPhi l E b o q jf pf jg pg jh ph d e wf wg wh
              Pf Pg Ph af ag ah c hR)
            (H.orientation.inv ≫
              (Etale.rightDerivedUpperShriekCongr (SpTowerP1.levelRing l E n)
                hcomp.symm).hom.app (MonoidalCategory.tensorUnit _) ≫
              (finiteMu (SpTowerP1.levelRing l E n) (jf ≫ pf) (jg ≫ pg) hr).hom) ∧
          SpTowerP1.WordComparison l E n
            (SpTowerGamma.coefficientWord l E b X wh ah.roots n (ah.unitsX n)
              (ah.coefficientsX n) (ah.tensors n) (d + e))
            (towerOrientationTargetWord l E b o q jf pf jg pg d e wf wg Pf Pg af ag n F G)
            (towerOrientationPsi l E b o q jf pf jg pg d e wf wg wh Pf Pg af ag s)
            ((finiteLineSplit (SpTowerP1.levelRing l E n) (jf ≫ pf) (l ^ (n + 1))
                (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n)
                (ag.unitsX n) e d).hom ≫
              ((Etale.derivedTensor (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) X).map
                ((Etale.ordinaryFinitePullback (SpTowerP1.levelRing l E n) (jf ≫ pf)).map
                  G.orientation.inv)).app _ ≫
              ((Etale.derivedTensor (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) X).obj
                _).map F.orientation.inv) := by
  have hR := tower_rho_isIso l E b o q jf pf jg pg d e wf wg Pf Pg af ag
  obtain ⟨s, hs⟩ := tower_tate_split_normalized l E b o q
    jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah D _hl hcomp
  have hline := ordered_tate_tower_cohomology l E b D _hl X wh (d + e)
  let psiIso := s ≪≫ (SpTowerShriek.tensor l E b X).mapIso
    (Iso.prod ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).mapIso ag.orientation)
      af.orientation)
  have htarget := concentrated_of_iso l E d e psiIso hline
  refine ⟨hR, s, hs, hline, htarget, ?_, ?_, ?_⟩
  · intro m n h
    exact cal.reduction.reduction_naturality X h
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map _)
  · intro m n h
    exact cal.reduction.reduction_naturality X h
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map _)
  · intro n
    let F : TowerOrientationLevel l E b o q jf pf d wf Pf af n :=
      Classical.choice (orientation_level_exists l E b o q jf pf d wf Pf af n)
    let G : TowerOrientationLevel l E b o q jg pg e wg Pg ag n :=
      Classical.choice (orientation_level_exists l E b o q jg pg e wg Pg ag n)
    let H : TowerOrientationLevel l E b o q jh ph (d + e) wh Ph ah n :=
      Classical.choice (orientation_level_exists l E b o q jh ph (d + e) wh Ph ah n)
    obtain ⟨hr, hm⟩ := tower_mu_evaluation l E b o q
      jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah c
      D _hl hcomp z pres cal alpha _ha _hc hR n
      F.unit F.unit_normalized G.unit G.unit_normalized H.unit H.unit_normalized
    refine ⟨F, G, H, hr, ?_, ?_⟩
    · exact word_comp l E b n H.evaluated hm
    · exact word_comp l E b n (hs n)
        (tensor_word_comparison l E b n (af.tensors n)
          (word_pull l E b (jf ≫ pf) n (o.geometry (jf ≫ pf))
            (af.geometry n) G.evaluated) F.evaluated)

end Composite
end AlgebraicGeometry.ProEtale.SpCompositionFactors
