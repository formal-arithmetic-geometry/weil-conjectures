# AlgebraicGeometry.ProEtale.SpTowerGamma: shared data extraction

## Reason

The actual transpose-evaluation and twisted-domain lemmas import
SmoothPurityTowerGamma for its map definitions. The tower theorem now uses these lemmas.
Keeping their old import would create a cycle. Extract the existing twenty data
and predicate declarations verbatim into SmoothPurityTowerGammaData and publicly
re-export them from SmoothPurityTowerGamma. No target statement or mathematical
definition changes, and no source-library module changes. This is extraction to
resolve an actual import cycle, not splitting a slow declaration.

## Old

These declarations, in namespace AlgebraicGeometry.ProEtale.SpTowerGamma with the
original universe and section variables, occur in SmoothPurityTowerGamma:

```lean
/-- The actual full inclusion followed by the section-preserving system realization.
Source: gamma (1)--(3), ordinary derived towers (blueprint: det-sp-tower-gamma). -/
def realization (T : Scheme.{u}) :=
  SpTowerCalculus.inclusion l E b q T ⋙
    (SpTowerCalculus.realization l E b T (q.abelian T)).functor

/-- The coefficient tower in degree zero, in the published section coordinates.
Source: gamma (1), O_E/ell^bullet (blueprint: det-sp-tower-gamma). -/
abbrev unit (T : Scheme.{u}) := SpTowerClasses.unit T (SpTowerClasses.Arings l E T)

/-- The Tate coefficient line with its even shift, written as the ordered product
of d shifted degree-one lines. This is the same convention as finite smooth purity.
Source: clauses (1)--(2), O_X(d)[2d] (blueprint: det-sp-tower-gamma). -/
def orderedLine (T : Scheme.{u}) (w : SpChartAdmissibility.Twists l E T) :
    ℕ → SpTowerShriek.D l E T
  | 0 => unit l E T
  | d + 1 => (SpTowerShriek.tensor l E b T).obj
      (orderedLine T w d, (SpCoordinateAdjunction.line l E w 1)⟦(2 : ℤ)⟧)

/-- The levelwise pullback with the ordered positive Tate line and shift.
Source: clause (2), canonical tensor presentation (blueprint: det-sp-tower-gamma). -/
def source {X Y : Scheme.{u}} (f : X ⟶ Y)
    (w : SpChartAdmissibility.Twists l E X) (d : ℕ) :=
  realization l E b q Y ⋙ SpTowerShriek.pull l E b (o.geometry f) ⋙
    Prod.sectL (SpTowerShriek.D l E X) (orderedLine l E b X w d) ⋙
      SpTowerShriek.tensor l E b X

/-- The coefficient unit in the original strict-tower category, transported by the
specified inverse realization. Source: clause (1) (blueprint: det-sp-tower-gamma). -/
def originalUnit (T : Scheme.{u}) :=
  (SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj (unit l E T)

/-- The given exceptional image, in the section-preserving ordinary system coordinates.
Source: clauses (1)--(2) (blueprint: det-sp-tower-gamma). -/
def exceptional {X Y : Scheme.{u}}
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X) :=
  G ⋙ realization l E b q X

/-- The actual compact-support counit, conjugated only by the fixed realization.
Source: epsilon in clause (2) (blueprint: det-sp-tower-gamma). -/
def counit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (K : SpTowerCalculus.C l E b q Y) :
    (SpTowerShriek.F l E b o c).obj ((exceptional l E b q G).obj K) ⟶
      (realization l E b q Y).obj K :=
  (SpCoordinateAdjunction.supportRealization l E b o q c).inv.app (G.obj K).obj ≫
    (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.map
      (adj.counit.app K).hom

/-- The untwisted tensor source of the canonical exceptional tensor mate.
Source: t_K in clause (2) (blueprint: det-sp-tower-gamma). -/
def tensorSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : SpTowerShriek.D l E X) : SpTowerCalculus.C l E b q Y ⥤ SpTowerShriek.D l E X :=
  realization l E b q Y ⋙ SpTowerShriek.pull l E b (o.geometry f) ⋙
    Prod.sectL (SpTowerShriek.D l E X) W ⋙ SpTowerShriek.tensor l E b X

/-- Inverse projection, symmetry, identity tensor the actual counit, and the scalar
unitor. This is the displayed arrow whose adjunct is t_K.
Source: clause (2), displayed PF composite (blueprint: det-sp-tower-gamma). -/
def projectionCounit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (tx : SpTowerP1.TensorData l E b X) (ty : SpTowerP1.TensorData l E b Y)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (hU : spConstructibleTorTowers l E Y (q.abelian Y) (originalUnit l E b q Y))
    (K : SpTowerCalculus.C l E b q Y)
    (hpf : IsIso (SpTowerShriek.projection l E b o c
      ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)
      ((realization l E b q Y).obj K))) :
    (SpTowerShriek.F l E b o c).obj
        ((tensorSource l E b o q f
          ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)).obj K) ⟶
      (realization l E b q Y).obj K :=
  (SpTowerShriek.F l E b o c).map
      (((tx.symmetry l E).braiding _ _).hom) ≫
    @inv _ _ _ _ (SpTowerShriek.projection l E b o c
      ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)
      ((realization l E b q Y).obj K)) hpf ≫
    ((ty.symmetry l E).braiding _ _).hom ≫
    (SpTowerShriek.tensor l E b Y).map (Prod.mkHom (𝟙 _)
      (counit l E b o q c hF G adj ⟨originalUnit l E b q Y, hU⟩ ≫
        (SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso.hom.app
          (unit l E Y))) ≫
    (ty.rightUnit l E _).hom

/-- The actual adjunction transpose. The full inclusion and the section-preserving
realization supply the unique Hom lifts; no family of level maps is lifted by choice.
Source: t_K in clause (2) (blueprint: det-sp-tower-gamma). -/
def tensorMate {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (tx : SpTowerP1.TensorData l E b X) (ty : SpTowerP1.TensorData l E b Y)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (hU : spConstructibleTorTowers l E Y (q.abelian Y) (originalUnit l E b q Y))
    (K : SpTowerCalculus.C l E b q Y)
    (hQ : spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((tensorSource l E b o q f
          ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)).obj K)))
    (hpf : IsIso (SpTowerShriek.projection l E b o c
      ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)
      ((realization l E b q Y).obj K))) :
    (tensorSource l E b o q f
      ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)).obj K ⟶
        (exceptional l E b q G).obj K :=
  (SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.inv.app _ ≫
    (SpTowerCalculus.realization l E b X (q.abelian X)).functor.map
      (((adj.homEquiv ⟨_, hQ⟩ K)
        (ObjectProperty.homMk
          ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.preimage
            ((SpCoordinateAdjunction.supportRealization l E b o q c).hom.app _ ≫
              (SpTowerShriek.F l E b o c).map
                ((SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.hom.app _) ≫
              projectionCounit l E b o q c tx ty hF G adj hU K hpf)))).hom)

/-- In the ordered shifted tensor presentation of the source, tensor the diagonal
orientation and take the actual projection/counit transpose before evaluation.
Source: clause (2), gamma's displayed formula (blueprint: det-sp-tower-gamma). -/
def gamma {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
    (tx : SpTowerP1.TensorData l E b X) (ty : SpTowerP1.TensorData l E b Y)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (hU : spConstructibleTorTowers l E Y (q.abelian Y) (originalUnit l E b q Y))
    (a : orderedLine l E b X w d ≅
      (exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)
    (K : SpTowerCalculus.C l E b q Y)
    (hQ : spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((tensorSource l E b o q f
          ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)).obj K)))
    (hpf : IsIso (SpTowerShriek.projection l E b o c
      ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)
      ((realization l E b q Y).obj K))) :
    (source l E b o q f w d).obj K ⟶ (exceptional l E b q G).obj K :=
  (SpTowerShriek.tensor l E b X).map (Prod.mkHom (𝟙 _) a.hom) ≫
    tensorMate l E b o q c tx ty hF G adj hU K hQ hpf

/-- The root-normalized shifted degree-one word, with the same finite root projection
as the coordinate construction. Source: clause (1) (blueprint: det-sp-tower-gamma). -/
def rootWord (T : Scheme.{u}) (w : SpChartAdmissibility.Twists l E T)
    (roots : SpCoordinateAdjunction.RootLines l E T) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (cc : SpTowerP1.CoefficientCoordinates l E n T hT) : SpTowerP1.LevelWord l E n T where
  tower := (SpCoordinateAdjunction.line l E w 1)⟦(2 : ℤ)⟧
  etale := (Etale.ordinaryFiniteLine (SpTowerP1.levelRing l E n) (l ^ (n + 1))
    (SpTowerP1.levelAnnihilates l E n) T)⟦(2 : ℤ)⟧
  comparison := (((SpTowerP1.nu l E n T).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (SpTowerP1.nuSingle l E n T _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (cc.line ≪≫ (roots.iso n).symm ≪≫ (w.level n 1).symm) ≪≫
        (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm) ≪≫
    (((SpTowerShriek.Ev l E T n).commShiftIso (2 : ℤ)).app _).symm).hom

/-- Recursively form the actual tensor-evaluation word; all endpoint arrows are fixed
by the normalized site and K-flat comparisons. Source: clause (1)
(blueprint: det-sp-tower-gamma). -/
def lineWord (T : Scheme.{u}) (w : SpChartAdmissibility.Twists l E T)
    (roots : SpCoordinateAdjunction.RootLines l E T) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (cc : SpTowerP1.CoefficientCoordinates l E n T hT)
    (tc : SpTowerP1.TensorCoordinates l E n b T) : ∀ d : ℕ,
    (SpTowerP1.nu l E n T).obj
      (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
        (SpTowerP1.levelAnnihilates l E n) T d) ⟶
      (SpTowerShriek.Ev l E T n).obj (orderedLine l E b T w d)
  | 0 => (SpTowerP1.unitWord l E n T cc).comparison
  | d + 1 => (SpTowerP1.tensorWord l E n b tc
      ⟨orderedLine l E b T w d,
        Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) T d,
        lineWord T w roots n hT cc tc d⟩
      (rootWord l E T w roots n hT cc)).comparison

/-- Package the explicitly constructed ordered coefficient comparison.
Source: clause (1), diagonal source (blueprint: det-sp-tower-gamma). -/
def coefficientWord (T : Scheme.{u}) (w : SpChartAdmissibility.Twists l E T)
    (roots : SpCoordinateAdjunction.RootLines l E T) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (cc : SpTowerP1.CoefficientCoordinates l E n T hT)
    (tc : SpTowerP1.TensorCoordinates l E n b T) (d : ℕ) :
    SpTowerP1.LevelWord l E n T :=
  ⟨orderedLine l E b T w d,
    Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
      (SpTowerP1.levelAnnihilates l E n) T d,
    lineWord l E b T w roots n hT cc tc d⟩

/-- The given right-adjoint output in its retained ordinary etale origin, with the
specified finite adjunction comparison and exact evaluation factors.
Source: clauses (1)--(2), finite evaluations (blueprint: det-sp-tower-gamma). -/
def targetWord {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q c hF G adj) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (K : SpTowerCalculus.C l E b q Y) : SpTowerP1.LevelWord l E n X where
  tower := (exceptional l E b q G).obj K
  etale := (lv.realization n).right.obj
    ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))
  comparison := ((lv.realization n).rightIso.inv.app _ ≫
    ((lv.comparison n).inv.app K).hom) ≫
    (SpTowerCalculus.levelComparison l E b q X n).inv.app (G.obj K).obj

/-- The retained ordinary origin of a tower input, followed by its specified
section-preserving evaluation. Source: clause (2) (blueprint: det-sp-tower-gamma). -/
def inputWord {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q c hF G adj) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (K : SpTowerCalculus.C l E b q Y) : SpTowerP1.LevelWord l E n Y where
  tower := (realization l E b q Y).obj K
  etale := (lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)
  comparison := (lv.realization n).originIso.hom.app _ ≫
    (SpTowerCalculus.levelComparison l E b q Y n).inv.app K.obj

/-- The actual compactification specified by an open/proper factorization.
Source: clause (2), projection mate on a compactification
(blueprint: det-sp-tower-gamma). -/
def factorization {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [IsProper p] : Compactification (j ≫ p) :=
  ⟨Z, p, j, rfl, inferInstance, inferInstance⟩

/-- Unique comparison of ordinary right adjoints, using the canonical compactification
comparison on the left. Thus it preserves the actual counit.
Source: clauses (1)--(2), finite adjunction identifications
(blueprint: det-sp-tower-gamma). -/
def finiteRightComparison (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adj : reductionCtfCompactSupport A j p hF ⊣ G)
    (r : ReductionExceptionalRealization A j p hF G adj) :
    r.right ≅ Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) (j ≫ p) :=
  r.adjunction.rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) (j ≫ p)).ofNatIsoLeft
        (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A) (factorization j p)).symm)

/-- The finite diagonal and purity equations with the prescribed normalized word maps.
Factoring out this proposition keeps the tower structure's generated recursors small.
Source: clauses (1)--(2), every positive level (blueprint: det-sp-tower-gamma). -/
def FiniteLevels {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj)
    (unit_mem : spConstructibleTorTowers l E Y (q.abelian Y) (originalUnit l E b q Y))
    (tensorX : SpTowerP1.TensorData l E b X) (tensorY : SpTowerP1.TensorData l E b Y)
    (roots : SpCoordinateAdjunction.RootLines l E X)
    (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (coefficientsX : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.CoefficientCoordinates l E n X (unitsX n))
    (unitsY : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
    (coefficientsY : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.CoefficientCoordinates l E n Y (unitsY n))
    (tensors : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.TensorCoordinates l E n b X)
    (geometry : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.GeometricCoordinates l E n (j ≫ p))
    (orientation : orderedLine l E b X w d ≅
      (exceptional l E b q G).obj ⟨originalUnit l E b q Y, unit_mem⟩)
    (tensor_mem : ∀ K : SpTowerCalculus.C l E b q Y,
      spConstructibleTorTowers l E X (q.abelian X)
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
          ((tensorSource l E b o q (j ≫ p)
            ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, unit_mem⟩)).obj K)))
    (projection_iso : ∀ K : SpTowerCalculus.C l E b q Y,
      IsIso (SpTowerShriek.projection l E b o (factorization j p)
        ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, unit_mem⟩)
        ((realization l E b q Y).obj K))) : Prop :=
  ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    ∃ dg : Etale.FiniteRingSectionDeformation.Geometry d
        (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p)),
    ∃ alpha : Etale.dualizingComplex (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) (j ≫ p) ≅
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n)
          (l ^ (n + 1)) (SpTowerP1.levelAnnihilates l E n) X d),
      Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n)
        (j ≫ p) d dg (unitsX n) alpha ∧
    ∃ ui : ((lv.realization n).origin.obj
        ((SpTowerGluing.level l E b q Y n).obj
          ⟨originalUnit l E b q Y, unit_mem⟩)) ≅
        Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Y,
      (SpTowerP1.nu l E n Y).map ui.hom ≫
          (SpTowerP1.unitWord l E n Y (coefficientsY n)).comparison =
        (inputWord l E b o q (factorization j p) hF G adj lv n
          ⟨originalUnit l E b q Y, unit_mem⟩).comparison ≫
          (SpTowerShriek.Ev l E Y n).map
            ((SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso.hom.app
              (unit l E Y)) ∧
      SpTowerP1.WordComparison l E n
        (coefficientWord l E b X w roots n (unitsX n) (coefficientsX n) (tensors n) d)
        (targetWord l E b o q (factorization j p) hF G adj lv n
          ⟨originalUnit l E b q Y, unit_mem⟩) orientation.hom
        (alpha.inv ≫ (finiteRightComparison (SpTowerShriek.R l E n) j p
            (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _ ≫
          (lv.realization n).right.map ui.inv) ∧
      ∀ K : SpTowerCalculus.C l E b q Y,
        SpTowerP1.WordComparison l E n
          (SpTowerP1.tensorWord l E n b (tensors n)
            (SpTowerP1.pullWord l E n b (o.geometry (j ≫ p)) (geometry n)
              (inputWord l E b o q (factorization j p) hF G adj lv n K))
            (coefficientWord l E b X w roots n (unitsX n) (coefficientsX n) (tensors n) d))
          (targetWord l E b o q (factorization j p) hF G adj lv n K)
          (gamma l E b o q (factorization j p) w d tensorX tensorY hF G adj unit_mem
            orientation K (tensor_mem K) (projection_iso K))
          (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
            (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
              (SpTowerP1.levelAnnihilates l E n) X d) alpha
            ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ≫
          (finiteRightComparison (SpTowerShriek.R l E n) j p
            (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _)

/-- The three tower assertions, including the normalized finite diagonal orientation
and the actual map at every positive level. All data are asserted to exist by
` tower_gamma `; this structure does not choose an orientation or a purity map.
Source: clauses (1)--(3) (blueprint: det-sp-tower-gamma). -/
structure Purity {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj) where
  unit_mem : spConstructibleTorTowers l E Y (q.abelian Y) (originalUnit l E b q Y)
  tensorX : SpTowerP1.TensorData l E b X
  tensorY : SpTowerP1.TensorData l E b Y
  roots : SpCoordinateAdjunction.RootLines l E X
  unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))
  unitsY : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤))
  coefficientsX : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    SpTowerP1.CoefficientCoordinates l E n X (unitsX n)
  coefficientsY : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    SpTowerP1.CoefficientCoordinates l E n Y (unitsY n)
  tensors : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    SpTowerP1.TensorCoordinates l E n b X
  geometry : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    SpTowerP1.GeometricCoordinates l E n (j ≫ p)
  orientation : orderedLine l E b X w d ≅
    (exceptional l E b q G).obj ⟨originalUnit l E b q Y, unit_mem⟩
  tensor_mem : ∀ K : SpTowerCalculus.C l E b q Y,
    spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((tensorSource l E b o q (j ≫ p)
          ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, unit_mem⟩)).obj K))
  projection_iso : ∀ K : SpTowerCalculus.C l E b q Y,
    IsIso (SpTowerShriek.projection l E b o (factorization j p)
      ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, unit_mem⟩)
      ((realization l E b q Y).obj K))
  source_mem : ∀ K : SpTowerCalculus.C l E b q Y,
    spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((source l E b o q (j ≫ p) w d).obj K))
  purity_iso : ∀ K : SpTowerCalculus.C l E b q Y,
    IsIso (gamma l E b o q (factorization j p) w d tensorX tensorY hF G adj unit_mem
      orientation K (tensor_mem K) (projection_iso K))
  naturality : ∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
    (source l E b o q (j ≫ p) w d).map v ≫
        gamma l E b o q (factorization j p) w d tensorX tensorY hF G adj unit_mem
          orientation L (tensor_mem L) (projection_iso L) =
      gamma l E b o q (factorization j p) w d tensorX tensorY hF G adj unit_mem
        orientation K (tensor_mem K) (projection_iso K) ≫ (exceptional l E b q G).map v
  support_normalized : ∀ M : SpTowerCalculus.C l E b q X,
    IsSpNormalizedTower l E X (q.abelian X) M.obj →
      IsSpNormalizedTower l E Y (q.abelian Y)
        ((SpTowerGluing.support l E b o q (factorization j p) hF).obj M).obj
  exceptional_normalized : ∀ K : SpTowerCalculus.C l E b q Y,
    IsSpNormalizedTower l E Y (q.abelian Y) K.obj →
      IsSpNormalizedTower l E X (q.abelian X) (G.obj K).obj
  finite_levels : FiniteLevels l E b o q j p d w hF G adj lv unit_mem tensorX tensorY
    roots unitsX coefficientsX unitsY coefficientsY tensors geometry orientation tensor_mem
    projection_iso
```

## New

Every declaration in Old, including its docstring, signature, visibility and body,
occurs verbatim in SmoothPurityTowerGammaData under the same namespace and section
variables. The original module retains all its original public imports and adds:

```lean
public import Sheaf.Paper.SmoothPurityTowerGammaData
```

The proof dependency definition modules TwistedPullbackTowerDomainDefinitions
and TowerTensorTransposeWords change exactly line 8, from the public import of
SmoothPurityTowerGamma to:

```lean
public import Sheaf.Paper.SmoothPurityTowerGammaData
```

They use only the data, never tower_gamma; all their declarations are unchanged.
IntegralReconstructionComparisons now uses tower_gamma directly, and continues to
import the original module and its unchanged theorem signature. The original data
bodies were compared as exact text against the current shared source. The extraction
moves no unproved existence choice into a definition and adds no data-bearing definition.

## Users

The following is the current complete direct-importer list, obtained by scanning
lean/Sheaf for imports of SmoothPurityTowerGamma. Current claim holders were read
from coord/claims; unclaimed means no module claim file was present.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralAdjunctionBijection | S6 | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | B3 | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Same public declarations via original module re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComparison | unclaimed | Same public declarations via original module re-export; no adaptation (landed after the delivery base; added by the reviewer). |
| Sheaf.Paper.FieldExceptionalSystemDomains | unclaimed | Same public declarations via original module re-export; no adaptation (landed after the delivery base; added by the reviewer). |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed | Only line 8 imports GammaData; all declarations unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | Only line 8 imports GammaData; all declarations unchanged. |
| Sheaf.Paper.SmoothPurityTowerGamma | Q4 | Publicly re-exports identical data and supplies assembly proof. |

Both adapted modules are unclaimed. Keeping the original import produces the
cycles Gamma -> TwistedPullbackTowerDomain -> TwistedPullbackTowerDomainDefinitions
-> Gamma and Gamma -> TowerTensorTransposeEvaluation -> TowerTensorTransposeWords
-> Gamma. Import-cycle rejection precedes declaration elaboration. Replacing only
these two import edges removes all cycles in the main module's import closure.
No existing signature, visibility or body in either adapted module changes.
The recently landed domain and evaluation theorem proofs remain exactly as in
the current library; older holed copies were removed from the packet after the
first preflight caught the concurrent change. The normalization sublemma imports
only the data interface; the conjugacy module is unchanged.

## Recompiled unchanged dependencies

Published theorem interfaces still referenced the old defining module of the data.
Compiling Gamma against those interfaces and the extracted data failed with:

```text
import Sheaf.Paper.SmoothPurityTowerGamma failed, environment already contains
'AlgebraicGeometry.ProEtale.SpTowerGamma.inputWord' from
Sheaf.Paper.SmoothPurityTowerGammaData
```

This is a stale-artifact effect only: TowerTensorTransposeEvaluation,
TensorTransposeTowerNaturality, TensorTransposeFiniteEvaluation,
TwistedPullbackTowerDomain, TwistedPullbackTowerBounds and
TwistedPullbackTowerOrigins are not part of the delivery and have no source edits;
they are rebuilt unchanged in import order by the global build, which updates the
recorded module provenance. Their statements and proofs are preserved.

## Status

landed 20261025T202818-L-2755214 2026-10-25 (merge of deliver/Q4/Sheaf.Paper.SmoothPurityTowerGamma)
