module

public import Sheaf.Paper.ProEtaleAffineLineCounit

/-! # Canonical pro-etale ordered integration arrows
Source: main-20261015 vector-bundle integration and projective-line normalization
(blueprint: def-pur-proetale-ordered-integration).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)


set_option linter.unusedVariables false in
/-- Boundedness of every ordered Tate coefficient, including arbitrary D+ input.
Source: finite Tate lines are locally free and inverse image is exact
(blueprint: def-pur-proetale-ordered-integration).
Proof: each step tensors with a flat degree-zero line, shifts by two, and applies
exact inverse image. It lowers a lower bound by two. Induct on the number of
coordinates; the zero step is the identity. No flatness of A over Z/l^r occurs.
-/
theorem rightTower_plus (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    DerivedCategory.TStructure.t.plus
      ((Etale.affineTraceRight _ (l ^ (r + 1)) hA T d).obj K.obj) := by
  sorry

/-- The ordered pro-etale left composite. Zero coordinates means the identity.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
abbrev towerLeft (T : Scheme.{u}) (d : ℕ) :=
  Etale.affineTraceLeftTower
    (C := fun e ↦ DerivedCategory (Sheaf (Scheme.ProEt.topology (affineTraceTower T e))
      (ModuleCat.{u + 1} A))) (fun e ↦ lineLeft A (affineTraceTower T e)) d

/-- Ordered composition of coordinate counits, before specializing the categories.
Source: blueprint affine-space trace, composite-counit formula
(blueprint: def-pur-proetale-ordered-integration). -/
@[irreducible]
def orderedCounit {C : ℕ → Type v} [∀ d, Category.{w} (C d)]
    (L : ∀ d, C (d + 1) ⥤ C d) (J : ∀ d, C d)
    (e : ∀ d, (L d).obj (J (d + 1)) ⟶ J d) :
    (d : ℕ) → (Etale.affineTraceLeftTower L d).obj (J d) ⟶ J 0
  | 0 => 𝟙 _
  | d + 1 => (Etale.affineTraceLeftTower L d).map (e d) ≫ orderedCounit L J e d

/-- The family of Hom types in the ordered counit recursion.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
@[implicit_reducible]
def TowerCounitFamily (T : Scheme.{u}) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :=
  (d : ℕ) → (towerLeft (Scheme.finiteTateCoefficient l E n) T d).obj
    ((comparison (Scheme.finiteTateCoefficient l E n) (affineTraceTower T d)).obj
      ((Etale.affineTraceRight _ (l ^ (r + 1)) hA T d).obj K)) ⟶
    (comparison (Scheme.finiteTateCoefficient l E n) T).obj K

/-- Exact zero and successor equations for the ordered counit family.
HEq only avoids expanding the defining successor identification of the right tower.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
def TowerCounitRecursion (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (e : TowerCounitFamily l E n T r hA K.obj) : Prop :=
  HEq (e 0) (𝟙 ((comparison (Scheme.finiteTateCoefficient l E n) T).obj K.obj)) ∧
    ∀ d : ℕ,
      letI := affineTraceNoetherian T d
      HEq (e (d + 1))
        ((towerLeft (Scheme.finiteTateCoefficient l E n) T d).map
          (lineCounit l E n (affineTraceTower T d)
            (affineTraceInvertible l T hT d) (infinityCartier _) r hA
            ⟨_, rightTower_plus l E n T hT r hA d K⟩) ≫ e d)

/-- The ordered counit recursion determines the entire family uniquely.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration).
Proof: use orderedCounit on the line functors and the compared right objects,
identifying each successor by the defining recursion of affineTraceRightTower.
It satisfies the displayed zero
and successor equations. Induction on the number of coordinates proves equality
of any two such families; function extensionality concludes uniqueness.
-/
theorem existsUniqueTowerCounit (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    ∃! e : TowerCounitFamily l E n T r hA K.obj,
      TowerCounitRecursion l E n T hT r hA K e := by
  sorry

/-- The unique ordered composition of the actual pro-etale line counits.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
@[irreducible]
def towerCounit (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    TowerCounitFamily l E n T r hA K.obj :=
  (existsUniqueTowerCounit l E n T hT r hA K).exists.choose

/-- The canonical proper-mate/open-extension comparison for one coordinate.
Source: Stacks 099R and 09AF (blueprint: def-pur-proetale-ordered-integration). -/
@[irreducible]
def lineSiteComparison (T : Scheme.{u})
    (J : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} T).smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    (lineLeft A T).obj ((comparison A _).obj J.obj) ≅
      (comparison A T).obj ((Etale.affineTraceLineLeft A T).obj J.obj) :=
  (compactSupportSiteComparison A (affineTraceLineCompactification T)).app J

/-- Iterated canonical proper/open comparison; no counit or trace occurs in this map.
Source: Stacks 099R, 09AF and compact-support composition
(blueprint: def-pur-proetale-ordered-integration). -/
@[irreducible]
def towerSiteComparison (T : Scheme.{u}) : (d : ℕ) →
    (J : DerivedCategory.Plus (Sheaf (affineTraceTower T d).smallEtaleTopology
      (ModuleCat.{u + 1} A))) →
    (towerLeft A T d).obj ((comparison A _).obj J.obj) ≅
      (comparison A T).obj ((Etale.affineTraceLeft A T d).obj J.obj)
  | 0, _ => Iso.refl _
  | d + 1, J =>
    let L := Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower T d))
    let e := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) (affineTraceLineCompactification (affineTraceTower T d))).app J
    (towerLeft A T d).mapIso (lineSiteComparison A _ J) ≪≫
      (towerLeft A T d).mapIso ((comparison A _).mapIso e.symm) ≪≫
      towerSiteComparison T d (L.obj J) ≪≫
      (comparison A T).mapIso ((Etale.affineTraceLeft A T d).mapIso e)

/-- Ordered integration in ordinary-comparison source coordinates, with actual pro-etale
line counits in its body. The source comparison contains no ordinary integration map.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
@[irreducible]
def orderedIntegration (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (comparison (Scheme.finiteTateCoefficient l E n) T).obj
      ((Etale.affineTraceLeft _ T d).obj
        ((Etale.affineTraceRight _ (l ^ (r + 1)) hA T d).obj
          (Etale.ordinaryFiniteUnit _ T))) ⟶ unit (Scheme.finiteTateCoefficient l E n) T :=
  (towerSiteComparison (Scheme.finiteTateCoefficient l E n) T d
    ⟨_, rightTower_plus l E n T hT r hA d
      ⟨Etale.ordinaryFiniteUnit _ T, ⟨0, inferInstance⟩⟩⟩).inv ≫
    towerCounit l E n T hT r hA ⟨Etale.ordinaryFiniteUnit _ T, ⟨0, inferInstance⟩⟩ d


end AlgebraicGeometry.ProEtale.VectorIntegrationSite
