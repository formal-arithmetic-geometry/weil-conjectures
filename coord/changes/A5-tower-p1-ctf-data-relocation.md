# AlgebraicGeometry.ProEtale.SpTowerP1Uniform data declarations

## Reason

The parent theorem is reduced to three independent argument steps. Those new modules
must refer to its functors, interval predicate and LocalModel structure without importing
the theorem that uses them. Move exactly the six data declarations to
`Sheaf.Paper.TowerP1CtfData`, and publicly re-export that module from the original module.
Every name, signature, visibility, attribute and definition body is unchanged. This is
an import-cycle separation, not a mathematical definition or statement correction.
No adopted source-library file changes.

## Old

The following declarations were in `Sheaf.Paper.TowerP1UniformCtfDomains`, with its
original public imports. Verbatim declaration block:

```lean
/-- The proper tower image, in the original coefficient-tower coordinates.
Source: standing-setting restriction, proper q
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def push {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}
    (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S)) :=
  (spTowerShriekRealization l E c.base (ProjectiveLine S) DP).functor ⋙
    SpTowerShriek.push l E c.base c.projective.geometry ⋙
      (spTowerShriekRealization l E c.base S DS).inverse

/-- Exact tower inverse image, derived tensor with the recorded Tate line, and shift two.
Source: standing-setting restriction, q^*(-)(1)[2]
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def pullTwist {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}
    (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S)) :=
  (spTowerShriekRealization l E c.base S DS).functor ⋙
    SpTowerShriek.pull l E c.base c.projective.geometry ⋙
      Prod.sectL (SpTowerShriek.D l E (ProjectiveLine S))
        ((SpTowerClasses.line l E c.chernP)⟦(2 : ℤ)⟧) ⋙
      SpTowerShriek.tensor l E c.base (ProjectiveLine S) ⋙
        (spTowerShriekRealization l E c.base (ProjectiveLine S) DP).inverse

/-- The prescribed cohomological and Tor intervals, using intrinsic constructibility
with finite locally closed constructible stratifications, at every positive level.
Source: the more precise bounds (blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def bounds (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (K : spDerivedCoefficientTowers l E T D) (r s a b : ℤ) : Prop :=
  ∀ n : ℕ,
    DerivedCategory.IsGE ((spDerivedCoefficientEvaluation l E T D n).obj K) r ∧
    DerivedCategory.IsLE ((spDerivedCoefficientEvaluation l E T D n).obj K) s ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T (SpTowerShriek.R l E n)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj K))) ∧
    Scheme.HasProEtaleTorAmplitude T (SpTowerShriek.R l E n)
      ((spDerivedCoefficientEvaluation l E T D n).obj K) a b

/-- The literal termwise comparison pullback of the specified etale complex,
followed by the canonical associated-module-sheaf realization.
Source: the local pro-etale K-flat model
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def comparisonModel (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (C : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) :=
  ((finiteCoefficientIntrinsicRealization T A).mapHomologicalComplex (.up ℤ)).obj
    (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
      |>.mapHomologicalComplex (.up ℤ)).obj C)

/-- The actual etale inverse-image, root-line tensor and shift-two complex.
Source: the prescribed local model (blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def lineModel (A : Type u) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u})
    (C : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) :=
  Etale.etalePullbackLineModel (ULift.{u + 1} A) (ProjectiveLine T ↘ T) C
    (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
      (ULift.ext _ _ hA)) 2

/-- Retained etale and flat representatives, their specified pullback-line model, and
its actual pro-etale realization. The stratum clause is the existing pulled-back
stratification assertion, including finite local module values and common covers.
Source: the affine-local and global representative clauses; Stacks 03TT, 0963, 06YQ
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
structure LocalModel (A : Type u) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (K : Scheme.proEtaleDerivedCategory T A)
    (G : Scheme.proEtaleDerivedCategory (ProjectiveLine T) A) (r s a b : ℤ) where
  etale : DerivedCategory.Plus
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  etale_constructible : Etale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) T etale.obj
  etale_lower : DerivedCategory.IsGE etale.obj r
  etale_upper : DerivedCategory.IsLE etale.obj s
  etale_tor : Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T a b etale.obj
  origin : (finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
      |>.mapDerivedCategory.obj etale.obj) ≅ K
  complex : CochainComplex
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ
  represents : DerivedCategory.Q.obj complex ≅ etale.obj
  flat : Etale.IsBoundedFlatComplex (ULift.{u + 1} A) a b complex
  terms_constructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (complex.X i)
  cover : Scheme.Cover.{u} Scheme.etalePrecoverage (ProjectiveLine T)
  line_trivial : ∀ i : cover.I₀, Nonempty
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (cover.f i)).obj
      (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
        (ULift.ext _ _ hA)) ≅
      (constantSheaf (cover.X i).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
          (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))
  strata : Etale.etalePullbackLineAssertions (ULift.{u + 1} A)
    (ProjectiveLine T ↘ T) complex etale.obj represents
    (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
      (ULift.ext _ _ hA)) 2 a b cover
  pro_flat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
    (J := Scheme.ProEt.topology (ProjectiveLine T))
    (R := Scheme.proEtaleConstantRing (ProjectiveLine T) A)
    ((comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)).X i)
  pro_support : ∀ i : ℤ, (i < a - 2 ∨ b - 2 < i) → IsZero
    ((comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)).X i)
  pro_kflat : CochainComplex.IsKFlatIndependentCoefficients
    (R := Scheme.proEtaleConstantRing (ProjectiveLine T) A)
    (comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex))
  pro_represents : DerivedCategory.Q.obj
    (comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)) ≅ G

```

## New

The identical declaration block is now in `Sheaf.Paper.TowerP1CtfData`:

```lean
/-- The proper tower image, in the original coefficient-tower coordinates.
Source: standing-setting restriction, proper q
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def push {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}
    (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S)) :=
  (spTowerShriekRealization l E c.base (ProjectiveLine S) DP).functor ⋙
    SpTowerShriek.push l E c.base c.projective.geometry ⋙
      (spTowerShriekRealization l E c.base S DS).inverse

/-- Exact tower inverse image, derived tensor with the recorded Tate line, and shift two.
Source: standing-setting restriction, q^*(-)(1)[2]
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def pullTwist {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}
    (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S)) :=
  (spTowerShriekRealization l E c.base S DS).functor ⋙
    SpTowerShriek.pull l E c.base c.projective.geometry ⋙
      Prod.sectL (SpTowerShriek.D l E (ProjectiveLine S))
        ((SpTowerClasses.line l E c.chernP)⟦(2 : ℤ)⟧) ⋙
      SpTowerShriek.tensor l E c.base (ProjectiveLine S) ⋙
        (spTowerShriekRealization l E c.base (ProjectiveLine S) DP).inverse

/-- The prescribed cohomological and Tor intervals, using intrinsic constructibility
with finite locally closed constructible stratifications, at every positive level.
Source: the more precise bounds (blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def bounds (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (K : spDerivedCoefficientTowers l E T D) (r s a b : ℤ) : Prop :=
  ∀ n : ℕ,
    DerivedCategory.IsGE ((spDerivedCoefficientEvaluation l E T D n).obj K) r ∧
    DerivedCategory.IsLE ((spDerivedCoefficientEvaluation l E T D n).obj K) s ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T (SpTowerShriek.R l E n)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj K))) ∧
    Scheme.HasProEtaleTorAmplitude T (SpTowerShriek.R l E n)
      ((spDerivedCoefficientEvaluation l E T D n).obj K) a b

/-- The literal termwise comparison pullback of the specified etale complex,
followed by the canonical associated-module-sheaf realization.
Source: the local pro-etale K-flat model
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def comparisonModel (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (C : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) :=
  ((finiteCoefficientIntrinsicRealization T A).mapHomologicalComplex (.up ℤ)).obj
    (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
      |>.mapHomologicalComplex (.up ℤ)).obj C)

/-- The actual etale inverse-image, root-line tensor and shift-two complex.
Source: the prescribed local model (blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def lineModel (A : Type u) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u})
    (C : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) :=
  Etale.etalePullbackLineModel (ULift.{u + 1} A) (ProjectiveLine T ↘ T) C
    (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
      (ULift.ext _ _ hA)) 2

/-- Retained etale and flat representatives, their specified pullback-line model, and
its actual pro-etale realization. The stratum clause is the existing pulled-back
stratification assertion, including finite local module values and common covers.
Source: the affine-local and global representative clauses; Stacks 03TT, 0963, 06YQ
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
structure LocalModel (A : Type u) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (K : Scheme.proEtaleDerivedCategory T A)
    (G : Scheme.proEtaleDerivedCategory (ProjectiveLine T) A) (r s a b : ℤ) where
  etale : DerivedCategory.Plus
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  etale_constructible : Etale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) T etale.obj
  etale_lower : DerivedCategory.IsGE etale.obj r
  etale_upper : DerivedCategory.IsLE etale.obj s
  etale_tor : Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T a b etale.obj
  origin : (finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
      |>.mapDerivedCategory.obj etale.obj) ≅ K
  complex : CochainComplex
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ
  represents : DerivedCategory.Q.obj complex ≅ etale.obj
  flat : Etale.IsBoundedFlatComplex (ULift.{u + 1} A) a b complex
  terms_constructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (complex.X i)
  cover : Scheme.Cover.{u} Scheme.etalePrecoverage (ProjectiveLine T)
  line_trivial : ∀ i : cover.I₀, Nonempty
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (cover.f i)).obj
      (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
        (ULift.ext _ _ hA)) ≅
      (constantSheaf (cover.X i).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
          (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))
  strata : Etale.etalePullbackLineAssertions (ULift.{u + 1} A)
    (ProjectiveLine T ↘ T) complex etale.obj represents
    (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
      (ULift.ext _ _ hA)) 2 a b cover
  pro_flat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
    (J := Scheme.ProEt.topology (ProjectiveLine T))
    (R := Scheme.proEtaleConstantRing (ProjectiveLine T) A)
    ((comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)).X i)
  pro_support : ∀ i : ℤ, (i < a - 2 ∨ b - 2 < i) → IsZero
    ((comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)).X i)
  pro_kflat : CochainComplex.IsKFlatIndependentCoefficients
    (R := Scheme.proEtaleConstantRing (ProjectiveLine T) A)
    (comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex))
  pro_represents : DerivedCategory.Q.obj
    (comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)) ≅ G

```

The original module publicly imports that data module, so all six declarations and
their original public imports remain available to every importer. Its theorem retains
exactly its original signature and now imports the three proof-step modules privately.
The data node `def-sp-tower-p1-ctf-data` owns the six moved declarations; the original
node's Lean record now lists only its theorem.

## Users

`tools/downstream.py Sheaf.Paper.TowerP1UniformCtfDomains --uses push pullTwist bounds
comparisonModel lineModel LocalModel towerP1_uniform_ctf_domains` found zero downstream
modules, and only the assigned module mentions these names in that closure. This does
not authorize withdrawing the item: its unfinished DAG parents still need it, so it is
preserved and proved from the smaller steps.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TowerP1UniformCtfDomains | A5 | Same theorem signature; same public data re-exported. |
| Sheaf.Paper.TowerP1CtfData | new in A5 delivery | Owns the unchanged six data declarations. |
| Sheaf.Paper.TowerUniformEtaleDomains | new in A5 delivery | Imports data; states the domain step. |
| Sheaf.Paper.TowerP1ProperCtf | new in A5 delivery | Imports data; states proper-image preservation. |
| Sheaf.Paper.TowerP1LevelCtfModel | new in A5 delivery | Imports data; states a single-level model step. |

The original target meanings do not change: all existing definitions retain their exact
bodies and all existing theorem signatures remain identical. No consumer adaptation
or second mathematical target review is needed for the relocation.

## Status

landed 20261025T161756-L-102813 2026-10-25 (merge of deliver/A5/Sheaf.Paper.TowerP1UniformCtfDomains)
