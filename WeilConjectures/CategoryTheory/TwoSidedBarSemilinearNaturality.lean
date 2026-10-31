/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DoubleComplexTotal

/-!
# Semilinear naturality of the two-sided bar

Source: Stacks Project, Cohomology on Sites, Tags 08PH and 08PD; the explicit two-sided
semilinear refinement is agent-written
(blueprint: lem-trf-two-sided-bar-semilinear-naturality).

The raw coproducts and every generator map below are concrete. `Model` describes their
realization as complexes, with coordinates fixing every differential and both augmentations.
`System` asks for simultaneous realizations and maps with the specified generator formulas.
Its existence is the theorem, not a definition of data by choice from an existence proof.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite Simplicial

namespace CategoryTheory.TwoSidedBar

variable {D : Type u} [SmallCategory D] {R : Type u} [CommRing R]

/-- Delete a vertex of a string. Source: Stacks 08PH, first-vertex convention
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def delete {p : ℕ} (c : ComposableArrows D (p + 1)) (i : Fin (p + 2)) :
    ComposableArrows D p :=
  (SimplexCategory.toCat.map (SimplexCategory.δ i)).toFunctor ⋙ c

/-- The coefficient arrow of a deleted vertex. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def firstArrow {p : ℕ} (c : ComposableArrows D (p + 1)) (i : Fin (p + 2)) :
    c.left ⟶ (delete c i).left :=
  c.map (homOfLE (Fin.zero_le _))

/-- The arrow joining the new endpoint to the old endpoint. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def lastArrow {p : ℕ} (c : ComposableArrows D (p + 1)) (i : Fin (p + 2)) :
    (delete c i).right ⟶ c.right :=
  c.map (homOfLE (Fin.le_last _))

/-- Strings with an arrow into a simplicial term. Source: Stacks 08PH, two-sided refinement
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def Index (Q : SimplicialObject D) (p q : ℕ) :=
  Σ c : ComposableArrows D p, c.right ⟶ Q.obj (op ⦋q⦌)

/-- The concrete coproduct term of the two-sided bar. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def term (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) (p q : ℕ) : ModuleCat.{u} R :=
  ∐ (fun a : Index Q p q ↦ F.obj a.1.left)

/-- The concrete one-sided bar term. Source: Stacks 08PH, first-vertex convention
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def barTerm (F : D ⥤ ModuleCat.{u} R) (p : ℕ) : ModuleCat.{u} R :=
  ∐ (fun c : ComposableArrows D p ↦ F.obj c.left)

/-- A horizontal face, including coefficient transport at the first vertex and composition
at the last vertex. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def horizontalFace (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D)
    (p q : ℕ) (i : Fin (p + 2)) : term F Q (p + 1) q ⟶ term F Q p q :=
  Sigma.desc (fun a ↦ F.map (firstArrow a.1 i) ≫
    Sigma.ι (fun b : Index Q p q ↦ F.obj b.1.left)
      ⟨delete a.1 i, lastArrow a.1 i ≫ a.2⟩)

/-- Every vertical simplicial operator is postcomposition. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def verticalOperator (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D)
    (p : ℕ) {q r : ℕ} (α : op ⦋q⦌ ⟶ op ⦋r⦌) : term F Q p q ⟶ term F Q p r :=
  Sigma.desc (fun a ↦ Sigma.ι (fun b : Index Q p r ↦ F.obj b.1.left)
    ⟨a.1, a.2 ≫ Q.map α⟩)

/-- The unsigned horizontal alternating differential. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def horizontalD (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) (p q : ℕ) :
    term F Q (p + 1) q ⟶ term F Q p q :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • horizontalFace F Q p q i

/-- The unsigned vertical alternating differential. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def verticalD (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) (p q : ℕ) :
    term F Q p (q + 1) ⟶ term F Q p q :=
  ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
    verticalOperator F Q p (SimplexCategory.δ i).op

/-- The ordinary bar differential. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def barD (F : D ⥤ ModuleCat.{u} R) (p : ℕ) : barTerm F (p + 1) ⟶ barTerm F p :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val •
    Sigma.desc (fun c ↦ F.map (firstArrow c i) ≫
      Sigma.ι (fun b : ComposableArrows D p ↦ F.obj b.left) (delete c i))

/-- The evaluation edge on actual coproducts. Source: Stacks 08PH, two-sided refinement
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def evaluate (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) (q : ℕ) :
    term F Q 0 q ⟶ F.obj (Q.obj (op ⦋q⦌)) :=
  Sigma.desc (fun a ↦ F.map a.2)

/-- The forgetful edge on actual coproducts. Source: Stacks 08PH, two-sided refinement
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def forgetLast (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) (p : ℕ) :
    term F Q p 0 ⟶ barTerm F p :=
  Sigma.desc (fun a ↦ Sigma.ι (fun c : ComposableArrows D p ↦ F.obj c.left) a.1)

/-- Mathlib's alternating evaluation complex extended into nonpositive cochain degrees.
Source: Stacks 08PH (blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
abbrev evaluationComplex (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) :=
  ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} R)).obj (Q ⋙ F)).extend
    ComplexShape.embeddingDownNat

/-- The standard extension coordinates of the evaluation complex. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def evaluationCoordinates (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) (q : ℕ) :
    (evaluationComplex F Q).X (-↑q) ≅ F.obj (Q.obj (op ⦋q⦌)) :=
  ((AlgebraicTopology.alternatingFaceMapComplex _).obj (Q ⋙ F)).extendXIso
    ComplexShape.embeddingDownNat (i := q) rfl

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Realizations of the displayed bar formulas, with all coordinate maps and differential
normalizations. No quasi-isomorphism is required of either edge. Source: Stacks 08PH,
agent-written two-sided refinement (blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
structure Model (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) where
  double : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℤ) (.up ℤ)
  coordinates : ∀ p q : ℕ, (double.X (-↑p)).X (-↑q) ≅ term F Q p q
  positive : ∀ i j : ℤ, 0 < i ∨ 0 < j → IsZero ((double.X i).X j)
  horizontal : ∀ p q : ℕ,
    (coordinates (p + 1) q).inv ≫ (double.d (-↑(p + 1)) (-↑p)).f (-↑q) ≫
      (coordinates p q).hom = horizontalD F Q p q
  vertical : ∀ p q : ℕ,
    (coordinates p (q + 1)).inv ≫ (double.X (-↑p)).d (-↑(q + 1)) (-↑q) ≫
      (coordinates p q).hom = verticalD F Q p q
  bar : CochainComplex (ModuleCat.{u} R) ℤ
  barCoordinates : ∀ p : ℕ, bar.X (-↑p) ≅ barTerm F p
  barPositive : ∀ i : ℤ, 0 < i → IsZero (bar.X i)
  barDifferential : ∀ p : ℕ,
    (barCoordinates (p + 1)).inv ≫ bar.d (-↑(p + 1)) (-↑p) ≫
      (barCoordinates p).hom = barD F p
  toEvaluation : double.total (.up ℤ) ⟶ evaluationComplex F Q
  toBar : double.total (.up ℤ) ⟶ bar
  evaluationEdge : ∀ q : ℕ,
    (coordinates 0 q).inv ≫ double.ιTotal (.up ℤ) 0 (-↑q) (-↑q) (by simp) ≫
      toEvaluation.f (-↑q) ≫ (evaluationCoordinates F Q q).hom = evaluate F Q q
  evaluationOffEdge : ∀ (p q : ℕ) (n : ℤ), p ≠ 0 →
    (coordinates p q).inv ≫ double.ιTotalOrZero (.up ℤ) (-↑p) (-↑q) n ≫
      toEvaluation.f n = 0
  barEdge : ∀ p : ℕ,
    (coordinates p 0).inv ≫ double.ιTotal (.up ℤ) (-↑p) 0 (-↑p) (by simp) ≫
      toBar.f (-↑p) ≫ (barCoordinates p).hom = forgetLast F Q p
  barOffEdge : ∀ (p q : ℕ) (n : ℤ), q ≠ 0 →
    (coordinates p q).inv ≫ double.ιTotalOrZero (.up ℤ) (-↑p) (-↑q) n ≫ toBar.f n = 0

/-- Coproduct-to-total coordinates, zero away from their diagonal. The Mathlib total
uses horizontal plus `(-1)^p` times vertical differential in bidegree `(-p,-q)`.
Source: Stacks 08PH (blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def totalGenerator {F : D ⥤ ModuleCat.{u} R} {Q : SimplicialObject D}
    (M : Model F Q) (p q : ℕ) (n : ℤ) :
    term F Q p q ⟶ (M.double.total (.up ℤ)).X n :=
  (M.coordinates p q).inv ≫ M.double.ιTotalOrZero (.up ℤ) (-↑p) (-↑q) n


variable {D' : Type u} [SmallCategory D'] {R' : Type u} [CommRing R']

/-- Reindex strings, transport coefficients, and postcompose the endpoint. This formula
uses no contracting homotopy. Source: Stacks 08PH, semilinear two-sided refinement
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def reindex (u : D ⥤ D') (ρ : R →+* R')
    {F : D ⥤ ModuleCat.{u} R} {F' : D' ⥤ ModuleCat.{u} R'}
    (θ : F ⟶ u ⋙ F' ⋙ ModuleCat.restrictScalars ρ)
    {Q : SimplicialObject D} {Q' : SimplicialObject D'} (k : Q ⋙ u ⟶ Q') (p q : ℕ) :
    term F Q p q ⟶ (ModuleCat.restrictScalars ρ).obj (term F' Q' p q) :=
  Sigma.desc (fun a ↦ θ.app a.1.left ≫ (ModuleCat.restrictScalars ρ).map
    (Sigma.ι (fun b : Index Q' p q ↦ F'.obj b.1.left)
      ⟨a.1 ⋙ u, u.map a.2 ≫ k.app (op ⦋q⦌)⟩))

/-- The ordinary bar generator map. Source: Stacks 08PH
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def barReindex (u : D ⥤ D') (ρ : R →+* R')
    {F : D ⥤ ModuleCat.{u} R} {F' : D' ⥤ ModuleCat.{u} R'}
    (θ : F ⟶ u ⋙ F' ⋙ ModuleCat.restrictScalars ρ) (p : ℕ) :
    barTerm F p ⟶ (ModuleCat.restrictScalars ρ).obj (barTerm F' p) :=
  Sigma.desc (fun c ↦ θ.app c.left ≫ (ModuleCat.restrictScalars ρ).map
    (Sigma.ι (fun b : ComposableArrows D' p ↦ F'.obj b.left) (c ⋙ u)))

/-- Degreewise restriction of scalars, using Mathlib's functor. Source: Stacks 08PD
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
abbrev restriction (ρ : R →+* R') :=
  (ModuleCat.restrictScalars.{u} ρ).mapHomologicalComplex (.up ℤ)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A double-complex morphism, its induced total map, and its two edge maps, pinned on
all coproducts. The strict squares are part of the asserted laws. Source: Stacks 08PH
and 08PD, agent-written two-sided refinement
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
structure SemilinearMap (u : D ⥤ D') (ρ : R →+* R')
    {F : D ⥤ ModuleCat.{u} R} {F' : D' ⥤ ModuleCat.{u} R'}
    (θ : F ⟶ u ⋙ F' ⋙ ModuleCat.restrictScalars ρ)
    {Q : SimplicialObject D} {Q' : SimplicialObject D'} (k : Q ⋙ u ⟶ Q')
    (M : Model F Q) (M' : Model F' Q') where
  double : M.double ⟶ ((restriction ρ).mapHomologicalComplex (.up ℤ)).obj M'.double
  total : M.double.total (.up ℤ) ⟶ (restriction ρ).obj (M'.double.total (.up ℤ))
  evaluation : evaluationComplex F Q ⟶ (restriction ρ).obj (evaluationComplex F' Q')
  bar : M.bar ⟶ (restriction ρ).obj M'.bar
  doubleFormula : ∀ p q : ℕ,
    (M.coordinates p q).inv ≫ (double.f (-↑p)).f (-↑q) ≫
      (ModuleCat.restrictScalars ρ).map (M'.coordinates p q).hom = reindex u ρ θ k p q
  totalFormula : ∀ (p q : ℕ) (n : ℤ),
    totalGenerator M p q n ≫ total.f n = reindex u ρ θ k p q ≫
      (ModuleCat.restrictScalars ρ).map (totalGenerator M' p q n)
  evaluationFormula : ∀ q : ℕ,
    (evaluationCoordinates F Q q).inv ≫ evaluation.f (-↑q) ≫
      (ModuleCat.restrictScalars ρ).map (evaluationCoordinates F' Q' q).hom =
        θ.app (Q.obj (op ⦋q⦌)) ≫ (ModuleCat.restrictScalars ρ).map (F'.map (k.app (op ⦋q⦌)))
  barFormula : ∀ p : ℕ,
    (M.barCoordinates p).inv ≫ bar.f (-↑p) ≫
      (ModuleCat.restrictScalars ρ).map (M'.barCoordinates p).hom = barReindex u ρ θ p
  evaluationSquare : total ≫ (restriction ρ).map M'.toEvaluation = M.toEvaluation ≫ evaluation
  barSquare : total ≫ (restriction ρ).map M'.toBar = M.toBar ≫ bar
/-- Identity coefficients with the canonical scalar-restriction identification.
Source: Stacks 08PH (blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def identityCoefficient (F : D ⥤ ModuleCat.{u} R) :
    F ⟶ (𝟭 D) ⋙ F ⋙ ModuleCat.restrictScalars (RingHom.id R) :=
  whiskerLeft F (ModuleCat.restrictScalarsId R).inv

/-- The composite coefficient map, including the usual iterated-restriction identification.
Source: Stacks 08PH (blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
def compositeCoefficient {D'' : Type u} [SmallCategory D'']
    {R'' : Type u} [CommRing R''] (u : D ⥤ D') (v : D' ⥤ D'')
    (ρ : R →+* R') (σ : R' →+* R'')
    {F : D ⥤ ModuleCat.{u} R} {F' : D' ⥤ ModuleCat.{u} R'}
    {F'' : D'' ⥤ ModuleCat.{u} R''}
    (θ : F ⟶ u ⋙ F' ⋙ ModuleCat.restrictScalars ρ)
    (ψ : F' ⟶ v ⋙ F'' ⋙ ModuleCat.restrictScalars σ) :
    F ⟶ (u ⋙ v) ⋙ F'' ⋙ ModuleCat.restrictScalars (σ.comp ρ) :=
  θ ≫ whiskerLeft u (whiskerRight ψ (ModuleCat.restrictScalars ρ)) ≫
    whiskerLeft ((u ⋙ v) ⋙ F'') (ModuleCat.restrictScalarsComp ρ σ).inv

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Simultaneous bar realizations and semilinear maps, including identity, composition,
and scalar-restriction identifications. Equalities on underlying elements express exactly
the standard identity-on-groups restriction isomorphisms. No contractibility hypotheses
occur. Source: Stacks 08PH and 08PD, agent-written two-sided refinement
(blueprint: lem-trf-two-sided-bar-semilinear-naturality). -/
structure System where
  models : ∀ {D : Type u} [SmallCategory D] {R : Type u} [CommRing R]
    (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D), Model F Q
  maps : ∀ {D D' : Type u} [SmallCategory D] [SmallCategory D']
    {R R' : Type u} [CommRing R] [CommRing R'] (u : D ⥤ D') (ρ : R →+* R')
    {F : D ⥤ ModuleCat.{u} R} {F' : D' ⥤ ModuleCat.{u} R'}
    (θ : F ⟶ u ⋙ F' ⋙ ModuleCat.restrictScalars ρ)
    {Q : SimplicialObject D} {Q' : SimplicialObject D'} (k : Q ⋙ u ⟶ Q'),
    SemilinearMap u ρ θ k (models F Q) (models F' Q')
  identity : ∀ {D : Type u} [SmallCategory D] {R : Type u} [CommRing R]
    (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D),
    (∀ (i j : ℤ) (x : ((models F Q).double.X i).X j),
      (((maps (𝟭 D) (RingHom.id R) (identityCoefficient F)
        (Functor.rightUnitor Q).hom).double.f i).f j) x = x) ∧
    (∀ (n : ℤ) (x : ((models F Q).double.total (.up ℤ)).X n),
      ((maps (𝟭 D) (RingHom.id R) (identityCoefficient F)
        (Functor.rightUnitor Q).hom).total.f n) x = x) ∧
    (∀ (n : ℤ) (x : (evaluationComplex F Q).X n),
      ((maps (𝟭 D) (RingHom.id R) (identityCoefficient F)
        (Functor.rightUnitor Q).hom).evaluation.f n) x = x) ∧
    (∀ (n : ℤ) (x : (models F Q).bar.X n),
      ((maps (𝟭 D) (RingHom.id R) (identityCoefficient F)
        (Functor.rightUnitor Q).hom).bar.f n) x = x)
  composition : ∀ {D D' D'' : Type u}
    [SmallCategory D] [SmallCategory D'] [SmallCategory D'']
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (u : D ⥤ D') (v : D' ⥤ D'') (ρ : R →+* R') (σ : R' →+* R'')
    {F : D ⥤ ModuleCat.{u} R} {F' : D' ⥤ ModuleCat.{u} R'}
    {F'' : D'' ⥤ ModuleCat.{u} R''}
    (θ : F ⟶ u ⋙ F' ⋙ ModuleCat.restrictScalars ρ)
    (ψ : F' ⟶ v ⋙ F'' ⋙ ModuleCat.restrictScalars σ)
    {Q : SimplicialObject D} {Q' : SimplicialObject D'} {Q'' : SimplicialObject D''}
    (k : Q ⋙ u ⟶ Q') (l : Q' ⋙ v ⟶ Q''),
    (∀ (i j : ℤ) (x : ((models F Q).double.X i).X j),
      (((maps (u ⋙ v) (σ.comp ρ) (compositeCoefficient u v ρ σ θ ψ)
        (whiskerRight k v ≫ l)).double.f i).f j) x =
      (((maps v σ ψ l).double.f i).f j) ((((maps u ρ θ k).double.f i).f j) x)) ∧
    (∀ (n : ℤ) (x : ((models F Q).double.total (.up ℤ)).X n),
      ((maps (u ⋙ v) (σ.comp ρ) (compositeCoefficient u v ρ σ θ ψ)
        (whiskerRight k v ≫ l)).total.f n) x =
      ((maps v σ ψ l).total.f n) (((maps u ρ θ k).total.f n) x)) ∧
    (∀ (n : ℤ) (x : (evaluationComplex F Q).X n),
      ((maps (u ⋙ v) (σ.comp ρ) (compositeCoefficient u v ρ σ θ ψ)
        (whiskerRight k v ≫ l)).evaluation.f n) x =
      ((maps v σ ψ l).evaluation.f n) (((maps u ρ θ k).evaluation.f n) x)) ∧
    (∀ (n : ℤ) (x : (models F Q).bar.X n),
      ((maps (u ⋙ v) (σ.comp ρ) (compositeCoefficient u v ρ σ θ ψ)
        (whiskerRight k v ≫ l)).bar.f n) x =
      ((maps v σ ψ l).bar.f n) (((maps u ρ θ k).bar.f n) x))
  scalarRestriction : ∀ {D : Type u} [SmallCategory D]
    {R R' : Type u} [CommRing R] [CommRing R'] (ρ : R →+* R')
    (F' : D ⥤ ModuleCat.{u} R') (Q : SimplicialObject D),
    IsIso (maps (𝟭 D) ρ (F := F' ⋙ ModuleCat.restrictScalars ρ) (𝟙 _)
      (Functor.rightUnitor Q).hom).double ∧
    IsIso (maps (𝟭 D) ρ (F := F' ⋙ ModuleCat.restrictScalars ρ) (𝟙 _)
      (Functor.rightUnitor Q).hom).total ∧
    IsIso (maps (𝟭 D) ρ (F := F' ⋙ ModuleCat.restrictScalars ρ) (𝟙 _)
      (Functor.rightUnitor Q).hom).evaluation ∧
    IsIso (maps (𝟭 D) ρ (F := F' ⋙ ModuleCat.restrictScalars ρ) (𝟙 _)
      (Functor.rightUnitor Q).hom).bar

/-- Semilinear functoriality of the two-sided bar and both augmentation squares, with no
representable-contractibility condition. Source: Stacks 08PH and 08PD, agent-written
strict two-sided refinement (blueprint: lem-trf-two-sided-bar-semilinear-naturality).

Proof: Restriction preserves finite-support tuples and the subsets defining kernels and
images, hence is exact and preserves coproducts. Horizontal faces satisfy the simplicial
identities by functoriality and associativity; vertical faces do so by simpliciality of Q.
They commute because deletion commutes with postcomposition. Oppositely signed pairs
cancel in each alternating square. In cochain bidegree (-p,-q), the mixed total terms have
signs (-1)^(p-1) and (-1)^p, hence cancel. Each nonpositive total diagonal is finite.
Reindexing preserves horizontal faces by naturality of theta, and all vertical operators
by Q'(alpha) k_q = k_r u(Q(alpha)). The coefficient formulas therefore give double and
chain maps. Evaluation commutes with the vertical differential; the two horizontal
faces entering its edge cancel by F(f)F(a)=F(fa). Forgetting the endpoint commutes with
horizontal faces; the two vertical faces entering its edge become identical and cancel.
On the evaluation edge the square is F'(k_q u(f)) theta_T = F'(k_q) theta_Q F(f);
on the forgetful edge both routes retain the same string and theta_T(x). Off the edges
both routes vanish. Composing reindexings gives vu on strings and psi theta on coefficients;
naturality of psi at k proves the evaluation composition law. Identity data fix all
coefficients. Scalar restriction identifications are identities on these coproducts,
and applying localization preserves both equalities. These checks give all fields of
System simultaneously; no homotopies are chosen or needed. -/
theorem system_exists : Nonempty (System.{u}) := by
  sorry


/-- Reindexing commutes with individual horizontal faces and all vertical operators,
including degeneracies. Source: Stacks 08PH, agent-written two-sided refinement
(blueprint: lem-trf-two-sided-bar-semilinear-naturality).

Proof: On each coproduct injection the first horizontal face is naturality of theta;
internal faces use u(ba)=u(b)u(a), and the last face uses associativity with k_q u(f).
For a vertical operator alpha the last arrow is the same on both routes because
Q'(alpha) k_q = k_r u(Q(alpha)). The coefficient is theta_T(x) on both routes.
Equality on coproduct injections gives the two displayed identities. -/
theorem operator_naturality (u : D ⥤ D') (ρ : R →+* R')
    {F : D ⥤ ModuleCat.{u} R} {F' : D' ⥤ ModuleCat.{u} R'}
    (θ : F ⟶ u ⋙ F' ⋙ ModuleCat.restrictScalars ρ)
    {Q : SimplicialObject D} {Q' : SimplicialObject D'} (k : Q ⋙ u ⟶ Q') :
    (∀ (p q : ℕ) (i : Fin (p + 2)),
      horizontalFace F Q p q i ≫ reindex u ρ θ k p q =
        reindex u ρ θ k (p + 1) q ≫
          (ModuleCat.restrictScalars ρ).map (horizontalFace F' Q' p q i)) ∧
    (∀ (p q r : ℕ) (α : op ⦋q⦌ ⟶ op ⦋r⦌),
      verticalOperator F Q p α ≫ reindex u ρ θ k p r =
        reindex u ρ θ k p q ≫
          (ModuleCat.restrictScalars ρ).map (verticalOperator F' Q' p α)) := by
  sorry

/-- Restriction preserves direct sums and finite limits and colimits, hence kernels and
images. Source: Stacks 08PH, agent-written scalar-restriction verification
(blueprint: lem-trf-two-sided-bar-semilinear-naturality).

Proof: A coproduct is the module of finite-support tuples. Restriction changes only scalar
action, so the identity on tuples identifies the two coproducts. Kernels and images are
the same subsets with the restricted action; cokernels are the same quotient groups.
Finite products are coordinatewise. Thus products and kernels, and finite coproducts and
cokernels, are preserved, giving the claimed exactness. This includes the empty sum. -/
theorem restriction_exact (ρ : R →+* R') :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} ρ) ∧
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} ρ) ∧
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (ModuleCat.restrictScalars.{u} ρ) := by
  sorry

/-- Exact restriction preserves quasi-isomorphisms. Source: Stacks 08PD; derived passage
uses the exact-functor localization, Stacks 015F
(blueprint: lem-trf-two-sided-bar-semilinear-naturality).

Proof: Kernel and image subsets are unchanged by restriction, so cohomology is the same
quotient group with the restricted action. An isomorphism on this group remains an
isomorphism of restricted modules. Apply this to every degree of f. -/
theorem restriction_quasiIso (ρ : R →+* R')
    {K L : CochainComplex (ModuleCat.{u} R') ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((restriction ρ).map f) := by
  sorry

/-- Exact derived restriction takes inverses of localized quasi-isomorphisms to their
inverses, under the standard localization comparison. Source: Stacks 08PD and 015F
(blueprint: lem-trf-two-sided-bar-semilinear-naturality).

Proof: Apply the exact-functor-derived-factorization lemma to restriction, which preserves
finite limits and colimits. It represents the derived functor degreewise without any
resolution. Apply this functor to the two inverse identities for Q(f). Functoriality
shows that the image of its inverse is the inverse of its image. -/
theorem restriction_inverse (ρ : R →+* R')
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R')]
    {K L : CochainComplex (ModuleCat.{u} R') ℤ} (f : K ⟶ L) [QuasiIso f] :
    (ModuleCat.restrictScalars ρ).mapDerivedCategory.map (inv (DerivedCategory.Q.map f)) =
      inv ((ModuleCat.restrictScalars ρ).mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
  sorry

/-- Both strict squares give the same squares after localization and the canonical
identification of derived restriction with degreewise restriction. Source: Stacks 08PD
and 08PH, agent-written two-sided refinement
(blueprint: lem-trf-two-sided-bar-semilinear-naturality).

Proof: Apply the localization functor to each equality of composites. For the alternative
route through the derived restriction functor, naturality of mapDerivedCategoryFactors
at each augmentation identifies its localized degreewise restriction with that route.
The identifications retain the same finite-support tuples and signed differentials.
Neither edge map is asserted to be a quasi-isomorphism for general Q. -/
theorem localized_squares (u : D ⥤ D') (ρ : R →+* R')
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R')]
    {F : D ⥤ ModuleCat.{u} R} {F' : D' ⥤ ModuleCat.{u} R'}
    (θ : F ⟶ u ⋙ F' ⋙ ModuleCat.restrictScalars ρ)
    {Q : SimplicialObject D} {Q' : SimplicialObject D'} (k : Q ⋙ u ⟶ Q')
    {M : Model F Q} {M' : Model F' Q'} (a : SemilinearMap u ρ θ k M M') :
    (DerivedCategory.Q.map a.total ≫
        (ModuleCat.restrictScalars ρ).mapDerivedCategoryFactors.inv.app
          (M'.double.total (.up ℤ)) ≫
        (ModuleCat.restrictScalars ρ).mapDerivedCategory.map
          (DerivedCategory.Q.map M'.toEvaluation) =
      DerivedCategory.Q.map M.toEvaluation ≫ DerivedCategory.Q.map a.evaluation ≫
        (ModuleCat.restrictScalars ρ).mapDerivedCategoryFactors.inv.app
          (evaluationComplex F' Q')) ∧
    (DerivedCategory.Q.map a.total ≫
        (ModuleCat.restrictScalars ρ).mapDerivedCategoryFactors.inv.app
          (M'.double.total (.up ℤ)) ≫
        (ModuleCat.restrictScalars ρ).mapDerivedCategory.map
          (DerivedCategory.Q.map M'.toBar) =
      DerivedCategory.Q.map M.toBar ≫ DerivedCategory.Q.map a.bar ≫
        (ModuleCat.restrictScalars ρ).mapDerivedCategoryFactors.inv.app M'.bar) := by
  sorry

end CategoryTheory.TwoSidedBar
