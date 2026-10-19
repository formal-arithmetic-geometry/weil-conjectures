/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek
import Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# The category bar model for derived colimits

Source: Stacks Project, Cohomology on Sites, Tags 08PF, 08PG, 08PH, 08PD and 07AC
(blueprint: lem-trf-derived-colimit-bar).

The auxiliary records spell out the existence assertion, including its canonical comparison
and its formulas. No object is selected from the existence theorem below. In a chain
`c : ComposableArrows E n`, the vertices run from `U_n` to `U_0`, so the coefficient is at
`c.right`. In particular the last face, rather than the first, restricts the coefficient.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Standard localization universe for coefficient modules. Source: Stacks 08PF and the
size convention (blueprint: lem-trf-derived-colimit-bar). -/
noncomputable instance categoryBarModuleDerived (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

/-- Standard localization universe for module presheaves. Source: Stacks 08PF and the
size convention (blueprint: lem-trf-derived-colimit-bar). -/
noncomputable instance categoryBarPresheafDerived (E : Type u) [SmallCategory E]
    (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (Eᵒᵖ ⥤ ModuleCat.{u} R) := HasDerivedCategory.standard _

/-- Delete vertex `j`, composing the arrows on either side. Source: Stacks 08PG
(blueprint: lem-trf-derived-colimit-bar). -/
def categoryBarDelete {E : Type u} [SmallCategory E] {n : ℕ}
    (c : ComposableArrows E (n + 1)) (j : Fin (n + 2)) : ComposableArrows E n :=
  (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ c

/-- The coefficient map for a face. It is the identity unless the last vertex is deleted;
then it is restriction along the last arrow. Source: Stacks 08PG
(blueprint: lem-trf-derived-colimit-bar). -/
def categoryBarFaceCoefficient {E : Type u} [SmallCategory E]
    {R : Type u} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{u} R) {n : ℕ}
    (c : ComposableArrows E (n + 1)) (j : Fin (n + 2)) :
    F.obj (op c.right) ⟶ F.obj (op (categoryBarDelete c j).right) :=
  F.map (c.map (homOfLE (Fin.le_last _))).op

/-- The constant ring on the identity-cover site. Source: Stacks 08PF
(blueprint: lem-trf-derived-colimit-bar). -/
def categoryBarConstantRing (E : Type u) [SmallCategory E] (R : Type u) [CommRing R] :
    Sheaf (⊥ : GrothendieckTopology E) RingCat.{u} :=
  (sheafBotEquivalence _).inverse.obj ((Functor.const Eᵒᵖ).obj (RingCat.of R))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The point morphism and the identification of its coefficient modules with ordinary
module presheaves. The inverse-image isomorphism identifies its structural ring map with
the identity, and the evaluation isomorphisms respect restriction and linear maps.
Source: Stacks 08PF (blueprint: lem-trf-derived-colimit-bar). -/
structure CategoryColimitPoint (E : Type u) [SmallCategory E] (R : Type u) [CommRing R] where
  morphism : RingedToposMorphism (categoryBarConstantRing E R)
    (categoryBarConstantRing (Discrete PUnit.{u + 1}) R)
  inverse : morphism.inverse ≅
    (sheafBotEquivalence (Type u)).functor ⋙
      (evaluation (Discrete PUnit.{u + 1})ᵒᵖ (Type u)).obj (op ⟨PUnit.unit⟩) ⋙
      Functor.const Eᵒᵖ ⋙ (sheafBotEquivalence (Type u)).inverse
  ringMap : morphism.ringMap = inverse.hom.app
    ((sheafCompose (⊥ : GrothendieckTopology (Discrete PUnit.{u + 1}))
      (forget RingCat)).obj (categoryBarConstantRing (Discrete PUnit.{u + 1}) R))
  modules : ringedSiteModules.{u} (categoryBarConstantRing E R) ≌
    (Eᵒᵖ ⥤ ModuleCat.{u} R)
  evaluation : ∀ (U : Eᵒᵖ), modules.functor ⋙
    (CategoryTheory.evaluation Eᵒᵖ (ModuleCat.{u} R)).obj U ≅
      SheafOfModules.evaluation (categoryBarConstantRing E R) U
  restriction : ∀ (M : ringedSiteModules.{u} (categoryBarConstantRing E R))
    {U V : Eᵒᵖ} (a : U ⟶ V) (x : (modules.functor.obj M).obj U),
    (evaluation V).hom.app M ((modules.functor.obj M).map a x) =
      M.val.map a ((evaluation U).hom.app M x)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The bar-model part of the assertion: a functor with coproduct coordinates, its exact
alternating differential, and the canonical derived comparison computed on an augmented
acyclic resolution. Source: Stacks 08PG and 08PF
(blueprint: lem-trf-derived-colimit-bar).

The data are specified by universal properties and generator formulas, rather than a
chosen object from an unproved existence claim. `model_eq` fixes the derived model by the
resolution augmentation and the universal derived comparison; `colimitAugmentation` fixes the
identification of the colimit of the resolution with the bar complex in degree zero, where a
generator `(U_0, x)` goes to `ι_{U_0} x` in the colimit (Stacks 08PG: `π_! L_U(M) = M`). Without
it the model would be determined only up to a unit of `R`. -/
structure CategoryColimitBarModel (E : Type u) [SmallCategory E]
    (R : Type u) [CommRing R] where
  point : CategoryColimitPoint E R
  [colimitAdditive : (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).Additive]
  derived : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R)
  comparison : DerivedCategory.Q ⋙ derived ⟶
    (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q
  universal : derived.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ))
  pointwise : Functor.HasPointwiseLeftDerivedFunctor
    ((colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q)
    (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ))
  stacksPointwise : ∀ (X : HomotopyCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ)),
    IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget
        (HomotopyCategory.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ)) ⊤ X ⋙
        Over.forget X ⋙
        (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh) (derived.obj (DerivedCategory.Qh.obj X))
  [shift : derived.CommShift ℤ]
  triangulated : derived.IsTriangulated
  adjunction : derived ⊣ (Functor.const Eᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory
  transpose : ∀ (P : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (N : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : ((colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex
      (.up ℤ)).obj P ⟶ N),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
      (comparison.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((colimConstAdj.mapHomologicalComplex (.up ℤ)).homEquiv P N f) ≫
        (Functor.const Eᵒᵖ).mapDerivedCategoryFactors.inv.app N
  bar : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ CochainComplex (ModuleCat.{u} R) ℤ
  [additive : bar.Additive]
  coordinates : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ),
    (bar.obj F).X (-(n : ℤ)) ≅ ∐ (fun c : ComposableArrows E n ↦ F.obj (op c.right))
  positive : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (r : ℤ), 0 < r → IsZero ((bar.obj F).X r)
  differential : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (c : ComposableArrows E (n + 1)) (x : F.obj (op c.right)),
    ((bar.obj F).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))
      ((Sigma.ι (fun a : ComposableArrows E (n + 1) ↦ F.obj (op a.right)) c ≫
        (coordinates F (n + 1)).inv) x) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        ((Sigma.ι (fun a : ComposableArrows E n ↦ F.obj (op a.right))
          (categoryBarDelete c j) ≫ (coordinates F n).inv)
            (categoryBarFaceCoefficient F c j x))
  coefficientMap : ∀ {F G : Eᵒᵖ ⥤ ModuleCat.{u} R} (t : F ⟶ G) (n : ℕ)
    (c : ComposableArrows E n) (x : F.obj (op c.right)),
    ((bar.map t).f (-(n : ℤ)))
      ((Sigma.ι (fun a : ComposableArrows E n ↦ F.obj (op a.right)) c ≫
        (coordinates F n).inv) x) =
      (Sigma.ι (fun a : ComposableArrows E n ↦ G.obj (op a.right)) c ≫
        (coordinates G n).inv) (t.app (op c.right) x)
  exact : ∀ (S : ShortComplex (Eᵒᵖ ⥤ ModuleCat.{u} R)),
    (∀ U : Eᵒᵖ, (S.map ((evaluation Eᵒᵖ (ModuleCat.{u} R)).obj U)).ShortExact) →
      (S.map bar).ShortExact
  resolution : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ
  augmentation : resolution ⟶ (CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0)
  quasiIso : ∀ F, QuasiIso (augmentation.app F)
  acyclic : ∀ F, IsIso (comparison.app (resolution.obj F))
  colimitResolution : resolution ⋙
    (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex (.up ℤ) ≅ bar
  model : CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0 ⋙
    DerivedCategory.Q ⋙ derived ≅ bar ⋙ DerivedCategory.Q
  model_eq : ∀ F,
    model.hom.app F = inv (derived.map (DerivedCategory.Q.map (augmentation.app F))) ≫
      comparison.app (resolution.obj F) ≫ DerivedCategory.Q.map (colimitResolution.hom.app F)
  colimitAugmentation : ∀ F : Eᵒᵖ ⥤ ModuleCat.{u} R,
    (colimitResolution.hom.app F).f (-((0 : ℕ) : ℤ)) ≫ (coordinates F 0).hom ≫
        Sigma.desc (fun c : ComposableArrows E 0 ↦ colimit.ι F (op c.right)) =
      (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).map
        ((augmentation.app F).f (-((0 : ℕ) : ℤ)) ≫
          (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F
            (-((0 : ℕ) : ℤ)) (by simp)).hom)
  singleExact : ∀ (S : ShortComplex (Eᵒᵖ ⥤ ModuleCat.{u} R)),
    (∀ U : Eᵒᵖ, (S.map ((evaluation Eᵒᵖ (ModuleCat.{u} R)).obj U)).ShortExact) →
      (S.map (CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0)).ShortExact
  modelBoundary : ∀ (S : ShortComplex (Eᵒᵖ ⥤ ModuleCat.{u} R))
    (hS : ∀ U : Eᵒᵖ, (S.map ((evaluation Eᵒᵖ (ModuleCat.{u} R)).obj U)).ShortExact),
    derived.map (DerivedCategory.triangleOfSESδ (singleExact S hS)) ≫
      (derived.commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj S.X₁)) ≫
      (model.hom.app S.X₁)⟦(1 : ℤ)⟧' =
        model.hom.app S.X₃ ≫ DerivedCategory.triangleOfSESδ (exact S hS)

attribute [instance] CategoryColimitBarModel.shift CategoryColimitBarModel.additive

namespace CategoryColimitBarModel

/-- A bar generator in coproduct coordinates. Source: Stacks 08PG
(blueprint: lem-trf-derived-colimit-bar). -/
noncomputable def generator {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (B : CategoryColimitBarModel E R) (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (c : ComposableArrows E n) : F.obj (op c.right) ⟶ (B.bar.obj F).X (-(n : ℤ)) :=
  Sigma.ι (fun a : ComposableArrows E n ↦ F.obj (op a.right)) c ≫ (B.coordinates F n).inv

end CategoryColimitBarModel

/-- The ordinary reindexing comparison on colimits, degree by degree. Source: Stacks 08PH
(blueprint: lem-trf-derived-colimit-bar). -/
noncomputable def categoryBarColimitReindex {E D : Type u}
    [SmallCategory E] [SmallCategory D] {R : Type u} [CommRing R] (u : E ⥤ D) :
    ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapHomologicalComplex (.up ℤ) ⋙
      (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex (.up ℤ) ⟶
        (colim : (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex
    (F := ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op) ⋙ colim)
    (G := (colim : (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R))
    { app := fun F ↦ colimit.pre F u.op
      naturality := fun _ _ t ↦ (colimit.pre_map t u.op).symm } (.up ℤ)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Functorial bar models, with semilinear chain maps and augmented resolution lifts.
All maps are fixed by their generator formulas; `lift_aug` and `canonical` identify them
with the canonical derived maps, not merely maps between isomorphic homology groups.
Source: Stacks 08PG, 08PH, 08PD, with the natural-transformation prism extension
(blueprint: lem-trf-derived-colimit-bar). -/
structure CategoryColimitBarSystem where
  models : ∀ (E : Type u) [SmallCategory E] (R : Type u) [CommRing R],
    CategoryColimitBarModel E R
  map : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S]
    (u : E ⥤ D) (φ : R →+* S) {F : Eᵒᵖ ⥤ ModuleCat.{u} R}
    {G : Dᵒᵖ ⥤ ModuleCat.{u} S} (_t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ),
    (models E R).bar.obj F ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
        ((models D S).bar.obj G)
  formula : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S]
    (u : E ⥤ D) (φ : R →+* S) {F : Eᵒᵖ ⥤ ModuleCat.{u} R}
    {G : Dᵒᵖ ⥤ ModuleCat.{u} S} (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ)
    (n : ℕ) (c : ComposableArrows E n) (x : F.obj (op c.right)),
    ((map u φ t).f (-(n : ℤ))) ((models E R).generator F n c x) =
      (models D S).generator G n (c ⋙ u) (t.app (op c.right) x)
  identity : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (r : ℤ) (x : ((models E R).bar.obj F).X r),
    ((map (𝟭 E) (RingHom.id R) (𝟙 F)).f r) x = x
  composition : ∀ {E D H : Type u} [SmallCategory E] [SmallCategory D] [SmallCategory H]
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (u : E ⥤ D) (v : D ⥤ H) (φ : R →+* S) (ψ : S →+* T)
    {F : Eᵒᵖ ⥤ ModuleCat.{u} R} {G : Dᵒᵖ ⥤ ModuleCat.{u} S}
    {N : Hᵒᵖ ⥤ ModuleCat.{u} T}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ)
    (s : G ⟶ v.op ⋙ N ⋙ ModuleCat.restrictScalars ψ)
    (a : F ⟶ (u ⋙ v).op ⋙ N ⋙ ModuleCat.restrictScalars (ψ.comp φ)),
    (∀ (U : Eᵒᵖ) (x : F.obj U), a.app U x = s.app (u.op.obj U) (t.app U x)) →
    ∀ (r : ℤ) (x : ((models E R).bar.obj F).X r),
      ((map (u ⋙ v) (ψ.comp φ) a).f r) x =
        ((map v ψ s).f r) (((map u φ t).f r) x)
  lift : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R : Type u} [CommRing R] (u : E ⥤ D) {F : Eᵒᵖ ⥤ ModuleCat.{u} R}
    {G : Dᵒᵖ ⥤ ModuleCat.{u} R} (_t : F ⟶ u.op ⋙ G),
    (models E R).resolution.obj F ⟶
      (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapHomologicalComplex
        (.up ℤ)).obj ((models D R).resolution.obj G)
  lift_aug : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R : Type u} [CommRing R] (u : E ⥤ D) {F : Eᵒᵖ ⥤ ModuleCat.{u} R}
    {G : Dᵒᵖ ⥤ ModuleCat.{u} R} (t : F ⟶ u.op ⋙ G),
    lift u t ≫
      (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapHomologicalComplex
        (.up ℤ)).map ((models D R).augmentation.app G) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op) (.up ℤ) 0).hom.app G =
      (models E R).augmentation.app F ≫
        (CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).map t
  canonical : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R : Type u} [CommRing R] (u : E ⥤ D) {F : Eᵒᵖ ⥤ ModuleCat.{u} R}
    {G : Dᵒᵖ ⥤ ModuleCat.{u} R} (t : F ⟶ u.op ⋙ G),
    (models E R).colimitResolution.hom.app F ≫ map u (RingHom.id R) t =
      ((colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex
        (.up ℤ)).map (lift u t) ≫
      (categoryBarColimitReindex u).app ((models D R).resolution.obj G) ≫
      (models D R).colimitResolution.hom.app G
  scalarIso : ∀ {E : Type u} [SmallCategory E] {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) (G : Eᵒᵖ ⥤ ModuleCat.{u} S),
    (models E R).bar.obj (G ⋙ ModuleCat.restrictScalars φ) ≅
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
        ((models E S).bar.obj G)
  scalarFormula : ∀ {E : Type u} [SmallCategory E] {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) (G : Eᵒᵖ ⥤ ModuleCat.{u} S)
    (n : ℕ) (c : ComposableArrows E n) (x : G.obj (op c.right)),
    ((scalarIso φ G).hom.f (-(n : ℤ)))
      ((models E R).generator (G ⋙ ModuleCat.restrictScalars φ) n c x) =
        (models E S).generator G n c x
  scalarCanonical : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (u : E ⥤ D) (φ : R →+* S)
    {F : Eᵒᵖ ⥤ ModuleCat.{u} R} {G : Dᵒᵖ ⥤ ModuleCat.{u} S}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ),
    map u φ t = map u (RingHom.id R) t ≫ (scalarIso φ G).hom
  scalarExact : ∀ {E : Type u} [SmallCategory E] {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) (A : ShortComplex (Eᵒᵖ ⥤ ModuleCat.{u} S)),
    (∀ U : Eᵒᵖ, (A.map ((evaluation Eᵒᵖ (ModuleCat.{u} S)).obj U)).ShortExact) →
      ((A.map (models E S).bar).map
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ))).ShortExact
  connecting : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (u : E ⥤ D) (φ : R →+* S)
    (A : ShortComplex (Eᵒᵖ ⥤ ModuleCat.{u} R))
    (C : ShortComplex (Dᵒᵖ ⥤ ModuleCat.{u} S))
    (hA : ∀ U : Eᵒᵖ, (A.map ((evaluation Eᵒᵖ (ModuleCat.{u} R)).obj U)).ShortExact)
    (hC : ∀ U : Dᵒᵖ, (C.map ((evaluation Dᵒᵖ (ModuleCat.{u} S)).obj U)).ShortExact)
    (t₁ : A.X₁ ⟶ u.op ⋙ C.X₁ ⋙ ModuleCat.restrictScalars φ)
    (t₂ : A.X₂ ⟶ u.op ⋙ C.X₂ ⋙ ModuleCat.restrictScalars φ)
    (t₃ : A.X₃ ⟶ u.op ⋙ C.X₃ ⋙ ModuleCat.restrictScalars φ),
    (models E R).bar.map A.f ≫ map u φ t₂ =
      map u φ t₁ ≫ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        ((models D S).bar.map C.f) →
    (models E R).bar.map A.g ≫ map u φ t₃ =
      map u φ t₂ ≫ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        ((models D S).bar.map C.g) →
    DerivedCategory.triangleOfSESδ ((models E R).exact A hA) ≫
      (DerivedCategory.Q.map (map u φ t₁))⟦(1 : ℤ)⟧' =
        DerivedCategory.Q.map (map u φ t₃) ≫
          DerivedCategory.triangleOfSESδ (scalarExact φ C hC)
  homotopy : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (v w : E ⥤ D) (η : v ⟶ w)
    {F : Eᵒᵖ ⥤ ModuleCat.{u} R} {G : Dᵒᵖ ⥤ ModuleCat.{u} S}
    (φ : R →+* S) (t : F ⟶ w.op ⋙ G ⋙ ModuleCat.restrictScalars φ),
    Nonempty (Homotopy
      (map v φ (t ≫ Functor.whiskerRight
        (Functor.whiskerRight (NatTrans.op η) G) (ModuleCat.restrictScalars φ)))
      (map w φ t)) ∧
    DerivedCategory.Q.map
      (map v φ (t ≫ Functor.whiskerRight
        (Functor.whiskerRight (NatTrans.op η) G) (ModuleCat.restrictScalars φ))) =
      DerivedCategory.Q.map (map w φ t)

/-- The category bar complex computes the unbounded total left derived colimit, naturally
in indexing functors and coefficient rings, preserving exact sequences and connecting maps.
Natural transformations induce homotopic chain maps, hence equal derived maps.
Source: Stacks 08PF, 08PG, 08PH, 08PD and 07AC, with the bar prism extension
(blueprint: lem-trf-derived-colimit-bar).

Proof (the DAG argument, including the omitted contractions and prism cancellations):
1. Use the topology generated by singleton identity coverings, equivalently the pretopology of
   singleton isomorphisms. The sheaf condition for an isomorphism is automatic, so the module
   category is exactly the presheaf category in the statement. Kernels and cokernels are
   objectwise by [def-weil-sheaf-of-modules-category]. The constant functor preserves finite
   limits and has right adjoint the limit: a map from a constant object is precisely a
   compatible family of maps to all values. It therefore defines the stated geometric morphism
   with identity ring map. The required colimit exists explicitly: quotient $\bigoplus_UF(U)$ by
   the submodule generated by $\iota_Ux-\iota_VF(a)x$ for $a:V\to U$. Compatible families of
   linear maps are exactly maps out of this quotient. A map $F\to\underline M$ is precisely a
   cocone from $F$ to $M$, so [def-weil-pbc-category-colimit] identifies its left adjoint with
   $\operatorname{colim}_{\mathcal E^{op}}$.

2. The projection $\mathcal E\to *$ is continuous: isomorphisms and their pullbacks are carried
   to isomorphisms and their pullbacks. It is cocontinuous: the only covering of the point
   needed in the singleton-isomorphism pretopology is refined by $\{1_U\}$ for each $U$. All
   indexing sets are small in [def-weil-size-convention]. Apply [lem-trf-continuous-
   cocontinuous-derived-shriek] with $\mathcal O=R$ to get the unbounded triangulated $L\pi_!$
   and its adjunction to the exact constant functor. The same argument applies to any functor
   between categories with these topologies. For $u:\mathcal E\to\mathcal F$ it supplies $Lu_!$,
   adjoint to precomposition. Since the inverse images satisfy $\pi_{\mathcal
   E}^{-1}=u^{-1}\pi_{\mathcal F}^{-1}$, the Hom adjunctions identify $L\pi_{\mathcal F,!}Lu_!$
   with $L\pi_{\mathcal E,!}$, with the composite adjunction unit and counit.

3. For $U\in\mathcal E$ and an $R$-module $M$, define $L_U(M)(V)=\bigoplus_{a:V\to U}M$,
   restrictions sending the $a$-summand to the $a\circ b$-summand. A map $L_U(M)\to H$ is
   uniquely determined by its value on the identity summand at $U$: its value on $(a,m)$ must be
   $H(a)(f(m))$. Thus $\operatorname{Hom}(L_U(M),H)=\operatorname{Hom}_R(M,H(U))$. It follows
   directly from the lifting definition that $L_U(P)$ is projective when $P$ is a projective
   module. Every module has a free epimorphism, and $\bigoplus_{U,x\in H(U)}L_U(R)\to H$,
   $(a,r)\mapsto rH(a)(x)$, is surjective at $V$ because $x\in H(V)$ is hit by $(1_V,1)$. Direct
   sums of these projectives are projective: choose each lift and take their coproduct. Hence
   both module categories used below have enough projectives. Direct sums are exact: every
   element has finite support, and an element in a componentwise kernel has preimages in those
   finitely many components. In particular each $L_U$ is exact. The colimit universal property
   gives $\pi_!L_U(M)=M$, with every $a$-summand mapping identically to $M$.

4. Construct an augmented presheaf complex $B(F)$ by $B_n(F)=\bigoplus_{U_n\to\cdots\to
   U_0}L_{U_n}(F(U_0))$ in degree $-n$. At $V$ a generator is $(V\xrightarrow a U_n\to\cdots\to
   U_0,x)$. The first face removes $U_n$ and composes $a$ with the next arrow, internal faces
   compose adjacent arrows, and the last face removes $U_0$ and restricts $x$ to $U_1$. Use the
   alternating signs in the statement. The augmentation $B_0(F)(V)\to F(V)$ is $(a:V\to
   U_0,x)\mapsto F(a)x$. Deleting two vertices in either order yields the same generator and
   coefficient: for internal vertices this is associativity, and at the coefficient end it is
   $F(ab)=F(b)F(a)$. Thus $d_i d_j=d_{j-1}d_i$ for $i<j$; the corresponding two terms of $d^2$
   have opposite signs. This proves $d^2=0$ and compatibility with the augmentation.

5. At a fixed $V$, insert $V$ at the left of the displayed chain: $s_n(V\xrightarrow a
   U_n\to\cdots\to U_0,x)=(V\xrightarrow{1}V\xrightarrow a U_n\to\cdots\to U_0,x)$, and
   $s_{-1}(x)=(1_V,x)$. Deleting the inserted vertex is the identity, while every other deletion
   is insertion after the corresponding old deletion. Therefore $ds_n+s_{n-1}d=1$ on the
   augmented complex, also in degree zero, where the extra term is $s_{-1}\varepsilon$.
   Consequently $B(F)(V)\to F(V)[0]$ is a quasi-isomorphism for every $V$. Kernels and cokernels
   are objectwise, so $B(F)\to F[0]$ is a quasi-isomorphism of module presheaves. This
   contraction is asserted only after evaluation; it need not be a natural presheaf contraction.

6. Fix a chain-indexed family of modules $M_c$ and objects $U_c$. By [lem-trf-bounded-above-
   acyclic-derived-computation], choose projective module resolutions $P_c\to M_c[0]$, all zero
   in positive degrees. The complex $\bigoplus_c L_{U_c}(P_c)$ is a projective resolution of
   $\bigoplus_c L_{U_c}(M_c)$: exactness and projectivity were proved in step 3. Applying
   $\pi_!$ gives $\bigoplus_cP_c\to(\bigoplus_cM_c)[0]$, which is a quasi-isomorphism by the
   same finite-support calculation. Projective computation in the cited node therefore shows
   that every $\bigoplus_c L_{U_c}(M_c)$ is left $\pi_!$-acyclic. Similarly, for $u:\mathcal
   E\to\mathcal F$, the adjunction calculation of step 3 gives $u_!L_U(M)=L_{uU}(M)$: their Hom
   sets into $G$ are both $\operatorname{Hom}_R(M,G(uU))$. Applying $u_!$ to the same projective
   resolution gives an exact resolution $\bigoplus_cL_{uU_c}(P_c)$, so these objects are also
   left $u_!$-acyclic.

7. Each term of $B(F)$ has the form in step 6, and $B(F)$ is bounded above by zero. Apply [lem-
   trf-bounded-above-acyclic-derived-computation] to its quasi-isomorphic augmentation from step
   5. This gives the canonical identification $L\pi_!F\simeq\pi_!B(F)$. Step 3 identifies the
   latter's degree $-n$ with $\bigoplus_{U_n\to\cdots\to U_0}F(U_0)$. Its faces are exactly the
   stated faces, since a morphism between the representable factors becomes the identity on the
   coefficient after colimit. In degree two they are precisely the three summands displayed in
   the statement. The derived comparison in the cited node makes this a natural identification
   in $F$, not merely an equality of homology groups.

8. For $0\to F'\to F\to F''\to0$ objectwise exact, every degree of $K$ is a direct sum, over the
   same set of chains, of the exact sequence at $U_0$. The finite-support argument of step 3
   proves injectivity, kernel equality and surjectivity of that direct sum. All coefficient maps
   commute with restriction, so this is a short exact sequence of complexes. The identical
   argument also gives a short exact sequence of presheaf bar resolutions $B(F')\to B(F)\to
   B(F'')$.

9. First work over a single ring $R$. Given $t:F\to u^{-1}G$, send a generator of $B_{\mathcal
   E}(F)(V)$ to $(uV\xrightarrow{u(a)}uU_n\to\cdots\to uU_0,t_{U_0}x)$ in $B_{\mathcal
   F}(G)(uV)$. This commutes with the augmentation by naturality of $t$. It commutes with every
   face: functoriality of $u$ handles compositions, and the coefficient face is exactly
   $t_{U_1}F(U_1\to U_0)=G(uU_1\to uU_0)t_{U_0}$. By adjunction this gives $u_!B_{\mathcal
   E}(F)\to B_{\mathcal F}(G)$. Step 6 and [lem-trf-bounded-above-acyclic-derived-computation]
   identify its source with $Lu_!F$ and its target with $G$, compatibly with the augmentations.
   Thus it represents the derived adjunct $Lu_!F\to G$ of $t$. Applying $L\pi_{\mathcal F,!}$,
   and the composite adjunction of step 2, gives the canonical map of Tag 08PD. That
   identification is computed on these models: by the explicit adjunction clause of [lem-trf-
   continuous-cocontinuous-derived-shriek] (take $f=\mathrm{id}$, then compose with
   $\varepsilon_C^{-1}$), at a complex $C$ with $\varepsilon_C$ invertible the derived unit is
   $g^{-1}(\varepsilon_C^{-1})\circ Q(C\to g^{-1}g_!C)$. Hence on $B_{\mathcal E}(F)$ the
   derived units of $L\pi_{\mathcal E,!}$ and of $L\pi_{\mathcal F,!}Lu_!$ are both represented
   by the termwise unit $B_{\mathcal E}(F)\to\pi_{\mathcal E}^{-1}\pi_{\mathcal E,!}B_{\mathcal
   E}(F)=u^{-1}\pi_{\mathcal F}^{-1}\pi_{\mathcal F,!}u_!B_{\mathcal E}(F)$, so the step-2
   isomorphism is the identity of $K_{\mathcal E}(F)$ on the models of step 7. Both complexes of
   representable sums are $\pi_{\mathcal F,!}$-acyclic by step 6; the cited comparison therefore
   computes this map by applying ordinary $\pi_{\mathcal F,!}$ to the displayed map. Its formula
   is precisely $(U_\bullet,x)\mapsto(uU_\bullet,t_{U_0}x)$.

10. For $R\to S$, replace $G$ temporarily by its restriction $\operatorname{Res}_R^S G$.
   Restriction changes neither underlying abelian groups nor any differential or direct sum, so
   $B_R(\operatorname{Res}G)=\operatorname{Res}B_S(G)$ and
   $K_R(\operatorname{Res}G)=\operatorname{Res}K_S(G)$ by their displayed formulas. Their
   augmentations are the same maps. The acyclicity proofs of steps 3 and 6 apply over both rings
   separately; [lem-trf-bounded-above-acyclic-derived-computation] identifies these complexes
   with their respective derived colimits. This supplies the canonical scalar-restriction
   identification, and step 9 gives exactly the requested semilinear chain map under it. No
   assertion that restriction preserves projectives, and no flatness of $S$ over $R$, is used.

11. For identity functor and identity coefficient map, each generator is unchanged. Composing
   $(u,t)$ and $(v,s)$ sends $(U_\bullet,x)$ first to $(uU_\bullet,t_{U_0}x)$ and then to
   $(vuU_\bullet,s_{uU_0}t_{U_0}x)$, exactly the formula for the composite coefficient map.
   These are equal chain maps before localization. Therefore they give the identity and
   composition laws for the canonical derived maps of steps 9 and 10. The argument works also
   for composable coefficient-ring maps because the same underlying maps are used at every
   restriction of scalars.

12. Connecting morphisms are compatible as well. For a short exact sequence of complexes
   $A\xrightarrow i B\xrightarrow p C$, the chain map $q:\operatorname{Cone}(i)\to C$,
   $(b,a)\mapsto p(b)$, is a quasi-isomorphism: its kernel has terms $A^r\oplus A^{r+1}$ and
   differential $(a,a')\mapsto(da+a',-da')$, contracted by $(a,a')\mapsto(0,a)$. The connecting
   morphism is represented by the roof $C\xleftarrow
   q\operatorname{Cone}(i)\xrightarrow{-\mathrm{pr}}A[1]$, using [def-weil-abstract-derived-
   category]'s cone convention. A morphism of short exact sequences induces the map
   $(b,a)\mapsto(f_Bb,f_Aa)$ on these cones; it commutes with $q$ and with $-\mathrm{pr}$. Apply
   this to the short exact sequences of $B$ and $K$ in step 8. The augmentation $B(F)\to F$
   gives a morphism of such sequences. The natural comparisons in [lem-trf-bounded-above-
   acyclic-derived-computation] and triangulatedness of $L\pi_!$ therefore identify the $K$-roof
   with the derived connecting morphism. The maps of step 9 give morphisms of the same roofs.
   Their squares with connecting morphisms commute already as roof diagrams. Exact scalar
   restriction preserves this calculation, proving the semilinear claim too.

13. For the natural transformation clause put $p_r$, $0\leq r\leq n$, for the map sending
   $(U_n\to\cdots\to U_0,x)$ to the length-$(n+1)$ chain $$vU_n\to\cdots\to
   vU_{n-r}\xrightarrow{\eta_{U_{n-r}}}wU_{n-r}\to\cdots\to wU_0$$ with coefficient $t_{U_0}x\in
   G(wU_0)$. Define $H_n=\sum_{r=0}^n(-1)^rp_r:K_{\mathcal E}(F)^{-n}\to K_{\mathcal
   F}(G)^{-n-1}$ and $H_{-1}=0$. These maps are linear, also after scalar restriction. At the
   two ends $d_0p_0=K(w,t)$ and $d_{n+1}p_n=K(v,G(\eta)t)$: the last equality is precisely the
   restriction $G(\eta_{U_0})t_{U_0}$. At degree zero this says
   $dH_0(U,x)=(wU,t_Ux)-(vU,G(\eta_U)t_Ux)$.

14. For $j<r$, deleting a vertex before the inserted arrow gives $d_jp_r=p_{r-1}d_j$. For
   $j>r+1$, deleting after it gives $d_jp_r=p_rd_{j-1}$; at the coefficient end this uses the
   naturality of $t$. At the junction, for $0\leq r<n$, naturality $w(a)\eta_V=\eta_Uv(a)$ for
   $a:V\to U$ gives $d_{r+1}p_r=d_{r+1}p_{r+1}$. In $dH+Hd$ the first two kinds cancel because
   their signs are respectively $(-1)^{j+r}$ versus $(-1)^{j+r-1}$ and $(-1)^{j+r}$ versus
   $(-1)^{j+r-1}$. The junction terms cancel between $p_r$ and $p_{r+1}$. The only survivors are
   the two end terms of step 13, with signs $+1$ and $(-1)^n(-1)^{n+1}=-1$. Hence
   $dH+Hd=K(w,t)-K(v,G(\eta)t)$. This proves the stated chain homotopy, and [def-weil-abstract-
   derived-category] identifies homotopic maps after passage to the derived category. If $\eta$
   is an isomorphism its coefficient maps are isomorphisms, giving the last assertion. All
   constructions use finite sums in each input generator, including identity arrows; they
   require no nonemptiness or finiteness of the categories.

The records above are just the explicit data and laws of this assertion; no definition
chooses a bar complex or an adjunction from this postponed existence theorem. -/
theorem categoryColimitBarSystem_exists : Nonempty CategoryColimitBarSystem.{u} := by
  sorry

end CategoryTheory
