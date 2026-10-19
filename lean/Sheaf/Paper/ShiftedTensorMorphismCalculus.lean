/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Products.Associator
public import Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.Paper.RingedTopoiTensorComparisonData
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Signed calculus of shifted derived tensor morphisms

Source: literature/stacks-project/sites-cohomology.tex, Tags 0FPL and 0FPM
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warn.sorry false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

/-- The module category on the ringed site. Source: Stacks 03DA
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedModuleCategory {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) :=
  CategoryTheory.ringedSiteModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

/-- Its unbounded derived category. Source: Stacks 05RR
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedDerivedCategory {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (ShiftedModuleCategory R)] :=
  DerivedCategory (ShiftedModuleCategory R)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})
  [HasDerivedCategory.{w} (ShiftedModuleCategory R)]

/-- Flat-term K-flat resolving complexes. Source: Stacks 06YS and 06YU
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorResolving : ObjectProperty (CochainComplex (ShiftedModuleCategory R) ℤ) :=
  fun E ↦ E.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (E.X n)

/-- The ordinary tensor bifunctor, with the dependency's canonical sheaf tensor.
Source: Stacks 03EK (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedOrdinaryTensor :=
  @curriedTensor (ShiftedModuleCategory R) _ (monoidalCategory R)

/-- Total tensor, with the differential sign on the second factor.
Source: Stacks 06YM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedTotalTensor :=
  Functor.uncurry.obj ((shiftedOrdinaryTensor R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

/-- A presentation of the derived tensor by the natural resolving comparison.
This is precisely the tensor and its representative isomorphism from site-derived-tensor
 descent; quantifying over presentations makes the statement independent of this choice.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
structure ShiftedTensorModel where
  tensor : ShiftedDerivedCategory R × ShiftedDerivedCategory R ⥤ ShiftedDerivedCategory R
  representative : ((shiftedTensorResolving R).ι.prod (shiftedTensorResolving R).ι) ⋙
    shiftedTotalTensor R ⋙ DerivedCategory.Q ≅
    (((shiftedTensorResolving R).ι ⋙ DerivedCategory.Q).prod
      ((shiftedTensorResolving R).ι ⋙ DerivedCategory.Q)) ⋙ tensor

/-- The recorded site-derived tensor admits exactly the resolving presentation used here.
This connects the presentation-independent calculus to the dependency's actual bifunctor.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Step 3): take the tensor and homotopy representative comparison from
site_derived_tensor_descent_independentCoefficients. Precompose its two comparisons
with the resolving complexes' homotopy quotient and compose with quotientCompQhIso.
The membership equivalence identifies precisely the K-flat flat-term objects.
The resulting natural comparison supplies the displayed model of the recorded tensor. -/
theorem shiftedTensorPublishedModel_exists :
    ∃ T : ShiftedTensorModel R,
      T.tensor = siteDerivedTensorIndependentCoefficients J R := by
  sorry

/-- Move the second shift first, then the first shift. Thus the only sign is
`(-1)^(bp)` with p the degree in E[a], exactly the node's convention.
Source: Stacks sign rules, item-shift-tensor
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorComplexComparison
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (a b : ℤ) :
    (shiftedTotalTensor R).obj (E⟦a⟧, F⟦b⟧) ≅
      ((shiftedTotalTensor R).obj (E, F))⟦a + b⟧ :=
  letI := monoidalCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  CochainComplex.mapBifunctorShift₂Iso (E⟦a⟧) F (shiftedOrdinaryTensor R) b ≪≫
    (CategoryTheory.shiftFunctor _ b).mapIso
      (CochainComplex.mapBifunctorShift₁Iso E F (shiftedOrdinaryTensor R) a) ≪≫
    (shiftFunctorAdd _ a b).symm.app _

variable (T : ShiftedTensorModel R)

/-- Normalization of t on every resolving model, with localization's shift comparisons.
Source: Stacks 06YU and sign rules (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalShiftComparison (a b : ℤ)
    (t : ((CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) a).prod
      (CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) b) ⋙ T.tensor) ≅
      T.tensor ⋙ CategoryTheory.shiftFunctor _ (a + b)) : Prop :=
  ∀ (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F),
    ∃ (hEa : shiftedTensorResolving R (E⟦a⟧))
      (hFb : shiftedTensorResolving R (F⟦b⟧)),
      T.representative.hom.app (⟨E⟦a⟧, hEa⟩, ⟨F⟦b⟧, hFb⟩) ≫
        T.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso a).hom.app E)
          ((DerivedCategory.Q.commShiftIso b).hom.app F)) ≫
        t.hom.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) =
      DerivedCategory.Q.map (shiftedTensorComplexComparison R E F a b).hom ≫
        (DerivedCategory.Q.commShiftIso (a + b)).hom.app _ ≫
        (CategoryTheory.shiftFunctor _ (a + b)).map
          (T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩))

/-- The canonical comparison is uniquely determined by the resolving square.
Source: Stacks 06YU; proof Steps 1--3 of the node
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof: the two complex shift isomorphisms give the coefficient (-1)^(bp), and are natural.
Shifts preserve K-flatness and flat terms (Step 2). Transport through the representative
comparison and extend the resulting transformation and its inverse by the unique-extension
clause of site-derived-tensor descent (Step 3). Uniqueness proves the inverse equations
and the asserted uniqueness. -/
theorem shiftedTensorCanonicalComparison_exists (a b : ℤ) :
    ∃! t : ((CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) a).prod
      (CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) b) ⋙ T.tensor) ≅
      T.tensor ⋙ CategoryTheory.shiftFunctor _ (a + b),
      IsCanonicalShiftComparison R T a b t := by
  sorry

/-- The comparison fixed by the actual resolving square, not a free parameter.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorCanonicalComparison (a b : ℤ) :=
  (shiftedTensorCanonicalComparison_exists R T a b).exists.choose

/-- Signed swap on total complexes, characterized on every summand. These equations
specify an actual map, including its sign; existence is part of the derived normalization.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsSignedComplexSwap (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E)) : Prop :=
  ∀ p q : ℤ,
    CochainComplex.ιMapBifunctor E F (shiftedOrdinaryTensor R) p q (p + q) rfl ≫
      χ.hom.f (p + q) =
    ((-1 : ℤ) ^ Int.natAbs (p * q)) •
      (((symmetricCategory R).braiding (E.X p) (F.X q)).hom ≫
        CochainComplex.ιMapBifunctor F E (shiftedOrdinaryTensor R) q p (p + q)
          (add_comm q p))

/-- Derived symmetry is the image of the signed swap on K-flat representatives.
Source: Stacks 0FPQ and 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalDerivedTensorSymmetry
    (σ : T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor) : Prop :=
  ∀ (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F),
    ∃ χ : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E),
      IsSignedComplexSwap R E F χ ∧
      T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩) ≫
          σ.hom.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) =
        DerivedCategory.Q.map χ.hom ≫
          T.representative.hom.app (⟨F, hF⟩, ⟨E, hE⟩)

/-- Existence and uniqueness of the signed derived symmetry.
Source: Stacks 0FPQ and 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Step 3): define the swap by its summand equations. The differential coefficients
of y tensor dx agree modulo 2, as do those of dy tensor x. The reverse swap is its inverse.
It is natural; descend it and its inverse using the unique-extension clause of tensor descent.
The summand equations determine the chain map and descent determines the natural isomorphism. -/
theorem derivedTensorSymmetry_exists :
    ∃! σ : T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor,
      IsCanonicalDerivedTensorSymmetry R T σ := by
  sorry

/-- Canonical Koszul symmetry, fixed by the signed representative equations.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def derivedTensorSymmetry := (derivedTensorSymmetry_exists R T).exists.choose

/-- B is tensor of the two maps followed by the canonical shift comparison.
Source: Stacks 0FPL/0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorB (a b : ℤ) (P Q K L : ShiftedDerivedCategory R)
    (f : P ⟶ K⟦a⟧) (g : Q ⟶ L⟦b⟧) :
    T.tensor.obj (P, Q) ⟶ (T.tensor.obj (K, L))⟦a + b⟧ :=
  T.tensor.map (Prod.mkHom f g) ≫
    (shiftedTensorCanonicalComparison R T a b).hom.app (K, L)

/-- The unsigned associator is fixed on triple total summands.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsComplexTensorAssociator (E F G : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ : (shiftedTotalTensor R).obj ((shiftedTotalTensor R).obj (E, F), G) ≅
      (shiftedTotalTensor R).obj (E, (shiftedTotalTensor R).obj (F, G))) : Prop :=
  ∀ p q r : ℤ,
    ((shiftedOrdinaryTensor R).map
      (CochainComplex.ιMapBifunctor E F (shiftedOrdinaryTensor R) p q (p + q) rfl)).app _ ≫
      CochainComplex.ιMapBifunctor ((shiftedTotalTensor R).obj (E, F)) G
        (shiftedOrdinaryTensor R) (p + q) r ((p + q) + r) rfl ≫
      χ.hom.f ((p + q) + r) =
    ((monoidalCategory R).associator (E.X p) (F.X q) (G.X r)).hom ≫
      ((shiftedOrdinaryTensor R).obj (E.X p)).map
        (CochainComplex.ιMapBifunctor F G (shiftedOrdinaryTensor R) q r (q + r) rfl) ≫
      CochainComplex.ιMapBifunctor E ((shiftedTotalTensor R).obj (F, G))
        (shiftedOrdinaryTensor R) p (q + r) ((p + q) + r) (add_assoc p q r).symm

/-- The left triple tensor functor. Source: Stacks 0FPQ
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedTensorLeftTriple := (T.tensor.prod (𝟭 _)) ⋙ T.tensor

/-- The right triple tensor functor. Source: Stacks 0FPQ
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedTensorRightTriple :=
  CategoryTheory.prod.associator (ShiftedDerivedCategory R) _ _ ⋙
    ((𝟭 _).prod T.tensor) ⋙ T.tensor

/-- The derived associator's full representative square, including tensor closure.
Source: Stacks 0FPQ/0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalTensorAssociator
    (α : shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T) : Prop :=
  ∀ (E F G : CochainComplex (ShiftedModuleCategory R) ℤ)
    (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F)
    (hG : shiftedTensorResolving R G),
    ∃ (hEF : shiftedTensorResolving R ((shiftedTotalTensor R).obj (E, F)))
      (hFG : shiftedTensorResolving R ((shiftedTotalTensor R).obj (F, G)))
      (χ : (shiftedTotalTensor R).obj ((shiftedTotalTensor R).obj (E, F), G) ≅
        (shiftedTotalTensor R).obj (E, (shiftedTotalTensor R).obj (F, G))),
      IsComplexTensorAssociator R E F G χ ∧
      T.representative.hom.app (⟨_, hEF⟩, ⟨G, hG⟩) ≫
        T.tensor.map (Prod.mkHom (T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩))
          (𝟙 (DerivedCategory.Q.obj G))) ≫
        α.hom.app ((DerivedCategory.Q.obj E, DerivedCategory.Q.obj F),
          DerivedCategory.Q.obj G) =
      DerivedCategory.Q.map χ.hom ≫
        T.representative.hom.app (⟨E, hE⟩, ⟨_, hFG⟩) ≫
        T.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj E))
          (T.representative.hom.app (⟨F, hF⟩, ⟨G, hG⟩)))

/-- The derived associator exists uniquely with its unsigned normalization.
Source: Stacks 0FPQ/0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Steps 2--3): tensor preserves sums by its right adjoint, so triple tensor
summands determine the unsigned associator and its inverse. Differential signs are
1, (-1)^p, (-1)^(p+q) on both sides. K-flatness of total tensor follows by applying
K-flatness twice to an acyclic test complex. Tensor products and sums of flat terms
are flat. Extend the representative square and its inverse by tensor descent,
variable by variable. Uniqueness on resolving triples gives uniqueness everywhere. -/
theorem derivedTensorAssociator_exists :
    ∃! α : shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T,
      IsCanonicalTensorAssociator R T α := by
  sorry

/-- Canonical associator, with no arbitrary associator parameter.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def derivedTensorAssociator := (derivedTensorAssociator_exists R T).exists.choose

/-- A module sheaf in degree zero. Source: Stacks 06YU
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedDegreeZero (P : ShiftedModuleCategory R) : ShiftedDerivedCategory R :=
  (DerivedCategory.singleFunctor _ 0).obj P

/-- Both additivity equations for flat degree-zero sources.
Source: Stacks 0FPL/0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorAdditivityClause (a b : ℤ) : Prop :=
  ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
    ∀ (K L : ShiftedDerivedCategory R)
      (f₁ f₂ : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g₁ g₂ : shiftedDegreeZero R Q ⟶ L⟦b⟧),
      shiftedTensorB R T a b _ _ K L (f₁ + f₂) g₁ =
        shiftedTensorB R T a b _ _ K L f₁ g₁ + shiftedTensorB R T a b _ _ K L f₂ g₁ ∧
      shiftedTensorB R T a b _ _ K L f₁ (g₁ + g₂) =
        shiftedTensorB R T a b _ _ K L f₁ g₁ + shiftedTensorB R T a b _ _ K L f₁ g₂

/-- Associativity for precisely three flat degree-zero source sheaves.
Source: Stacks 0FPL (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorAssociativityClause (a b c : ℤ) : Prop :=
  ∀ (P Q S : ShiftedModuleCategory R),
    IsFlatOnSite P → IsFlatOnSite Q → IsFlatOnSite S →
    ∀ (K L M : ShiftedDerivedCategory R)
      (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g : shiftedDegreeZero R Q ⟶ L⟦b⟧)
      (h : shiftedDegreeZero R S ⟶ M⟦c⟧),
      (derivedTensorAssociator R T).hom.app
          ((shiftedDegreeZero R P, shiftedDegreeZero R Q), shiftedDegreeZero R S) ≫
        shiftedTensorB R T a (b + c) _ _ K (T.tensor.obj (L, M)) f
          (shiftedTensorB R T b c _ _ L M g h) =
      shiftedTensorB R T (a + b) c _ _ (T.tensor.obj (K, L)) M
          (shiftedTensorB R T a b _ _ K L f g) h ≫
        (CategoryTheory.shiftFunctor _ ((a + b) + c)).map
          ((derivedTensorAssociator R T).hom.app ((K, L), M)) ≫
        (eqToIso (congrArg
          (fun n : ℤ ↦ (T.tensor.obj (K, T.tensor.obj (L, M)))⟦n⟧)
          (add_assoc a b c))).hom

/-- Symmetry with the scalar (-1)^(ab) and the specified sum-of-shifts identification.
Source: Stacks 0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorSymmetryClause (a b : ℤ) : Prop :=
  ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
    ∀ (K L : ShiftedDerivedCategory R)
      (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g : shiftedDegreeZero R Q ⟶ L⟦b⟧),
      shiftedTensorB R T a b _ _ K L f g ≫
        (CategoryTheory.shiftFunctor _ (a + b)).map
          ((derivedTensorSymmetry R T).hom.app (K, L)) =
      ((-1 : ℤ) ^ Int.natAbs (a * b)) •
        ((derivedTensorSymmetry R T).hom.app (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫
          shiftedTensorB R T b a _ _ L K g f ≫
          (eqToIso (congrArg (fun n : ℤ ↦ (T.tensor.obj (L, K))⟦n⟧)
            (add_comm b a))).hom)

/-- The local signed calculus for flat sources and arbitrary derived targets.
Source: Stacks 0FPL/0FPM; all ten proof steps of the DAG node are retained below
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof plan:
1. On E[a]^p tensor F[b]^q, move the second shift first. Its sign is (-1)^(bp);
   the two differential coefficients agree as checked in the node's Step 1.
2. The unsigned associator respects the coefficients 1, (-1)^p, (-1)^(p+q).
   Tensor and shifts preserve K-flatness and flat terms, by tensoring an acyclic
   test complex twice and using flatness of sums and tensor products.
3. Descend these maps and the Koszul swap uniquely using
   lem-weil-pbc-site-derived-tensor-descent, variable by variable.
4. Ordinary additive tensor preserves biproduct diagrams; resolving comparisons
   descend this property. Bilinear composition proves both additivity equations.
5. Associativity signs are bp+c(p+q)=cq+(b+c)p. Descend and precompose with f,g,h.
6. Symmetry signs differ by 2bp: bp+(p+a)(q+b) and ab+pq+aq. Descend and use naturality.
7. Flat degree-zero sheaves are K-flat (lem-pc-kflat-closure). Their tensor is flat
   because tensoring by it is the composite of two exact tensor functors. Thus the
   iterated B operations have the specified flat degree-zero sources.
8. For pullback, use the algebraic inverse image and scalar extension in
   def-weil-pbc-algebraic-inverse-image and the pure-tensor normalization of
   def-weil-pbc-canonical-ringed-tensor-comparison. Its associator and swap squares
   agree on locally generating pure tensors.
9. Module pullback preserves sums by lem-weil-pbc-ringed-topoi-module-adjunction.
   Sum the ordinary comparisons over bidegrees. Additivity preserves all differential,
   shift and swap signs; the unsigned associator is preserved by Step 8.
10. lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves resolving models.
   Its unique representative comparison descends the Step 9 diagrams. Exactness
   identifies its derived functor with termwise pullback. The degree-zero comparison
   identifies pulled-back f,g with maps out of uStar P,uStar Q, which are flat.
   Naturality of t gives the pullback clause, including all coherence squares. -/
theorem shiftedTensorMorphismCalculus_local (a b c : ℤ) :
    ShiftedTensorAdditivityClause R T a b ∧
    ShiftedTensorAssociativityClause R T a b c ∧
    ShiftedTensorSymmetryClause R T a b := by
  sorry

section Pullback

open CanonicalTensorPullbackOfUniverses
open scoped ChangeOfRings

variable {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
  [J'.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J' AddCommGrpCat.{max u v}]
  (S RI : Sheaf J' CommRingCat.{max u v})
  [HasDerivedCategory.{w} (ShiftedModuleCategory S)]
  (TS : ShiftedTensorModel S)
  (uInv : Sheaf J (Type (max u v)) ⥤ Sheaf J' (Type (max u v)))
  (uPush : Sheaf J' (Type (max u v)) ⥤ Sheaf J (Type (max u v)))
  (adj : uInv ⊣ uPush) [hlex : PreservesFiniteLimits uInv]
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (uStar : ShiftedModuleCategory R ⥤ ShiftedModuleCategory S)
  (hobj : ∀ M : ShiftedModuleCategory R, uStar.obj M = changeOfRings c (I.modules.obj M))
  (hmap : ∀ {M N : ShiftedModuleCategory R} (f : M ⟶ N),
    uStar.map f = eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M)
      (I.modules.map f) ≫ eqToHom (hobj N).symm)
  [uStar.Additive] [PreservesFiniteLimits uStar] [PreservesFiniteColimits uStar]
  (V : ShiftedModuleCategory S ⥤ ShiftedModuleCategory R) (am : uStar ⊣ V)
  (k : CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison.{u, v}
    R S RI uInv I c uStar hobj)

include uPush adj hmap hlex in
/-- The exact pullback comparison is uniquely fixed by the total-complex comparison.
No arbitrary natural isomorphism is assumed. The square uses the canonical ordinary
pure-tensor comparison k and the actual termwise derived functor.
Source: Stacks 07A4/03EL (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Steps 8--10): use the specified scalar-extension functor and its module adjunction.
The ordinary pure-tensor comparison gives k.totalIso. Exactness makes termwise pullback
invert every quasi-isomorphism. The normalized representative square in
ringedTopoiCanonicalDerivedTensorPullback then gives this comparison; tensor descent
proves uniqueness and independence of representatives. -/
theorem shiftedExactTensorPullback_exists :
    ∃! μ : T.tensor ⋙ uStar.mapDerivedCategory ≅
      (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor,
      ∀ (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
        (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F),
        ∃ (hE' : shiftedTensorResolving S
            ((uStar.mapHomologicalComplex (.up ℤ)).obj E))
          (hF' : shiftedTensorResolving S
            ((uStar.mapHomologicalComplex (.up ℤ)).obj F)),
          uStar.mapDerivedCategory.map
              (T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) ≫
            μ.hom.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) ≫
            TS.tensor.map (Prod.mkHom (uStar.mapDerivedCategoryFactors.hom.app E)
              (uStar.mapDerivedCategoryFactors.hom.app F)) =
          uStar.mapDerivedCategoryFactors.hom.app ((shiftedTotalTensor R).obj (E, F)) ≫
            DerivedCategory.Q.map (k.totalIso R S RI uInv I c uStar hobj V am E F).inv ≫
            TS.representative.hom.app (⟨_, hE'⟩, ⟨_, hF'⟩) := by
  sorry

/-- The canonical exact derived tensor comparison, fixed by its representative square.
Source: Stacks 07A4 (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedExactTensorPullback :=
  (shiftedExactTensorPullback_exists R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k).exists.choose

/-- All associator, Koszul symmetry and two-shift squares for exact pullback.
The proposition contains equations, rather than an unconstrained coherence hypothesis.
Source: Stacks 03EL/07A4 (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedPullbackCoherence
    (μ : T.tensor ⋙ uStar.mapDerivedCategory ≅
      (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor) : Prop :=
  (∀ X Y Z : ShiftedDerivedCategory R,
    uStar.mapDerivedCategory.map ((derivedTensorAssociator R T).hom.app ((X, Y), Z)) ≫
      μ.hom.app (X, T.tensor.obj (Y, Z)) ≫
      TS.tensor.map (Prod.mkHom (𝟙 (uStar.mapDerivedCategory.obj X)) (μ.hom.app (Y, Z))) =
    μ.hom.app (T.tensor.obj (X, Y), Z) ≫
      TS.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (uStar.mapDerivedCategory.obj Z))) ≫
      (derivedTensorAssociator S TS).hom.app
        ((uStar.mapDerivedCategory.obj X, uStar.mapDerivedCategory.obj Y),
          uStar.mapDerivedCategory.obj Z)) ∧
  (∀ X Y : ShiftedDerivedCategory R,
    uStar.mapDerivedCategory.map ((derivedTensorSymmetry R T).hom.app (X, Y)) ≫
      μ.hom.app (Y, X) =
    μ.hom.app (X, Y) ≫ (derivedTensorSymmetry S TS).hom.app
      (uStar.mapDerivedCategory.obj X, uStar.mapDerivedCategory.obj Y)) ∧
  ∀ (a b : ℤ) (X Y : ShiftedDerivedCategory R),
    uStar.mapDerivedCategory.map ((shiftedTensorCanonicalComparison R T a b).hom.app (X, Y)) ≫
      (uStar.mapDerivedCategory.commShiftIso (a + b)).hom.app (T.tensor.obj (X, Y)) ≫
      (CategoryTheory.shiftFunctor _ (a + b)).map (μ.hom.app (X, Y)) =
    μ.hom.app (X⟦a⟧, Y⟦b⟧) ≫
      TS.tensor.map (Prod.mkHom ((uStar.mapDerivedCategory.commShiftIso a).hom.app X)
        ((uStar.mapDerivedCategory.commShiftIso b).hom.app Y)) ≫
      (shiftedTensorCanonicalComparison S TS a b).hom.app
        (uStar.mapDerivedCategory.obj X, uStar.mapDerivedCategory.obj Y)

/-- The complete ringed-topos clause: flatness preservation, all coherence diagrams,
 and B on the actual pulled-back flat degree-zero source sheaves.
Source: Stacks 03EL, 07A4, 0G7E, 0FPL/0FPM
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof: follow Steps 8--10 of the ten-step plan. Pure tensors
prove ordinary coherence, direct sums give the total-complex comparisons, and additivity
preserves every sign. The normalized derived tensor comparison descends the diagrams
by tensor descent. The preservation clause gives flatness of uStar P (apply it to P[0]).
Exactness gives the termwise derived functor used here. Naturality of the shift square
with respect to f and g proves the B equation; mapDerivedCategorySingleFunctor supplies
exactly the source identification with (uStar P)[0], including identity pullbacks. -/
def ShiftedTensorPullbackClause (a b : ℤ) : Prop :=
    (∀ P : ShiftedModuleCategory R, IsFlatOnSite P → IsFlatOnSite (uStar.obj P)) ∧
    ShiftedPullbackCoherence R T S TS uStar
      (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k) ∧
    ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
      ∀ (K L : ShiftedDerivedCategory R)
        (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
        (g : shiftedDegreeZero R Q ⟶ L⟦b⟧),
        uStar.mapDerivedCategory.map (shiftedTensorB R T a b _ _ K L f g) ≫
          (uStar.mapDerivedCategory.commShiftIso (a + b)).hom.app (T.tensor.obj (K, L)) ≫
          (CategoryTheory.shiftFunctor _ (a + b)).map
            ((shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar
              hobj hmap V am k).hom.app (K, L)) =
        (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k).hom.app
            (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫
          TS.tensor.map (Prod.mkHom ((uStar.mapDerivedCategorySingleFunctor 0).hom.app P)
            ((uStar.mapDerivedCategorySingleFunctor 0).hom.app Q)) ≫
          shiftedTensorB S TS a b _ _ (uStar.mapDerivedCategory.obj K)
            (uStar.mapDerivedCategory.obj L)
            ((uStar.mapDerivedCategorySingleFunctor 0).inv.app P ≫
              uStar.mapDerivedCategory.map f ≫
              (uStar.mapDerivedCategory.commShiftIso a).hom.app K)
            ((uStar.mapDerivedCategorySingleFunctor 0).inv.app Q ≫
              uStar.mapDerivedCategory.map g ≫
              (uStar.mapDerivedCategory.commShiftIso b).hom.app L)

/-- The full signed calculus and its exact ringed-topos pullback law.
Source: Stacks 0FPL/0FPM; all ten proof steps of the DAG node are retained below
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof plan:
1. On E[a]^p tensor F[b]^q, move the second shift first. Its sign is (-1)^(bp);
   the two differential coefficients agree as checked in the node's Step 1.
2. The unsigned associator respects the coefficients 1, (-1)^p, (-1)^(p+q).
   Tensor and shifts preserve K-flatness and flat terms, by tensoring an acyclic
   test complex twice and using flatness of sums and tensor products.
3. Descend these maps and the Koszul swap uniquely using
   lem-weil-pbc-site-derived-tensor-descent, variable by variable.
4. Ordinary additive tensor preserves biproduct diagrams; resolving comparisons
   descend this property. Bilinear composition proves both additivity equations.
5. Associativity signs are bp+c(p+q)=cq+(b+c)p. Descend and precompose with f,g,h.
6. Symmetry signs differ by 2bp: bp+(p+a)(q+b) and ab+pq+aq. Descend and use naturality.
7. Flat degree-zero sheaves are K-flat (lem-pc-kflat-closure). Their tensor is flat
   because tensoring by it is the composite of two exact tensor functors. Thus the
   iterated B operations have the specified flat degree-zero sources.
8. For pullback, use the algebraic inverse image and scalar extension in
   def-weil-pbc-algebraic-inverse-image and the pure-tensor normalization of
   def-weil-pbc-canonical-ringed-tensor-comparison. Its associator and swap squares
   agree on locally generating pure tensors.
9. Module pullback preserves sums by lem-weil-pbc-ringed-topoi-module-adjunction.
   Sum the ordinary comparisons over bidegrees. Additivity preserves all differential,
   shift and swap signs; the unsigned associator is preserved by Step 8.
10. lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves resolving models.
   Its unique representative comparison descends the Step 9 diagrams. Exactness
   identifies its derived functor with termwise pullback. The degree-zero comparison
   identifies pulled-back f,g with maps out of uStar P,uStar Q, which are flat.
   Naturality of t gives the pullback clause, including all coherence squares. -/
theorem shiftedTensorMorphismCalculus (a b cshift : ℤ) :
    ShiftedTensorAdditivityClause R T a b ∧
    ShiftedTensorAssociativityClause R T a b cshift ∧
    ShiftedTensorSymmetryClause R T a b ∧
    ShiftedTensorPullbackClause R T S RI TS uInv uPush adj I c uStar hobj hmap V am k a b := by
  sorry

end Pullback
end SheafOfModules
