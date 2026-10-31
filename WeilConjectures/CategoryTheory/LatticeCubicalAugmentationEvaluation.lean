/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.LatticeCubicalEvaluationModel

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import WeilConjectures.CategoryTheory.DiscreteLatticeKoszulResolution
public import WeilConjectures.CategoryTheory.CondensedDerivedRestrictionCalculus
public import WeilConjectures.CategoryTheory.CondensedActionTensor
public import WeilConjectures.AlgebraicTopology.IntegralLatticeCubicalContraction
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Cubical augmentation and signed Koszul evaluation

Source: current blueprint, direct-images proof, paragraph (3), agent lattice expansion
(blueprint: lem-sfb-lattice-cubical-augmentation-evaluation).

All existential data below are pinned by coproduct coordinates, action, boundary and
local evaluation formulas. No object is chosen from the concluding existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar
open CategoryTheory.CondensedDerivedRestriction
namespace Profinite.DiscreteLattice.CubicalEvaluation

variable (A : CondensedBar.Ring.{u}) (r : ℕ)

section

-- Use the canonical instances directly in these definitions, avoiding alias conversions.
attribute [-instance] sheafMonoidal latticeTopologicalGroup moduleMonoidal

/-- Signed Hom identification and evaluation, with all normalizations in local coordinates.
The two differential equations say exactly df = d_P f - (-1)^(a+b) f partial.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
structure Evaluation (B : DiscreteComparison A r) (K : KoszulModel A.toMon r)
    (C : CubicalModel A r) where
  E : ∀ P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)),
    HomologicalComplex.tensorObj
      ((trivialComplex A r).obj ((total A r B K).obj P.obj)) C.L ⟶ P.obj
  evaluation : ∀ (P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)))
      (a : ℕ) (b : ℤ) (v : Fin r → ℤ) (I : Subsets r (a : ℤ)),
    tensorCell A r B K C P.obj a b a b (by omega) v I.val ≫ ((E P).f b).val =
      theta a b • ((ρ_ _).hom ≫ coordinateAction A r B K (P.obj.X b) a I v)
  offDiagonal : ∀ (P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)))
      (a k : ℕ) (b : ℤ) (v : Fin r → ℤ) (I : Subsets r (k : ℤ)), a ≠ k →
    tensorCell A r B K C P.obj a b k ((a : ℤ) + b + -(k : ℤ)) rfl v I.val ≫
      ((E P).f ((a : ℤ) + b + -(k : ℤ))).val = 0
  naturality : ∀ {P Q : CochainComplex.Plus (CondensedBar.Equivariant A (D r))}
      (f : P ⟶ Q),
    HomologicalComplex.tensorHom
      ((trivialComplex A r).map ((total A r B K).map f.hom)) (𝟙 C.L) ≫ E Q =
      E P ≫ f.hom
  b : ∀ P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)),
    (invariantComplex A r).obj P.obj ⟶ (total A r B K).obj P.obj
  invariantCoordinates : ∀ (P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)))
      (n : ℤ) (I : Subsets r 0),
    (b P).f n =
      (CondensedDerivedRestriction.invariants A (D r)).inclusion.app (P.obj.X n) ≫
        (B.underlying.inv.app (P.obj.X n)) ≫
          biproduct.ι (fun _ : Subsets r 0 ↦ (B.equivalence.functor.obj (P.obj.X n)).V) I ≫
          (K.coordinates _ 0).inv ≫ summand A r B K P.obj 0 n ≫
            eqToHom (congrArg (((total A r B K).obj P.obj).X) (zero_add n))
  normalization : ∀ P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)),
    HomologicalComplex.tensorHom ((trivialComplex A r).map (b P)) (𝟙 C.L) ≫ E P =
      tensorAugmentation A r C.ε
        ((trivialComplex A r).obj ((invariantComplex A r).obj P.obj)) ≫
          (invariantInclusion A r).app P.obj
  homIso : ∀ (P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)))
      (a : ℕ) (b : ℤ),
    (K.functor.obj (B.equivalence.functor.obj (P.obj.X b))).X (a : ℤ) ≅
      equivariantHom A r (C.L.X (-(a : ℤ))) (P.obj.X b)
  homCoordinates : ∀ (P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)))
      (a : ℕ) (b : ℤ) (v : Fin r → ℤ) (I : Subsets r (a : ℤ)),
    ((homIso P a b).hom ⊗ₘ cell A r C.L C.ι (-(a : ℤ)) v I.val) ≫
      ((actionTensor A (D r)).forgetCore.μIso
        ((CondensedAction.trivial (R := A.toMon) (P := D r)).obj
          (equivariantHom A r (C.L.X (-(a : ℤ))) (P.obj.X b)))
        (C.L.X (-(a : ℤ)))).hom ≫
      (homEvaluation A r (C.L.X (-(a : ℤ))) (P.obj.X b)).val =
        theta a b • ((ρ_ _).hom ≫ coordinateAction A r B K (P.obj.X b) a I v)
  homVertical : ∀ (P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)))
      (a : ℕ) (b : ℤ),
    (-1 : ℤ) ^ a •
      ((K.functor.map (B.equivalence.functor.map (P.obj.d b (b + 1)))).f a ≫
        (homIso P a (b + 1)).hom) =
      (homIso P a b).hom ≫ (CondensedDerivedRestriction.invariants A (D r)).functor.map
        ((ihom (C.L.X (-(a : ℤ)))).map (P.obj.d b (b + 1)))
  homHorizontal : ∀ (P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)))
      (a : ℕ) (b : ℤ),
    (K.functor.obj (B.equivalence.functor.obj (P.obj.X b))).d a ((a : ℤ) + 1) ≫
        (homIso P (a + 1) b).hom =
      (-1 : ℤ) ^ (((a : ℤ) + b + 1).natAbs) •
        ((homIso P a b).hom ≫ (CondensedDerivedRestriction.invariants A (D r)).functor.map
          ((MonoidalClosed.pre (C := CondensedBar.Equivariant A (D r))
            (A := C.L.X (-(a : ℤ))) (B := C.L.X (-((a + 1 : ℕ) : ℤ)))
            (C.L.d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ)))).app (P.obj.X b)))

/-- Rank zero is ordinary evaluation, in the canonical unique-vertex coordinates.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def RankZero (B : DiscreteComparison A r) (K : KoszulModel A.toMon r)
    (C : CubicalModel A r) (F : Evaluation A r B K C) : Prop :=
  r = 0 → IsIso C.ε ∧
    ∀ P : CochainComplex.Plus (CondensedBar.Equivariant A (D r)),
      ∃ (z : (total A r B K).obj P.obj ≅ (forgetComplex A r).obj P.obj)
        (e : (trivialComplex A r).obj ((total A r B K).obj P.obj) ≅ P.obj),
      (∀ n : ℤ, (e.hom.f n).val = z.hom.f n) ∧
      (∀ n : ℤ, summand A r B K P.obj 0 n ≫
        eqToHom (congrArg (((total A r B K).obj P.obj).X) (zero_add n)) ≫ z.hom.f n =
          coordinateAction A r B K (P.obj.X n) 0 ⟨∅, rfl⟩ 0) ∧
      F.E P = HomologicalComplex.tensorHom e.hom C.ε ≫
        (HomologicalComplex.rightUnitor P.obj).hom

/-- Internal cubical augmentation, K-flatness and the signed Koszul evaluation, including
its Hom-differential identification, invariant normalization and rank-zero normalization.
Every map is a morphism of the original internal modules, so it is natural under all
profinite restrictions; evaluation is also natural in bounded-below equivariant complexes.
Source: current blueprint, direct-images proof, paragraph (3), agent lattice expansion
(blueprint: lem-sfb-lattice-cubical-augmentation-evaluation).

Proof:
1. Apply lem-sfb-lattice-cubical-sheaf-resolution to the regular module. Its coproducts,
   boundary, augmentation, translation and origin section give CubicalModel. Replace
   each coefficient of the integral contraction from
   lem-sfb-integral-lattice-cubical-contraction by that integer multiple of the identity.
   Column finiteness makes every resulting internal map well defined. Translation
   commutes with boundary and augmentation, but no equivariance of the section or
   contraction is imposed. All integer matrices commute with profinite restriction.
2. On a tensor summand of input degree p use H = (-1)^p times 1 tensor h. Expanding the
   total differential cancels the two mixed terms and gives dH+Hd=1-(1 tensor s)(1 tensor
   epsilon). Also (1 tensor epsilon)(1 tensor s)=1. The augmentation is therefore a
   homotopy equivalence after forgetting action, for arbitrary unbounded complexes.
   Forgetting detects exactness by lem-sfb-condensed-derived-restriction-calculus;
   lem-pe-internal-section-tensor-comparison identifies the ordinary internal total.
   Thus tensoring L with an acyclic complex is acyclic and its trivial-input
   augmentations are quasi-isomorphisms, with no flatness assumption on the input.
3. Constant lattice sections define the discrete comparison. An inverse extends the
   discrete action over the finitely many clopen fibres of any map from a profinite
   set to the discrete lattice. Two normalized comparisons differ by the composite of
   their underlying identifications, which intertwines the constant actions; every
   clause below is transported along it, so it holds for each comparison B. The
   coproduct universal property identifies an equivariant map on L^(-a) with its
   coordinates on the origin cells [0,I]. The same
   argument in every slice identifies internal Hom modules, not only global Hom sets.
4. Set c_a=(-1)^(a(a+1)/2) and theta_(a,b)=(-1)^(ab)c_a. The recurrences
   theta_(a+1,b)=(-1)^(a+b+1)theta_(a,b) and
   theta_(a,b+1)=(-1)^a theta_(a,b) identify the Koszul-first total differential with
   d_P f-(-1)^(a+b)f partial. All scaling factors are their own inverses.
5. Define evaluation on a tensor summand by theta_(a,b)T^v x_I when the cell degree is
   a, and zero otherwise. Balanced bilinearity gives the internal map. In cell degree
   a only the vertical terms contribute, with (-1)^a theta_(a,b+1)=theta_(a,b).
   In cell degree a+1 the horizontal and boundary contributions cancel by the first
   recurrence; in all other degrees both sides vanish. Thus evaluation is a chain map.
6. Translation changes T^v into T^(v+w)=T^w T^v. Equivariant morphisms commute with all
   these operators and coordinate projections, giving naturality. The same finite
   clopen decomposition verifies equivariance for all generalized lattice sections.
7. An invariant coefficient is killed by every T_i-1. Its degree-zero Koszul inclusion
   is b. On a vertex, theta_(0,b)=1 and T^v x=x, proving the normalization equation;
   on positive cells both sides vanish. At rank zero there is just the unique vertex,
   L is the regular module in degree zero, augmentation is identity and evaluation is
   the ordinary right unitor. The zero ring and arbitrary characteristics need no
   exception since only integral sums and signs occur.
-/
theorem lattice_cubical_augmentation_evaluation :
    ∃ C : CubicalModel A r,
      (∀ P : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ,
        P.Acyclic → (HomologicalComplex.tensorObj P C.L).Acyclic) ∧
      (∀ X : CochainComplex (CondensedBar.Modules A) ℤ,
        QuasiIso (tensorAugmentation A r C.ε ((trivialComplex A r).obj X))) ∧
      Nonempty (DiscreteComparison A r) ∧
      ∀ (B : DiscreteComparison A r) (K : KoszulModel A.toMon r),
        ∃ F : Evaluation A r B K C, RankZero A r B K C F := by
  sorry

end

end Profinite.DiscreteLattice.CubicalEvaluation
