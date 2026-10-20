/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Sheaf.AlgebraicGeometry.OpenClosedRecollement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.EtaleStratifiedStalkIdentification

/-!
# Smooth stratification of bounded constructible etale complexes of finite Tor amplitude

Source: Stacks Project, Tags 09BI, 03TT, 0B8X, 095L and 0658; the finite smooth
refinement and localization assembly in the DAG
(blueprint: lem-sf-etale-smooth-stratified-ctf).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace AlgebraicGeometry.Etale

/-- Smooth connected strata with constant finite projective local models in the prescribed
Tor interval, and a finite localization tower in the ordinary etale derived category.
Source: Stacks Project, Tags 09BI, 03TT, 0B8X, 095L and 0658
(blueprint: lem-sf-etale-smooth-stratified-ctf).

Proof plan:
1. Finite coefficients are Noetherian. Finite type over a field makes X Noetherian
   (lem-weil-pbc-finite-type-over-noetherian) and finite dimensional
   (lem-kun-dimension-finite-type). Tensor with the constant coefficient unit to obtain
   cohomological bounds [a,b]. Exact inverse image commutes with cohomology
   (prop-weil-pbc-inverse-image-modules-exact); constructibility restricts
   (prop-constructible-pullback).
2. Replace X by its reduced induced closed subscheme
   (lem-weil-pbc-reduced-induced-closed-subscheme). The empty-complement localization
   sequence identifies K with the exact closed image of its restriction
   (lem-cbc-open-closed-recollement, lem-weil-pbc-open-closed-short-exact).
3. On each reduced residual closed subscheme, intersect the finitely many generic
   constancy opens of the nonzero cohomology sheaves
   (prop-constructible-generic-constancy). Residual schemes and their opens remain
   Noetherian and finite type (lem-weil-pbc-noetherian-open-subscheme-noetherian).
4. An algebraically closed field is perfect. Reduced finite-type schemes are
   geometrically reduced (lem-kun-geometric-reduced-perfect). Intersect with a dense
   smooth open (lem-pur-geometrically-reduced-dense-smooth-open), then remove the other
   finitely many components to obtain disjoint irreducible opens
   (lem-weil-pbc-noetherian-finite-components).
5. Noetherian induction on closed subsets terminates the peeling process
   (lem-weil-pbc-noetherian-scheme-closed-subsets-minimal). Give every residual closed
   subset its reduced structure. Each stratum is smooth and irreducible, hence connected
   and pure dimensional. Closing chains of irreducible closed subsets in X preserves
   strict inclusions, proving the dimension bound (def-kun-topological-krull-dimension).
6. Test Tor amplitude against the constant sheaf of every A-module, including infinite
   modules. Exact geometric stalks and tensor/pullback identify this with the ring Tor
   condition (prop-weil-pbc-geometric-stalks-exact, lem-kun-stalk-as-pullback,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
   lem-weil-pbc-constant-sheaf-geometric-stalk).
7. Finite lisse cohomology gives etale-local bounded constant finite-module complexes
   (lem-weil-pbc-finite-ring-derived-local-constancy). A geometric point on each nonempty
   cover member identifies its model with a stalk, hence gives the same Tor interval.
   Apply lem-weil-bounded-finite-tor-perfect to obtain finite projective models supported
   in [a,b]. Split finite free surjections by projectivity. Represent their derived
   isomorphisms by chain maps (lem-pc-ring-derived-map-representative). Constant sheaves
   preserve the finite exact sequences in the cone, hence these quasi-isomorphisms
   (lem-constructible-constant-exact). Inverse-image composition is module-linear
   (lem-weil-pbc-inverse-image-composition-module-linear).
8. Apply localization on successive residual closed schemes
   (lem-cbc-open-closed-recollement), then push by their exact closed direct images.
   Exact derived functors preserve triangles (lem-sf-exact-functor-derived-triangulated).
   Composition identifies the middle terms with the residual closed images of K;
   reduction identifies the first with K and the empty final residual scheme gives zero.
9. For each stratum take the open complement in X of the next residual closed subset.
   The stratum is closed in this open by closed-immersion base change
   (lem-weil-pbc-closed-immersion-base-change). Closed immersions are proper
   (lem-weil-pbc-closed-immersion-proper) and the open is quasi-compact by Noetherianity.
   Proper/open interchange (lem-weil-pbc-etale-open-proper-interchange) identifies the
   first term with j_! i_* P. Extension by zero is ordinary etale extension
   (def-weil-pbc-extension-by-zero). No finite-field-origin assumption is used. -/
theorem exists_smooth_stratification_finiteTor
    (F : Type u) [Field F] [IsAlgClosed F]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [X.Over (Spec (.of F))]
    [IsSeparated (X ↘ Spec (.of F))]
    [LocallyOfFiniteType (X ↘ Spec (.of F))] [QuasiCompact (X ↘ Spec (.of F))]
    (a b : ℤ) (hab : a ≤ b) (K : DerivedCategoryModule A X)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hTor : DerivedCategory.hasTorAmplitudeIn A X a b K) :
    ∃ (m : ℕ) (S V : Fin m → Scheme.{u})
      (i : ∀ r : Fin m, S r ⟶ V r) (j : ∀ r : Fin m, V r ⟶ X)
      (_ : ∀ r : Fin m, IsClosedImmersion (i r))
      (_ : ∀ r : Fin m, IsOpenImmersion (j r))
      (e : Fin m → ℕ) (P : ∀ r : Fin m, DerivedCategoryModule A (S r))
      (T : Fin (m + 1) → DerivedCategoryModule A X),
      (∀ r : Fin m, IsReduced (S r) ∧ ConnectedSpace (S r) ∧
        Smooth (i r ≫ j r ≫ (X ↘ Spec (.of F)))) ∧
      (Set.univ = ⋃ r : Fin m, Set.range (i r ≫ j r).base) ∧
      (∀ r t : Fin m, r ≠ t →
        Disjoint (Set.range (i r ≫ j r).base) (Set.range (i t ≫ j t).base)) ∧
      (∀ r : Fin m, (e r : WithBot ℕ∞) ≤ topologicalKrullDim X ∧
        ∀ C ∈ irreducibleComponents (S r),
          topologicalKrullDim C = (e r : WithBot ℕ∞)) ∧
      (∀ r : Fin m, P r =
        (upperStar (ModuleCat.{u + 1} A) (i r ≫ j r)).mapDerivedCategory.obj K) ∧
      (∀ (r : Fin m) (q : ℤ), Scheme.IsFiniteLocallyConstantSheaf
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf (S r).smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj (P r))) ∧
      (∀ r : Fin m, ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage (S r), ∀ t : 𝒰.I₀,
        ∃ Q : CochainComplex (ModuleCat.{u + 1} A) ℤ,
          (∀ q : ℤ, q < a ∨ b < q → IsZero (Q.X q)) ∧
          (∀ q : ℤ, ∃ (n : ℕ)
            (ι : Q.X q ⟶ ModuleCat.of A (Fin n → A))
            (π : ModuleCat.of A (Fin n → A) ⟶ Q.X q), ι ≫ π = 𝟙 (Q.X q)) ∧
          Nonempty ((upperStar (ModuleCat.{u + 1} A) (𝒰.f t)).mapDerivedCategory.obj (P r) ≅
            _root_.DerivedCategory.Q.obj
              (((constantSheaf (𝒰.X t).smallEtaleTopology
                (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q))) ∧
      T 0 = K ∧ IsZero (T (Fin.last m)) ∧
      (∀ r : Fin m, ∃
        (α : (openImmersionLowerShriek (ModuleCat.{u + 1} A) (j r)).mapDerivedCategory.obj
          ((lowerStar (ModuleCat.{u + 1} A) (i r)).mapDerivedCategory.obj (P r)) ⟶
            T r.castSucc)
        (β : T r.castSucc ⟶ T r.succ)
        (δ : T r.succ ⟶
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) (j r)).mapDerivedCategory.obj
            ((lowerStar (ModuleCat.{u + 1} A) (i r)).mapDerivedCategory.obj (P r)))⟦(1 : ℤ)⟧),
        Triangle.mk α β δ ∈ distTriang (DerivedCategoryModule A X)) := by
  sorry

end AlgebraicGeometry.Etale
