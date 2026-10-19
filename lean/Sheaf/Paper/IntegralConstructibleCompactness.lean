/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosureExistence
public import Sheaf.CategoryTheory.CompactObject
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.IntegralConstructibleExt
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.YonedaDerivedExtComparison
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Sheaf.CategoryTheory.CompactObjectsThick
import Sheaf.Paper.IntegralConstructibleHeart

/-!
# Integral constructible complexes are compact

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-int-compactness,
sk-prop-int-compactness-compact.md and its proof
(blueprint: det-prop-int-compactness-compact).

The assertion bundle expands the three clauses with the actual ambient module category.
`H.ind` is the full replete filtered-colimit image IndCons; Dic is expanded cohomologically.
The realization is characterized as the filtered-colimit-preserving extension of the
inclusion along Ind.yoneda. Thus it sends every formal filtered diagram to its ambient
colimit, including the induced maps. No unconstrained realization functor is assumed.
All coproducts and truncations are in the ordinary unbounded derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The three assertions of integral compactness, with the ambient category and its
constructible classes as parameters. Source: blueprint main-20261015,
sk-prop-int-compactness-compact, clauses 1--3
(blueprint: det-prop-int-compactness-compact).

Exactness means preservation of finite limits and finite colimits, whose existence
in Ind is included. The natural isomorphism on representables and preservation of
filtered colimits specify the colimit realization up to its unique compatible
isomorphism. The window clause asserts invertibility of the two actual Hom maps of
`K <- tau_le(m) K -> tau_ge(m-d_C) tau_le(m) K`, after shifting by m. Their composite,
inverting the first map, is the asserted natural isomorphism. The final clause uses
the recorded compact-object definition on the full localizing subcategory itself. -/
def IntegralConstructibleCompactnessAssertions
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    (H : ObjectProperty A) (B : ObjectProperty (DerivedCategory A))
    (d : H.FullSubcategory → ℕ) : Prop :=
  (HasFiniteLimits (Ind H.FullSubcategory) ∧
    HasFiniteColimits (Ind H.FullSubcategory) ∧
    ∃ Φ : Ind H.FullSubcategory ⥤ A,
      Nonempty (Ind.yoneda ⋙ Φ ≅ H.ι) ∧ PreservesFilteredColimits.{v} Φ ∧
      PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ ∧ Φ.Full ∧ Φ.Faithful ∧
      Φ.essImage = H.ind.{v} ∧
      (∀ S : ShortComplex A, S.ShortExact →
        H.ind.{v} S.X₁ → H.ind.{v} S.X₃ → H.ind.{v} S.X₂) ∧
      (∀ (M N : A) (f : M ⟶ N), H.ind.{v} M → H.ind.{v} N →
        H.ind.{v} (kernel f) ∧ H.ind.{v} (cokernel f)) ∧
      (∀ (C : H.FullSubcategory) (N : A), H.ind.{v} N →
        ∀ q : ℤ, (d C : ℤ) < q →
          Subsingleton (((DerivedCategory.singleFunctor A 0).obj C.obj) ⟶
            ((DerivedCategory.singleFunctor A 0).obj N)⟦q⟧))) ∧
  ((∀ (I : Type v) (K : I → DerivedCategory A),
      (∀ (i : I) (n : ℤ), H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj (K i))) →
      ∃ (c : Cofan K) (_ : IsColimit c),
        ∀ n : ℤ, H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj c.pt)) ∧
    (∀ K : DerivedCategory A,
      (∀ n : ℤ, H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj K)) →
      ∀ (m n : ℤ),
        H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj
          ((DerivedCategory.TStructure.t.truncLE m).obj K)) ∧
        H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj
          ((DerivedCategory.TStructure.t.truncGE m).obj K))) ∧
    (∀ K : DerivedCategory A, localizingClosure B K →
      ∀ n : ℤ, H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj K)) ∧
    (∀ (C : H.FullSubcategory) (K : DerivedCategory A),
      (∀ n : ℤ, H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj K)) →
      ∀ m : ℤ,
        IsIso ((preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor A 0).obj C.obj))).map
            ((shiftFunctor (DerivedCategory A) m).map
              ((DerivedCategory.TStructure.t.truncLEι m).app K))) ∧
        IsIso ((preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor A 0).obj C.obj))).map
            ((shiftFunctor (DerivedCategory A) m).map
              ((DerivedCategory.TStructure.t.truncGEπ (m - (d C : ℤ))).app
                ((DerivedCategory.TStructure.t.truncLE m).obj K)))))) ∧
  (∃ hc : HasCoproducts.{v} (localizingClosure B).FullSubcategory,
    ∀ C : (localizingClosure B).FullSubcategory, B C.obj →
      @CategoryTheory.IsCompactObject _ _ _ hc C)

/-- Integral constructible complexes are compact in their localizing closure, together
with the exact Ind realization, extension/kernel/cokernel closure, uniform Ext bound,
and canonical finite-window assertions. Source: blueprint main-20261015,
sk-prop-int-compactness-compact, all three clauses
(blueprint: det-prop-int-compactness-compact).

Proof plan, following the fifteen DAG steps:
1. Use the internal-module/section-ring-sheaf equivalence and the Grothendieck
   ring-sheaf theorem for exact filtered colimits. The integral heart is essentially
   small, abelian with ambient kernels/cokernels, and extension closed. Integral Ext
   continuity gives Hom and Ext^1 continuity; singleFunctor is fully faithful.
2. Compute Hom between two realized filtered diagrams as lim_i colim_j Hom(C_i,D_j).
   This proves full faithfulness and the stated essential image. The presheaf
   universal property and lem-sfb-ind-filtered-colimits give filtered-colimit
   preservation and the realization isomorphism on representables.
3. Finite sums are realized over products of the filtered indices. An arbitrary
   sum is the filtered colimit of its finite partial sums; include the empty sum.
4. Present an Ind arrow over one filtered index using lem-sfb-ind-arrow-presentation.
   Exact filtered colimits identify its kernel/cokernel with the colimits of their
   constructible counterparts. The image is abelian with ambient exact structure;
   transport that structure through the fully faithful realization for exactness.
5. Pull an extension back along each stage C_a of its quotient. Ext^1 continuity
   lifts its class to an extension by one constructible stage D_i. The Yoneda/derived
   Ext comparison, pushout-short-exact-sequence theorem and short five lemma identify
   the pulled-back extension with the pushout of that finite-stage extension.
6. Over i/I, the pushouts D_j amalgamated with its constructible middle term are
   constructible and have colimit the pulled-back extension. The undercategory is
   filtered and its diagram of D_j still has the original kernel as colimit.
7. The colimit of the pulled-back extensions is the original extension, by exact
   filtered colimits and the short five lemma. This proves extension closure.
8. Ext continuity extends the chosen bound d_C from constructible sheaves to
   their filtered colimits. Finite partial sums give continuity for arbitrary sums.
9. Long exact cohomology, kernel/cokernel/extension closure make Dic triangulated.
   Truncations retain or kill cohomology; termwise derived sums commute with
   cohomology. Thus Dic is sum closed and contains Dbc and hence its localizing closure.
10. For bounded lower tails, remove the highest cohomology successively. Each Hom
    layer vanishes by the Ext bound; exact Hom into the truncation triangle gives zero.
11. For unbounded lower tails use pro-etale left completeness and derived products.
    In the Milnor sequence the Hom limit is zero. The degree -1 tower becomes
    isomorphisms beyond d_C; recursively solving 1-T gives zero cokernel and zero Hom.
12. The upper truncation triangle has Hom-zero outer terms in degrees 1 and 2 by
    t-structure orthogonality. The lower triangle has tails ending at -d_C-1 and
    -d_C-2 after shift; step 11 kills both. Hence both canonical Hom arrows are isos.
13. Represent a family in one finite cohomological interval by complexes with a
    common lower bound. Ext continuity for the filtered diagram of finite partial
    sums gives the direct-sum comparison, with its actual coprojection maps.
14. Apply the finite-window reduction simultaneously to each summand and its sum.
    Exact sums commute with both truncations. Naturality makes the coprojection
    square commute, giving compactness of constructible sheaves without a bound
    on the original family.
15. Compact objects are thick (lem-sc-compact-objects-thick). Shifts and finite
    truncation devissage extend compactness to every bounded constructible complex. -/
theorem integralConstructibleCompactness
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X → ℕ)
    (hd : ∀ (C N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (q : ℤ), (d C : ℤ) < q →
        Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧)) :
    IntegralConstructibleCompactnessAssertions
      (IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X) d := by
  sorry

end AlgebraicGeometry.ProEtale
