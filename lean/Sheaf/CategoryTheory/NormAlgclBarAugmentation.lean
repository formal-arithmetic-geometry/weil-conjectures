/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.Paper.IndUnipotentSystem
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # The noncomplete scalar bar augmentation

Source: main-20261015 six-functors direct-images proof, paragraph (3), agent-formulated
noncomplete scalar comparison, exact external reference WANTED
(blueprint: lem-sfb-norm-algcl-bar-augmentation).

## Main definitions

* `augmentation`: the actual cochain map induced by a resolution augmentation, with its
  component in bar degree n inserted into the (n,0) summand of the finite total.
* `Assertion`: invertibility of this map, all-continuous evaluations, resolution
  independence, and the invariant-inclusion normalization in degree zero.

The ordinary internal-module and compatible bar models are the recorded constructions.
No complete-field acyclicity theorem is applied to the algebraic closure.
Evaluation uses the recorded generalized-element interface on S x H^q itself.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar Profinite.CondensedAction
namespace Profinite.NormAlgclBar

variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {F : InternalFunctions A} (B : BarDiagram (G := G) F)
  [ActionAbelian A G] {N : Equivariant A G}

/-- The component of the canonical resolution augmentation is the bar functor applied
 to N -> I^0, followed by the (n,0) coprojection. All other source summands vanish.
Source: node statement and proof, step 6
(blueprint: lem-sfb-norm-algcl-bar-augmentation). -/
def augmentationComponent (I : InjectiveResolution N) (n : ℕ) :
    ((cochains B).obj N).X n ⟶ ((totalCochains B).obj I.cocomplex).X n :=
  ((cochains B).map (I.ι.f 0)).f n ≫
    (doubleComplex B I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)

/-- These components commute with the differentials.
Source: node proof, step 6 (blueprint: lem-sfb-norm-algcl-bar-augmentation).
Proof: naturality of the bar differential gives the horizontal part. The vertical part
vanishes because I.ι is a chain map from a complex concentrated in degree zero, hence
I.ι.f 0 followed by the resolution differential is zero. The total differential is
exactly d_bar + (-1)^n d_res. Nonadjacent differentials are zero by the complex shape. -/
theorem augmentationComponent_comm (I : InjectiveResolution N) (i j : ℕ) :
    augmentationComponent B I i ≫ ((totalCochains B).obj I.cocomplex).d i j =
      ((cochains B).obj N).d i j ≫ augmentationComponent B I j := by
  sorry

/-- The actual augmentation before localization, with fully specified data.
Source: node statement, j_A, and proof step 6
(blueprint: lem-sfb-norm-algcl-bar-augmentation). -/
def augmentation (I : InjectiveResolution N) :
    (cochains B).obj N ⟶ (totalCochains B).obj I.cocomplex where
  f := augmentationComponent B I
  comm' := fun i j _ ↦ augmentationComponent_comm B I i j

/-- Localize this particular augmentation in the ordinary internal-module derived category.
Source: node statement, j_A (blueprint: lem-sfb-norm-algcl-bar-augmentation). -/
def derivedAugmentation [HasDerivedCategory.{u + 2} (Modules A)]
    (I : InjectiveResolution N) :
    DerivedCategory.Q.{u + 2}.obj (extend ((cochains B).obj N)) ⟶
      DerivedCategory.Q.{u + 2}.obj (extend ((totalCochains B).obj I.cocomplex)) :=
  DerivedCategory.Q.{u + 2}.map
    (HomologicalComplex.extendMap (augmentation B I) ComplexShape.embeddingUpNat)

/-- The resolution augmentation after invariants, with the canonical single-complex
comparison. It is the independently specified degree-zero normalization on the target.
Source: node proof, steps 7 and 8
(blueprint: lem-sfb-norm-algcl-bar-augmentation). -/
def invariantResolutionAugmentation (V : Invariants A G) (I : InjectiveResolution N) :
    (CochainComplex.single₀ (Modules A)).obj (V.functor.obj N) ⟶
      (V.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  (HomologicalComplex.singleMapHomologicalComplex V.functor (.up ℕ) 0).inv.app N ≫
    (V.functor.mapHomologicalComplex (.up ℕ)).map I.ι

/-- The fixed trivial-action scalar module; the action is the identity on every section.
Source: node statement, A with trivial H action
(blueprint: lem-sfb-norm-algcl-bar-augmentation). -/
abbrev scalarModule (Ω : Type u) [NormedField Ω] (ℓ : ℕ) [Fact ℓ.Prime] :=
  (Profinite.CondensedAction.trivial (R := (continuousScalarRing Ω).toMon)
    (P := IndUnipotent.IntegerGroup.{u} ℓ)).obj (Mod.regular (continuousScalarRing Ω).X)

/-- Evaluation of an underived bar term, using the recorded generalized-function
evaluation on the tautological parameter over S x H^q.
No finite-extension restriction is made on these continuous functions.
Source: node statement, U_A^q and its evaluation description
(blueprint: lem-sfb-norm-algcl-bar-augmentation). -/
def evaluation (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
    {F : InternalFunctions (continuousScalarRing Ω)}
    (B : BarDiagram (G := IndUnipotent.IntegerGroup.{u} ℓ) F)
    (q : ℕ) (S : Profinite.{u})
    (x : sections (continuousScalarRing Ω) (((cochains B).obj (scalarModule Ω ℓ)).X q) S) :
    C(S × power (IndUnipotent.IntegerGroup.{u} ℓ) q, Ω) :=
  ((F.evaluate (power (IndUnipotent.IntegerGroup.{u} ℓ) q) S
    (Mod.regular (continuousScalarRing Ω).X)
      ((B.term (scalarModule Ω ℓ) q).hom.hom.hom.app (op S) x)).val
    (Profinite.of (S × power (IndUnipotent.IntegerGroup.{u} ℓ) q))
    (CompHausLike.ofHom _ ContinuousMap.fst)
    (ContinuousMap.snd : C(S × power (IndUnipotent.IntegerGroup.{u} ℓ) q,
      power (IndUnipotent.IntegerGroup.{u} ℓ) q))).down

/-- The complete assertion on any compatible model supplied by the recorded derived-bar
node. Source: node statement and proof steps 4,6,7,8
(blueprint: lem-sfb-norm-algcl-bar-augmentation).
The last square uses both independently normalized invariant augmentations, so the
induced degree-zero map is the identity on the scalar module, rather than an unspecified
isomorphism. Every resolution comparison preserving the original augmentation is included. -/
def ModelAssertion (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
    [ActionAbelian (continuousScalarRing Ω) (IndUnipotent.IntegerGroup.{u} ℓ)]
    [IsGrothendieckAbelian.{u + 1}
      (Equivariant (continuousScalarRing Ω) (IndUnipotent.IntegerGroup.{u} ℓ))]
    [HasDerivedCategory.{u + 2}
      (Equivariant (continuousScalarRing Ω) (IndUnipotent.IntegerGroup.{u} ℓ))]
    [HasDerivedCategory.{u + 2} (Modules (continuousScalarRing Ω))]
    (M : Model (continuousScalarRing Ω) (IndUnipotent.IntegerGroup.{u} ℓ)) : Prop :=
  (∀ (q : ℕ) (S : Profinite.{u}), Function.Bijective (evaluation ℓ Ω M.bar q S)) ∧
  (((cochains M.bar).obj (scalarModule Ω ℓ)).d 0 1 = 0) ∧
  (∀ I : InjectiveResolution (scalarModule Ω ℓ),
    IsIso (derivedAugmentation M.bar I)) ∧
  (∀ (I J : InjectiveResolution (scalarModule Ω ℓ))
    (f : I.cocomplex ⟶ J.cocomplex), I.ι ≫ f = J.ι →
      IsIso (DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap
        ((totalCochains M.bar).map f) ComplexShape.embeddingUpNat)) ∧
      derivedAugmentation M.bar I ≫
        DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap
          ((totalCochains M.bar).map f) ComplexShape.embeddingUpNat) =
        derivedAugmentation M.bar J) ∧
  IsIso (M.invariants.inclusion.app (scalarModule Ω ℓ)) ∧
  IsIso (HomologicalComplex.homologyMap (M.augmentation.map.app (scalarModule Ω ℓ)) 0) ∧
  (∀ I : InjectiveResolution (scalarModule Ω ℓ),
    HomologicalComplex.homologyMap (M.augmentation.map.app (scalarModule Ω ℓ)) 0 ≫
      HomologicalComplex.homologyMap (augmentation M.bar I) 0 =
    HomologicalComplex.homologyMap
      (invariantResolutionAugmentation M.invariants I) 0 ≫
        HomologicalComplex.homologyMap (M.totalAugmentation.map.app I.cocomplex) 0)

/-- Existence of compatible ordinary models, and the assertion for every such model.
The categorical structures are conclusions, not extra hypotheses on Omega. Standard
localizations implement the prescribed common universe, as in the recorded bar theorem.
Source: node statement and lem-sfb-condensed-derived-invariant-bar
(blueprint: lem-sfb-norm-algcl-bar-augmentation). -/
def Assertion (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] : Prop := by
  refine ∃ h : ActionAbelian (continuousScalarRing Ω)
    (IndUnipotent.IntegerGroup.{u} ℓ), ?_
  letI := h
  refine ∃ g : IsGrothendieckAbelian.{u + 1}
    (Equivariant (continuousScalarRing Ω) (IndUnipotent.IntegerGroup.{u} ℓ)), ?_
  letI := g
  letI : HasDerivedCategory.{u + 2}
      (Equivariant (continuousScalarRing Ω) (IndUnipotent.IntegerGroup.{u} ℓ)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 2} (Modules (continuousScalarRing Ω)) :=
    HasDerivedCategory.standard _
  exact Nonempty (Model (continuousScalarRing Ω) (IndUnipotent.IntegerGroup.{u} ℓ)) ∧
    ∀ M : Model (continuousScalarRing Ω) (IndUnipotent.IntegerGroup.{u} ℓ),
      ModelAssertion ℓ Ω M

/-- For the norm algebraic closure itself the actual underived-to-derived total bar
augmentation is invertible, independent of compatible resolutions, and the identity
on A in degree zero. Existence of all categorical structures and of a model is part of
the conclusion; the assertion then ranges over every compatible model.
Source: main-20261015 direct-images proof, paragraph (3), noncomplete scalar input;
exact external reference WANTED (blueprint: lem-sfb-norm-algcl-bar-augmentation).

Proof:
1. Use lem-weil-pbc-sheaf-tensor-closed and
   def-weil-pbc-internal-abelian-sheaf-module-equivalence to pass to section-module
   sheaves. lem-pe-internal-section-tensor-comparison and the closed tensor adjunction
   of lem-pc-sheaf-modules-tensor-closed transport internal Hom and injective resolutions.
2. The independent analytic input lem-sfb-norm-algcl-profinite-cech-exact applies to
   Omega itself. Replace each finite covering family by its disjoint union; its fibre
   powers split into the products in def-weil-pbc-site-cech-complex. The alternating
   projections agree, giving positive covering Cech exactness.
3. Apply lem-weil-pbc-site-cech-vanishing-criterion to all profinite objects and defining
   finite covers. They are closed under fibre products and cofinal among covers.
   lem-sfb-modobj-grothendieck and lem-sp-grothendieck-enough-injectives give resolutions.
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison makes their evaluated
   augmentations quasi-isomorphisms, normalized by the identity in degree zero.
4. The free-generator adjunction identifies internal Hom from A[P] on S with sections
   on S x P: pull back a section along (T -> S,T -> P), and conversely evaluate on the
   tautological generator. These inverse maps are exactly the evaluation above and
   commute with every continuous parameter map. Use def-pur-sheaf-hom on the slice.
5. Apply step 3 to S x P. The resulting sectionwise comparison is a sheaf
   quasi-isomorphism, giving the ordinary derived-Hom column comparison, naturally in P.
6. Put P=H^q. Naturality respects deletion and adjacent addition in the nerve; the
   first face is trivial, including d^0=0. The compatible model from
   lem-sfb-condensed-derived-invariant-bar uses nonnegative resolutions and the sign
   d_bar + (-1)^q d_res of def-sp-double-complex-total. Apply
   lem-sc-first-quadrant-total-column-comparison. Its total map has precisely the
   components augmentationComponent, hence its localization is derivedAugmentation.
7. lem-weil-pbc-injective-resolution-lift-exists gives every comparison lift preserving
   the augmentation. Naturality on each summand gives the displayed square.
   lem-sp-derived-injective-resolution-naturality identifies it with canonical change
   of resolution. By lem-weil-pbc-lift-to-injective-unique-up-to-homotopy any two lifts
   are homotopic; multiplying the homotopy in bar degree q by (-1)^q totalizes it.
8. H^0 is a point, so the zeroth term is A and the augmentation on its resolution is
   the original A -> I^0. The invariant inclusion for the trivial module is the identity
   identification with A. Naturality of both invariant augmentations gives the final
   cohomology square. Empty test objects give zero sections and negative degrees vanish.
   Only finite total diagonals are used; there is no completion or solidification.
-/
theorem norm_algcl_bar_augmentation (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (hΩ : ∀ a : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] Ω a‖ = ‖a‖) : Assertion ℓ Ω := by
  sorry

end Profinite.NormAlgclBar
