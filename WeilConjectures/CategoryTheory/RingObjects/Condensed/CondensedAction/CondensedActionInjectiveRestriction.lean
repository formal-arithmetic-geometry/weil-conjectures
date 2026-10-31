/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import WeilConjectures.CategoryTheory.CondensedDerivedRestriction.CondensedDerivedInvariants
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
public import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.ProductForgetting.ProductActionExactForgetting

/-! # Exact induction and injective restriction for internal condensed actions

Source: the latest blueprint, direct-image stability proof, paragraph (3), internal-bar
categorical input; Stacks 04BL, 03EV, 03EO, 015Z, 013K and 070I
(blueprint: lem-sfb-condensed-action-injective-restriction).

All constructions use arbitrary commutative condensed rings. Induction is specified by
its actual relative tensor, translation action and adjunction on generalized generators.
The invariant resolution computes derived invariants; it need not resolve invariants.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction.InternalBar

namespace Profinite.CondensedAction

attribute [instance] ProductInvariants.additive

variable (A : CategoryTheory.CondensedBar.Ring.{u})

/-- The recorded free internal module on a represented profinite set.
Source: Stacks 04BL and the composite free adjunction
(blueprint: lem-sfb-condensed-action-injective-restriction). -/
abbrev restrictionFree (S : Profinite.{u}) : Modules A.toMon :=
  (free A.toMon).obj (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj S)

/-- The actual generator from the unit of the recorded free adjunction.
Source: Stacks 04BL (blueprint: lem-sfb-condensed-action-injective-restriction). -/
def restrictionGenerator (S T : Profinite.{u}) (s : T ⟶ S) :
    sectionModule A.toMon (restrictionFree A S) T :=
  (((freeAdjunction A.toMon).unit.app
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj S)).hom.app (op T))
      (ULift.up s)

/-- The recorded equivalence to sectionwise module sheaves, at the prescribed sizes.
Source: Stacks 00YV (blueprint: lem-sfb-condensed-action-injective-restriction). -/
abbrev restrictionEquivalence :=
  InternalAbelianSheafModule.sectionModuleEquivalence (coherentTopology Profinite.{u}) A.X

/-- The coefficient ring sheaf underlying the section-module equivalence.
Source: Stacks 00YV (blueprint: lem-sfb-condensed-action-injective-restriction). -/
abbrev restrictionRing :=
  InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) A.X

/-- Evaluation of the equalizer internal Hom, using its inclusion into ambient Hom.
This uses the existing closed evaluation and lax sheaf-inclusion tensor map.
Source: Stacks 03EO and the equalizer internal-Hom definition
(blueprint: lem-sfb-condensed-action-injective-restriction). -/
def restrictionHomEvaluation (M N : Modules A.toMon) (S : Profinite.{u})
    (x : sectionModule A.toMon ((Mod.ihom' A.X M).obj N) S)
    (m : sectionModule A.toMon M S) : sectionModule A.toMon N S :=
  ((MonoidalClosed.uncurry
    (equalizer.ι (Mod.homModPre (Mod.act M.X) N) (Mod.homModB A.X M N)).hom).hom.app
      (op S))
    ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
      M.X ((Mod.ihom' A.X M).obj N).X).app (op S) (TensorProduct.tmul ℤ m x))

/-- The free represented module is module sheafification of the sectionwise direct sum,
and its tensor functor is exact. The comparisons preserve tensor, its local pairing,
and internal Hom, naturally in both module arguments.
Source: Stacks 04BL, 03EV and 03EO
(blueprint: lem-sfb-condensed-action-injective-restriction).

Proof:
1. Apply the internal-to-sectionwise equivalence of
   def-weil-pbc-internal-abelian-sheaf-module-equivalence. The normalized comparison in
   lem-pe-internal-section-tensor-comparison is exact and preserves the pure tensor.
2. The generator adjunction of def-sfb-condensed-free-module-adjunction and the
   bijection of lem-trf-free-module-sheaf-universal-property identify the free objects.
   Both comparison maps send [s] to [s], hence are inverse and natural.
3. The free presheaf on the represented sheaf has sections the direct sum indexed by
   maps V to S (with ULift in the coefficient universe). It is the extension by zero
   of the regular module on the localized site. Apply lem-pc-sites-modules-j-shriek-flat
   and transport through the exact tensor comparison to obtain internal flatness.
4. The tensor-Hom adjunctions of def-sfb-modobj-internal-hom and
   lem-pc-sheaf-modules-tensor-closed identify maps from every test module into the two
   Hom objects. Yoneda gives their canonical natural isomorphism; evaluation corresponds
   to the identity under the same adjunctions. The empty parameter gives zero, including
   on the empty test object by the empty-cover sheaf axiom. No coefficient is nonzero
   by assumption, so zero modules and the zero ring are included.
-/
theorem restriction_free_flat_comparison :
    PreservesFiniteLimits (restrictionEquivalence A).functor ∧
    PreservesFiniteColimits (restrictionEquivalence A).functor ∧
    (∀ S : Profinite.{u},
      ∃ e : (restrictionEquivalence A).functor.obj (restrictionFree A S) ≅
        (SheafFreeModule.free (restrictionRing A)).obj
          (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj S),
      (∀ (T : Profinite.{u}) (s : T ⟶ S),
        (e.hom.val.app (op T)) (restrictionGenerator A S T s) =
          (SheafFreeModule.generatorRaw (restrictionRing A)
            (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj S)).hom.app
              (op T) (ULift.up s)) ∧
      PreservesFiniteLimits (tensorLeft (restrictionFree A S)) ∧
      PreservesFiniteColimits (tensorLeft (restrictionFree A S))) ∧
    ∃ t : ∀ M N : Modules A.toMon,
        (restrictionEquivalence A).functor.obj (M ⊗ N) ≅
          (restrictionEquivalence A).functor.obj M ⊗
            (restrictionEquivalence A).functor.obj N,
      (∀ (M N : Modules A.toMon) (S : Profinite.{u})
          (m : sectionModule A.toMon M S) (n : sectionModule A.toMon N S),
        ((t M N).hom.val.app (op S)) (pureTensor A.toMon M N S m n) =
          InternalAbelianSheafModule.comparison_sectionTmul
            (coherentTopology Profinite.{u}) A.X
            ((restrictionEquivalence A).functor.obj M)
            ((restrictionEquivalence A).functor.obj N) (op S) m n) ∧
      (∀ (M M' N N' : Modules A.toMon) (f : M ⟶ M') (g : N ⟶ N'),
        (restrictionEquivalence A).functor.map (f ⊗ₘ g) ≫ (t M' N').hom =
          (t M N).hom ≫ ((restrictionEquivalence A).functor.map f ⊗ₘ
            (restrictionEquivalence A).functor.map g)) ∧
      ∃ h : ∀ M N : Modules A.toMon,
        (restrictionEquivalence A).functor.obj ((Mod.ihom' A.X M).obj N) ≅
          SheafOfModules.homObj (R := restrictionRing A) ((restrictionEquivalence A).functor.obj M)
            ((restrictionEquivalence A).functor.obj N),
        (∀ (M N : Modules A.toMon) (S : Profinite.{u})
            (x : sectionModule A.toMon ((Mod.ihom' A.X M).obj N) S)
            (m : sectionModule A.toMon M S),
          ((((h M N).hom.val.app (op S)) x).app (op (Over.mk (𝟙 S)))) m =
            restrictionHomEvaluation A M N S x m) ∧
        ∀ (M M' N N' : Modules A.toMon) (f : M' ⟶ M) (g : N ⟶ N'),
          ∃ k : (Mod.ihom' A.X M).obj N ⟶ (Mod.ihom' A.X M').obj N',
            k ≫ equalizer.ι _ _ = equalizer.ι _ _ ≫
              Mod.homModMap M.X g ≫ Mod.homModPre f.hom N' ∧
            (restrictionEquivalence A).functor.map k ≫ (h M' N').hom =
              (h M N).hom ≫ SheafOfModules.homObjMap
                (R := restrictionRing A)
                (M := (restrictionEquivalence A).functor.obj M)
                (M' := (restrictionEquivalence A).functor.obj M')
                (N := (restrictionEquivalence A).functor.obj N)
                (N' := (restrictionEquivalence A).functor.obj N')
                ((restrictionEquivalence A).functor.map f)
                ((restrictionEquivalence A).functor.map g) := by
  sorry

private theorem restriction_sections_inv_hom {M N : Modules A.toMon} (e : M ≅ N)
    (S : Profinite.{u}) (x : sectionModule A.toMon M S) :
    onSections A.toMon e.inv S (onSections A.toMon e.hom S x) = x := by
  change ((e.hom ≫ e.inv).hom.hom.app (op S)).hom x = x
  rw [e.hom_inv_id]
  rfl

variable (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- Exact induction left adjoint to forgetting the action. The natural underlying
comparison identifies the functor with A[P] tensor -, and the action and transposes
are fixed on generalized pure tensors.
Source: paragraph (3), exact-induction input
(blueprint: lem-sfb-condensed-action-injective-restriction). -/
structure ForgetTensorInduction where
  functor : Modules A.toMon ⥤ ActionModule A.toMon P
  additive : functor.Additive
  underlying : functor ⋙ forgetAction ≅
    tensorLeft (restrictionFree A (Profinite.of P))
  adjunction : functor ⊣ forgetAction
  translation : ∀ (M : Modules A.toMon) (S : Profinite.{u}) (p g : C(S, P))
    (m : sectionModule A.toMon M S),
    (functor.obj M).act S p
        (onSections A.toMon (underlying.inv.app M) S
          (pureTensor A.toMon _ M S
            (restrictionGenerator A (Profinite.of P) S (CompHausLike.ofHom _ g)) m)) =
      onSections A.toMon (underlying.inv.app M) S
        (pureTensor A.toMon _ M S
          (restrictionGenerator A (Profinite.of P) S (CompHausLike.ofHom _ (p * g))) m)
  untranspose : ∀ (M : Modules A.toMon) (X : ActionModule A.toMon P)
    (f : M ⟶ X.module) (S : Profinite.{u}) (g : C(S, P)) (m : sectionModule A.toMon M S),
    onSections A.toMon (((adjunction.homEquiv M X).symm f).val) S
      (onSections A.toMon (underlying.inv.app M) S
        (pureTensor A.toMon _ M S
          (restrictionGenerator A (Profinite.of P) S (CompHausLike.ofHom _ g)) m)) =
      X.act S g (onSections A.toMon f S m)
  limits : PreservesFiniteLimits functor
  colimits : PreservesFiniteColimits functor


/-- Forgetting an action preserves and detects exactness, has the normalized exact
free-tensor left adjoint, and preserves injectives.
Source: Stacks 03CX and 015Z; paragraph (3), induction input
(blueprint: lem-sfb-condensed-action-injective-restriction).

Proof:
1. Apply lem-sfb-product-action-exact-forgetting with first and retained group P.
   Its plainInduction has exactly the required free module, generator, tensor functor,
   adjunction and exactness. These definitions agree with the ones above.
2. Apply the inverse underlying comparison to its action equation and cancel the
   comparison followed by its inverse. This gives the stated translation formula.
   The inverse-transpose formula is already the required one.
3. Use CondensedDerivedRestriction.forgetExact for finite limits, finite colimits
   and detection of exactness. The exact left adjoint preserves monomorphisms, so
   Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms applies.
No group or coefficient nontriviality is assumed.
-/
theorem forget_tensor_induction :
    Nonempty (ForgetTensorInduction A P) ∧
    PreservesFiniteLimits (forgetAction (R := A.toMon) (P := P)) ∧
    PreservesFiniteColimits (forgetAction (R := A.toMon) (P := P)) ∧
    (∀ K : ShortComplex (ActionModule A.toMon P),
      K.Exact ↔ (K.map (forgetAction (R := A.toMon) (P := P))).Exact) ∧
    (forgetAction (R := A.toMon) (P := P)).PreservesInjectiveObjects := by
  obtain ⟨D⟩ := ProductForgetting.exists_datum A.toMon P P
    (Or.inl ⟨inferInstance, inferInstance, inferInstance⟩)
  let L := D.plainInduction
  let T : ForgetTensorInduction A P :=
    { functor := L.functor
      additive := L.additive
      underlying := L.tensorIso
      adjunction := L.adjunction
      translation := by
        intro M S p g m
        exact (restriction_sections_inv_hom A (L.tensorIso.app M) S _).symm.trans
          (congrArg (onSections A.toMon (L.tensorIso.inv.app M) S)
            (L.action M S p g m))
      untranspose := L.untranspose
      limits := L.finiteLimits
      colimits := L.finiteColimits }
  have : PreservesFiniteLimits T.functor := T.limits
  exact ⟨⟨T⟩, (CondensedDerivedRestriction.forgetExact A P).1,
    (CondensedDerivedRestriction.forgetExact A P).2.1,
    (CondensedDerivedRestriction.forgetExact A P).2.2,
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      T.adjunction⟩

variable (G H : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- Induction from H to G times H, with the actual relative tensor underneath.
Translation in G and the given H-action, together with the transpose formula,
determine the construction up to its unique generator-preserving isomorphism.
Source: paragraph (3) (blueprint: lem-sfb-condensed-action-injective-restriction). -/
structure ProductTensorInduction where
  functor : ActionModule A.toMon H ⥤ ActionModule A.toMon (G × H)
  additive : functor.Additive
  underlying : functor ⋙ forgetAction ≅ forgetAction ⋙
    tensorLeft (restrictionFree A (Profinite.of G))
  adjunction : functor ⊣ inflate (ContinuousMonoidHom.inr G H)
  action : ∀ (M : ActionModule A.toMon H) (S : Profinite.{u}) (p : C(S, G × H))
    (g : C(S, G)) (m : sectionModule A.toMon M.module S),
    (functor.obj M).act S p
        (onSections A.toMon (underlying.inv.app M) S
          (pureTensor A.toMon _ M.module S
            (restrictionGenerator A (Profinite.of G) S (CompHausLike.ofHom _ g)) m)) =
      onSections A.toMon (underlying.inv.app M) S
        (pureTensor A.toMon _ M.module S
          (restrictionGenerator A (Profinite.of G) S
            (CompHausLike.ofHom _ ((ContinuousMap.fst.comp p) * g)))
          (M.act S (ContinuousMap.snd.comp p) m))
  untranspose : ∀ (M : ActionModule A.toMon H) (X : ActionModule A.toMon (G × H))
    (f : M ⟶ (inflate (ContinuousMonoidHom.inr G H)).obj X)
    (S : Profinite.{u}) (g : C(S, G)) (m : sectionModule A.toMon M.module S),
    onSections A.toMon (((adjunction.homEquiv M X).symm f).val) S
      (onSections A.toMon (underlying.inv.app M) S
        (pureTensor A.toMon _ M.module S
          (restrictionGenerator A (Profinite.of G) S (CompHausLike.ofHom _ g)) m)) =
      X.act S ((ContinuousMonoidHom.inl G H).toContinuousMap.comp g)
        (onSections A.toMon f.val S m)
  limits : PreservesFiniteLimits functor
  colimits : PreservesFiniteColimits functor

/-- Exact product restriction and its normalized exact tensor induction.
Source: paragraph (3), Stacks 03CX and 015Z
(blueprint: lem-sfb-condensed-action-injective-restriction).

Proof:
1. Apply lem-sfb-product-action-exact-forgetting with first group G and retained H.
   Its induction has the required underlying tensor, adjunction and exactness.
2. Decompose a generalized product element into its two projections. Apply the inverse
   underlying comparison to the recorded action formula and cancel the isomorphism.
   The inverse-transpose formula agrees definitionally with the required one.
3. The existing restrictionLimits and restrictionColimits instances give exactness
   of restriction. Both exactness tests, before and after restriction, are equivalent
   by forgetExact to the same underlying module complex, so restriction detects it.
4. The exact induction preserves monomorphisms. Apply the right-adjoint injectivity
   theorem to its adjunction. Trivial factors and the zero ring need no exception.
-/
theorem product_tensor_induction :
    Nonempty (ProductTensorInduction A G H) ∧
    PreservesFiniteLimits (inflate (R := A.toMon) (ContinuousMonoidHom.inr G H)) ∧
    PreservesFiniteColimits (inflate (R := A.toMon) (ContinuousMonoidHom.inr G H)) ∧
    (∀ K : ShortComplex (ActionModule A.toMon (G × H)),
      K.Exact ↔ (K.map (inflate (R := A.toMon) (ContinuousMonoidHom.inr G H))).Exact) ∧
    (inflate (R := A.toMon) (ContinuousMonoidHom.inr G H)).PreservesInjectiveObjects := by
  obtain ⟨D⟩ := ProductForgetting.exists_datum A.toMon G H
    (Or.inl ⟨inferInstance, inferInstance, inferInstance⟩)
  let L := D.induction
  let T : ProductTensorInduction A G H :=
    { functor := L.functor
      additive := L.additive
      underlying := L.tensorIso
      adjunction := L.adjunction
      action := by
        intro M S p g m
        have h := L.action M S (ContinuousMap.fst.comp p) g (ContinuousMap.snd.comp p) m
        have hp : (ContinuousMap.fst.comp p).prodMk (ContinuousMap.snd.comp p) = p := by
          ext s <;> rfl
        rw [hp] at h
        exact (restriction_sections_inv_hom A (L.tensorIso.app M) S _).symm.trans
          (congrArg (onSections A.toMon (L.tensorIso.inv.app M) S) h)
      untranspose := L.untranspose
      limits := L.finiteLimits
      colimits := L.finiteColimits }
  have : PreservesFiniteLimits T.functor := T.limits
  refine ⟨⟨T⟩, inferInstance, inferInstance, ?_,
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      T.adjunction⟩
  intro K
  exact ((CondensedDerivedRestriction.forgetExact A (G × H)).2.2 K).trans
    ((CondensedDerivedRestriction.forgetExact A H).2.2
      (K.map (inflate (R := A.toMon) (ContinuousMonoidHom.inr G H)))).symm

/-- Every equivariant module admits a nonnegative injective resolution; for any such
resolution all four restrictions of each term are injective. The original complex and
its H-invariant complex are K-injective, and the latter represents derived H-invariants.
Source: Stacks 079H, 013K, 013R, 070H and 070I; paragraph (3)
(blueprint: lem-sfb-condensed-action-injective-restriction).

Proof:
1. Grothendieck abelianness from lem-sfb-condensed-product-action-inflation and
   lem-sp-grothendieck-enough-injectives gives enough injectives. Successively embed
   the module and each cokernel into an injective; quotient followed by embedding
   is the next differential (lem-weil-pbc-left-exact-injective-resolution-degree-zero).
2. Forgetting and restriction preserve injectives by the two induction adjunctions.
   H-invariants preserve injectives because their left adjoint is exact projection
   inflation, supplied by lem-sfb-condensed-product-action-inflation. Apply forgetting
   once more to the G-equivariant invariant module to obtain all four assertions.
3. The given complex and its termwise invariant complex vanish in negative degrees
   and have injective terms. Apply lem-weil-pbc-bounded-below-injectives-kinjective.
4. The additive left exact invariants functor has its total right derived functor.
   Apply lem-sp-kinjective-computes to the original equivariant resolution: mapping
   its quasi-isomorphism and inverting the computation unit identifies the invariant
   complex with derived invariants. No quasi-isomorphism from N^H[0] is needed or
   claimed. The same reasoning includes trivial groups, zero modules and the zero ring.
-/
theorem action_injective_restriction (V : ProductInvariants A.toMon G H) :
    (∀ N : ActionModule A.toMon (G × H), Nonempty (InjectiveResolution N)) ∧
    V.functor.PreservesInjectiveObjects ∧
    ∀ (N : ActionModule A.toMon (G × H)) (I : InjectiveResolution N),
      (∀ q : ℤ, Injective (I.cochainComplex.X q).module ∧
        Injective ((inflate (ContinuousMonoidHom.inr G H)).obj (I.cochainComplex.X q)) ∧
        Injective (V.functor.obj (I.cochainComplex.X q)) ∧
        Injective (V.functor.obj (I.cochainComplex.X q)).module) ∧
      I.cochainComplex.IsKInjective ∧
      CochainComplex.IsKInjective
        ((V.functor.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ∧
      Nonempty (V.functor.rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
        DerivedCategory.Q.obj
          ((V.functor.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)) := by
  have : (forgetAction (R := A.toMon) (P := G × H)).PreservesInjectiveObjects :=
    (forget_tensor_induction A (G × H)).2.2.2.2
  have : (forgetAction (R := A.toMon) (P := G)).PreservesInjectiveObjects :=
    (forget_tensor_induction A G).2.2.2.2
  have : (inflate (R := A.toMon)
      (ContinuousMonoidHom.inr G H)).PreservesInjectiveObjects :=
    (product_tensor_induction A G H).2.2.2.2
  have : V.functor.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms V.adjunction
  refine ⟨fun N ↦ ⟨injectiveResolution N⟩, inferInstance, ?_⟩
  intro N I
  have hterm (q : ℤ) : Injective (V.functor.obj (I.cochainComplex.X q)) :=
    V.functor.injective_obj _
  have : ∀ q : ℤ, Injective
      (((V.functor.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).X q) := hterm
  refine ⟨?_, inferInstance, CochainComplex.isKInjective_of_injective _ 0, ?_⟩
  · intro q
    exact ⟨(forgetAction (R := A.toMon) (P := G × H)).injective_obj _,
      (inflate (R := A.toMon) (ContinuousMonoidHom.inr G H)).injective_obj _,
      hterm q, (forgetAction (R := A.toMon) (P := G)).injective_obj _⟩
  · exact ⟨V.functor.rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N ≪≫
        asIso (DerivedCategory.Q.map I.ι')) ≪≫
      V.functor.rightDerivedFunctorObjQIso I.cochainComplex⟩

end Profinite.CondensedAction
