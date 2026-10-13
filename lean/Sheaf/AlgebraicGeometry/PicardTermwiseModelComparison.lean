/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.AlgebraicGeometry.PicardOrdinaryModelCycles
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PicardDerivedModelSections
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf

/-! # Termwise model comparisons before imposing connectivity

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-model-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Termwise tensor pullback of the model transported from the open site.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-picard-termwise-model-comparison) -/
abbrev picardTermwiseModel (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T : Scheme.{v}} (s : T ⟶ U.toScheme) :
    CochainComplex (SheafOfModules.{v} (moduleRings T.toRingedSpace)) ℤ := by
  let : (Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (Modules.tensorPullback s).Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction s)).left_adjoint_additive
  exact ((Modules.tensorPullback s).mapHomologicalComplex (.up ℤ)).obj
    (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)

/-- The degree-zero single of the underived pullback of the source structure sheaf.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-picard-termwise-model-comparison) -/
abbrev picardTermwiseSource {W T : Scheme.{v}} (t : T ⟶ W) :=
  (CochainComplex.singleFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
      ((Modules.tensorPullback t).obj (SheafOfModules.unit (moduleRings W.toRingedSpace)))

/-- Source and target object comparisons can be chosen simultaneously, so that
restriction of a localized chain map is represented by a chain map whose zeroth
component is ordinary tensor restriction. No connectivity is assumed: this theorem
computes objects and the restriction of already given chain maps, not all derived
morphisms. The degree-zero source identification is included explicitly.
Source: Stacks Project, Tags 06YJ and 0D5S; open restriction via Tag 08DW.
(blueprint: lem-sc-picard-termwise-model-comparison)

Proof:
1. Choose the given model isomorphism once. Transport K along Modules.overEquiv U.
   The equivalence preserves finite-free retracts and zero terms. Each transported
   term is therefore flat and the transported complex is bounded above. The K-flat
   counit computes its pullback along every s by the termwise tensor complex P_s.
   Identify restriction of E to U with its derived open pullback using
   Modules.overFunctorEquiv and the exact open-site equivalence, then use the
   canonical derived composition isomorphism and the factorization s;U.ι=t.
   This gives b. Apply the same counit to the single structure sheaf and the
   single-mapHomologicalComplex comparison to get a (retaining the tensor-pulled
   unit as source, rather than changing it by an arbitrary unit isomorphism).
2. For a chain map f from the source single to P_s, termwise pull it back along i.
   Conjugate by the single-complex comparison and the underived composition
   comparisons for t and s, including the given equalities ht and hs. This is f'.
   In degree zero the single comparison cancels against singleObjXSelf; the
   resulting component is exactly picardOrdinaryModelRestriction of the component
   of f. All other degrees of its source are zero; the chain-map condition is
   preserved by the additive pullback functor and the comparison isomorphisms.
3. The derived composition map is the left-derived lift of the very same
   underived composition comparisons and counits. Evaluate its defining counit
   equation on the bounded K-flat model and on the single unit, where the counits
   are invertible. Naturality of the counits for f then gives the displayed
   restriction equation. Naturality of the fixed model isomorphism under further
   pullback cancels it on both sides. Equality transports ht, hs and the two
   factorizations commute by proof irrelevance. No assumption on negative terms
   is used; zero complexes and empty schemes are preserved by these functors. -/
theorem picard_termwise_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ (a : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        (derivedPullback t).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
          DerivedCategory.Q.obj (picardTermwiseSource t))
      (b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t →
          ((derivedPullback t).obj E ≅
            DerivedCategory.Q.obj (picardTermwiseModel W U K s))),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
        (ht : i ≫ t = t') (hs : i ≫ s = s')
        (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t')
        (f : picardTermwiseSource t ⟶ picardTermwiseModel W U K s),
      ∃ f' : picardTermwiseSource t' ⟶ picardTermwiseModel W U K s',
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ f'.f 0 =
          picardOrdinaryModelRestriction W U K i t t' s s' ht hs
            ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ f.f 0) ∧
        picardDerivedModelRestriction E i t t' ht
            ((a t).hom ≫ DerivedCategory.Q.map f ≫ (b t s hf).inv) =
          (a t').hom ≫ DerivedCategory.Q.map f' ≫ (b t' s' hf').inv := by sorry

end
end AlgebraicGeometry.Scheme
