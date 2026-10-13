/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Specified affine perfect models and base-change comparison
Source: Stacks Project, perfect.tex, Tag 09RE, Tags 08EB, 06Z0 and 08DW.
(blueprint: lem-pc-affine-specified-model-chain-comparison).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Base-change comparison from genuine affine perfect models.
Source: Stacks Project, perfect.tex, lemma-descend-homomorphisms, Tag 09RE;
Tags 06Z0 and 08DW.
(blueprint: lem-pc-affine-specified-model-chain-comparison).

Proof: Let B be the ring of global sections of Y, and give B its R(i)-algebra
structure via s. On the tail form F(j) = B tensor over R(i) with R(j).
Extension of scalars preserves the colimit, so its colimit is B tensor over
R(i) with c.pt. The map r : B to F(i) is an isomorphism. Tensor and pullback
universal properties identify their spectra with the prescribed pullbacks.
The isomorphism t identifies Spec B with Y. Use the composite of t.hom
with s to give B its R(i)-algebra structure. The factorization he identifies
e with exact pushforward along t.hom. The
isomorphisms hPE and hQK therefore identify the two specified tilde complexes
with P and Q. Extend E₀ and K₀ along r to obtain E and K. Extension of scalars
preserves degreewise zero objects, finite generation and projectivity, giving
both bounded finite-projective conditions. Their projective terms are flat,
and bounded flat complexes are K-flat, so the natural affine tilde/pullback
comparison computes all pullbacks by termwise scalar extension. Compose the
fully faithful affine quasi-coherent derived equivalence with scheme-isomorphism
transport and conjugate by the specified object isomorphisms. This gives stage
and limit Hom equivalences. On chain maps, naturality of tilde base change
identifies scalar extension with pullback. Tensor associativity and the fixed
counit-pinned derived composition comparison identify the conjugations with
perfectStageMap and perfectLimitMap, proving the two equations. The argument
uses neither morphism descent nor homotopy descent. It applies to zero rings
and empty spectra, because the tensor and pullback universal properties and
the affine equivalence do; the tail has its initial object i. -/
theorem exists_affineSpecifiedModelChainComparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (t : Spec (Scheme.Γ.obj (.op Y)) ≅ Y)
    (e : schemeDerivedCategory (Spec (Scheme.Γ.obj (.op Y))) ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward t.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (P Q : schemeDerivedCategory Y)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (Scheme.Γ.obj (.op Y))) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (Scheme.Γ.obj (.op Y)) (E₀.X n) ∧
        Module.Projective (Scheme.Γ.obj (.op Y)) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (Scheme.Γ.obj (.op Y)) (K₀.X n) ∧
        Module.Projective (Scheme.Γ.obj (.op Y)) (K₀.X n))
    (hPE : e.inverse.obj P ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (tilde.functor (Scheme.Γ.obj (.op Y)))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E₀))
    (hQK : e.inverse.obj Q ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (tilde.functor (Scheme.Γ.obj (.op Y)))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K₀)) :
    ∃ (F : Set.Ici i ⥤ CommRingCat.{u})
      (r : Scheme.Γ.obj (.op Y) →+* F.obj ⟨i, le_rfl⟩),
      let E := ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E₀
      let K := ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj K₀
      ((∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
        ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (E.X n) ∧
          Module.Projective (F.obj ⟨i, le_rfl⟩) (E.X n)) ∧
      ((∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
        ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (K.X n) ∧
          Module.Projective (F.obj ⟨i, le_rfl⟩) (K.X n)) ∧
      ∃ (stage : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)) ≃
          ((derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj P ⟶
           (derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj Q))
        (limit :
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj K)) ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          stage k (DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
              (F.map (homOfLE k.property)).hom
              (congrArg CommRingCat.Hom.hom (F.map_comp
                (homOfLE j.property) (homOfLE hjk))) E K f)) =
            perfectStageMap R s j.val.property hjk
              (stage j (DerivedCategory.Q.map f))) ∧
        (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          limit (DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
              (colimit.ι F ⟨i, le_rfl⟩).hom
              (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm)
              E K f)) =
            perfectLimitMap R c s j.val.property
              (stage j (DerivedCategory.Q.map f))) := by
  sorry

end AlgebraicGeometry
