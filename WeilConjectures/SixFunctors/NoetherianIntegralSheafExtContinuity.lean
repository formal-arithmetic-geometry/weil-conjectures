/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleObjects
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.SixFunctors.IntegralExtHomContinuity
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Hom and first Ext continuity for integral constructible sheaves

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-int-compactness/sk-lem-int-ext-continuity.proof.md, degree-zero extraction
of the Noetherian continuity argument
(blueprint: lem-sfb-noetherian-integral-sheaf-ext-continuity).

The source is constructible in the general finite-stratification, locally finitely
presented sense. The targets are arbitrary module sheaves. Both comparisons use
exactly the given colimit cocone; the second uses the derived definition of Ext.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Hom and derived Ext-one out of a constructible integral module commute with small
filtered colimits on a Noetherian scheme, without a base-field hypothesis.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-int-compactness/sk-lem-int-ext-continuity.proof.md; the base-field-free
Noetherian extraction in the DAG node
(blueprint: lem-sfb-noetherian-integral-sheaf-ext-continuity).

Proof:
1. Place `C` in degree zero. It is bounded, its cohomology in degree zero is `C` and
vanishes elsewhere, so `C[0]` is bounded constructible. The predicate comparison
lem-sfb-adic-constructibility-predicate-comparison, for the integral coefficient
certificate, makes `C[0]` constant-model bounded constructible; no coefficient object
or constructibility hypothesis changes.
2. Put `K_i = N_i[0]`; all its terms below degree zero vanish. The base-field-free
Noetherian version `integralExtHomContinuous_of_isNoetherian` of
det-lem-int-ext-continuity (its proof is the locally closed extension tower, costalk
model, integral local lfp continuity and extension closure argument) gives, for every
shift `q`, that the comparison for the termwise colimit cocone of `K` is invertible.
3. The single-complex functor preserves colimits, so the map from `colim K` to
`c.pt[0]` given by the cocone `c` is the unique colimit-vertex isomorphism. By
`colimit.post_desc` the comparison for the mapped cocone of `c` is the comparison of
step 2 followed by the image of this isomorphism; both are invertible. This holds for
every shift and uses exactly the legs `c.ι.app i`.
4. At shift zero remove the zero shift and use the fully faithful additive single
functor (lem-weil-pbc-derived-single-fully-faithful): its natural preadditive-coyoneda
isomorphism transports the derived colimit cocone to the ordinary Hom cocone, and
isomorphisms of functors preserve colimits. At shift one the comparison is the derived
Ext-one map of def-pc-ext as displayed. No stratification of the targets is used.
-/
theorem noetherian_integral_sheaf_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (C : condensedModuleCategory X (Mon.mk (Profinite.padicIntegersRingObj ℓ E)))
    (hC : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ condensedModuleCategory X (Mon.mk (Profinite.padicIntegersRingObj ℓ E)))
    (c : Cocone N) (hc : IsColimit c) :
    IsIso (colimit.desc _ ((preadditiveCoyoneda.obj (Opposite.op C)).mapCocone c)) ∧
      IsIso (colimit.desc _
        ((DerivedCategory.singleFunctor
            (condensedModuleCategory X (Mon.mk (Profinite.padicIntegersRingObj ℓ E))) 0 ⋙
          shiftFunctor _ (1 : ℤ) ⋙ preadditiveCoyoneda.obj
            (Opposite.op ((DerivedCategory.singleFunctor
              (condensedModuleCategory X (Mon.mk (Profinite.padicIntegersRingObj ℓ E)))
              0).obj C))).mapCocone c)) := by
  classical
  let A := condensedModuleCategory X (Mon.mk (Profinite.padicIntegersRingObj ℓ E))
  let S := DerivedCategory.singleFunctor A 0
  have hpred := (adicConstructibilityPredicateComparison ℓ X
    (Profinite.padicIntegersRingObj ℓ E) (.integral E)).2
  have hbound : constantModelBoundedConstructible
      (Profinite.padicIntegersRingObj ℓ E) X (S.obj C) := by
    rw [← hpred]
    exact CondensedRing.boundedConstructible_singleFunctor_obj _ X 0 C hC
  have h (q : ℤ) : IsIso (colimit.desc _
      ((S ⋙ shiftFunctor _ q ⋙ preadditiveCoyoneda.obj
        (Opposite.op (S.obj C))).mapCocone c)) := by
    let S₀ := CochainComplex.singleFunctor A 0
    let K := N ⋙ S₀
    let G := DerivedCategory.Q ⋙ shiftFunctor _ q ⋙
      preadditiveCoyoneda.obj (Opposite.op (S.obj C))
    have hK := CondensedRing.integralExtHomContinuous_of_isNoetherian (E := E)
      X (S.obj C) hbound K 0
      (fun i r hr ↦ HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (N.obj i) r (ne_of_lt hr)) q
    change IsIso (colimit.post K G) at hK
    have : PreservesColimit N S₀ := by
      change PreservesColimit N (HomologicalComplex.single A (.up ℤ) 0)
      infer_instance
    have : IsIso (colimit.desc K (S₀.mapCocone c)) := by
      change IsIso ((colimit.isColimit K).coconePointUniqueUpToIso
        (isColimitOfPreserves S₀ hc)).hom
      infer_instance
    change IsIso (colimit.desc (K ⋙ G) (G.mapCocone (S₀.mapCocone c)))
    rw [← colimit.post_desc]
    infer_instance
  refine ⟨?_, h 1⟩
  let H := preadditiveCoyoneda.obj (Opposite.op (S.obj C))
  let e : preadditiveCoyoneda.obj (Opposite.op C) ≅ S ⋙ shiftFunctor _ (0 : ℤ) ⋙ H :=
    (Functor.FullyFaithful.ofFullyFaithful S).preadditiveCoyonedaObjIso C ≪≫
      (Functor.isoWhiskerLeft S
        (Functor.isoWhiskerRight (shiftFunctorZero _ ℤ) H ≪≫ Functor.leftUnitor H)).symm
  apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
  obtain ⟨hcol⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (h 0)
  exact ⟨IsColimit.mapCoconeEquiv e.symm hcol⟩

end AlgebraicGeometry.ProEtale
