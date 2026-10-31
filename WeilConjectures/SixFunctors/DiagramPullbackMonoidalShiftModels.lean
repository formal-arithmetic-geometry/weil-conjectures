/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.DiagramPullbackShiftData
import WeilConjectures.SixFunctors.DiagramTensorShiftConstraints
import WeilConjectures.SixFunctors.DiagramGeometricTensorPresentations
import WeilConjectures.SixFunctors.DiagramTensorPullbackShiftDescent
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Simultaneous pullback, tensor and shift models on strict systems

Source: Stacks 06YS, 07A4, 0FPQ and 0FPT; More on Algebra 0FNH.
(blueprint: lem-pur-diagram-pullback-monoidal-shift-models). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  SheafOfModules.KFlatFixedTensor.representativeIso
  CategoryTheory.Functor.mapDerivedCategory
  HomologicalComplex₂.total

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open SheafOfModules.DerivedTensorConstraints

namespace WeilConjectures.DiagramPullbackShift

variable (A : ℕ → CommRingCat.{u + 1}) (δ : ∀ n : ℕ, A (n + 1) ⟶ A n)

private theorem unitModels (W : Scheme.{u}) : ChainUnitCoherence A δ W := by
  let := SheafOfModules.monoidalCategory (ring A δ W)
  let := complexMonoidal (ring A δ W)
  let := complexMonoidalStruct (ring A δ W)
  change ∀ (E : Complex A δ W) (p : ℤ),
    HomologicalComplex.ιTensorObj
        (HomologicalComplex.tensorUnit (Modules A δ W) (.up ℤ)) E 0 p p (zero_add p) ≫
        (λ_ E).hom.f p =
      ((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (𝟙_ (Modules A δ W))).hom ▷ E.X p) ≫ (λ_ (E.X p)).hom ∧
    HomologicalComplex.ιTensorObj E
        (HomologicalComplex.tensorUnit (Modules A δ W) (.up ℤ)) p 0 p (add_zero p) ≫
        (ρ_ E).hom.f p =
      (E.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (𝟙_ (Modules A δ W))).hom) ≫ (ρ_ (E.X p)).hom
  intro E p
  constructor
  · have hi := HomologicalComplex.leftUnitor'_inv E p
    change (λ_ E).inv.f p = _ at hi
    apply (cancel_epi ((λ_ (E.X p)).inv ≫
      ((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
        (𝟙_ (Modules A δ W))).inv ▷ E.X p))).1
    calc
      _ = (λ_ E).inv.f p ≫ (λ_ E).hom.f p := by
        rw [hi]
        simp only [Category.assoc]
      _ = 𝟙 _ := by
        rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
      _ = _ := by
        simp only [Category.assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
          Iso.inv_hom_id, MonoidalCategory.id_whiskerRight, Category.id_comp,
          Iso.inv_hom_id]
  · have hi := HomologicalComplex.rightUnitor'_inv E p
    change (ρ_ E).inv.f p = _ at hi
    apply (cancel_epi ((ρ_ (E.X p)).inv ≫
      (E.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
        (𝟙_ (Modules A δ W))).inv))).1
    calc
      _ = (ρ_ E).inv.f p ≫ (ρ_ E).hom.f p := by
        rw [hi]
        simp only [Category.assoc]
      _ = 𝟙 _ := by
        rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
      _ = _ := by
        simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
          Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
          Iso.inv_hom_id]

private theorem simultaneousResolutions (W : Scheme.{u}) (n : ℕ)
    (E : Fin n → Complex A δ W) :
    ∃ (P : Fin n → Model (ring A δ W)) (q : ∀ i : Fin n, (P i).obj ⟶ E i),
      ∀ i : Fin n, QuasiIso (q i) := by
  classical
  have h (i : Fin n) : ∃ (P : Model (ring A δ W)) (q : P.obj ⟶ E i), QuasiIso q := by
    obtain ⟨K, q, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (E i)
    have hflat : ∀ p : ℤ,
        SheafOfModules.IsFlatOnSite
          (J := coefficientSequenceTopology (ProEt.topology W)) (R := ring A δ W) (K.X p) := by
      intro p
      unfold SheafOfModules.IsFlatOnSite
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (ring A δ W) (K.X p)).symm (hf p)
    exact ⟨⟨K, hk, hflat⟩, q, hq⟩
  choose P q hq using h
  exact ⟨P, q, hq⟩

private theorem signedModels (W : Scheme.{u}) : ChainSignedCoherence A δ W := by
  exact CategoryTheory.RingedDerivedNative.totalTensor_signed_coherence.{u + 1, u, u + 1}
    (coefficientSequenceTopology (ProEt.topology W)) (ring A δ W)

private theorem compositorModels (S : Models A δ) : S.CompositorModels A δ := by
  intro X Y Z v w E r p
  exact ⟨HEq.rfl, HEq.rfl⟩

private theorem compositorShifts (S : Models A δ) : S.CompositorShifts A δ := by
  intro X Y Z v w
  unfold Models.compositor
  simp only [Iso.trans_hom, Iso.trans_inv]
  exact ⟨inferInstance, inferInstance⟩

private theorem equalityShifts (S : Models A δ) : S.EqualityShifts A δ := by
  intro X Y v w e
  subst w
  constructor
  · intro E r p
    rfl
  · intro M r
    simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp]
    rw [CategoryTheory.Functor.map_id]
    exact (CategoryTheory.Category.comp_id _).symm

/-- The specified comparisons admit simultaneous resolving representatives and descend
with all slotwise shift squares, intrinsically in the ordinary derived system category.
Source: blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
maps-used sentence; Stacks 06YS, 0G7E, 07A4, 0FPQ, 0FPT; More on Algebra 0FNH
(blueprint: lem-pur-diagram-pullback-monoidal-shift-models).

Proof:
1. By lem-coef-semilinear-derived-sections use modules on the entire ringed sequence
site. Apply lem-pc-kflat-resolution there to all finitely many inputs. By
lem-weil-pbc-ringed-topoi-derived-tensor-pullback exact inverse image preserves
flat-term K-flat models. The totalModel and shiftModel of
lem-pur-derived-tensor-additive-constraints close this class under tensor and shifts;
the degree-zero ring unit is resolving. These give the same models at all vertices.
2. For the canonical ordinary compositor, termwise application at E[r] in degree p
is its component at E^(p+r). Naturality with the actual semilinear transitions and
with d_E proves its system and chain equations, also after multiplying d_E by
(-1)^r. The same applies to identifications of equal scheme composites. Inversion
gives the opposite squares. Localize using the shift-compatible exact factorization
of lem-weil-pbc-exact-functor-derived-factorization.
3. Use the total of the normalized ordinary pure-tensor comparison from
lem-pur-cochain-pullback-tensor-coherence. It preserves both bidegrees. Naturality
with a coefficient transition f, g gives the same reduced tensor, since
f(cx)=c-bar f(x) and g(cy)=c-bar g(y); thus balancing and every transition commute.
Both shifted routes have coefficient (-1)^(bp), by
lem-weil-pbc-total-tensor-integer-shifts. Additivity and the direct-sum universal
property extend these identities to the total chain maps.
4. By lem-pur-total-tensor-signed-coherence, unsigned reassociation gives exponents
bp+c(p+q) and cq+(b+c)p, equal as integers. The degree-zero ring in an action unitor
gives coefficient one. These prove all three associator and both unitor squares.
5. Symmetry gives bp+(p+a)(q+b) and ab+pq+aq; their difference is 2bp, for all
integers including negative shifts. The resulting identity includes (-1)^(ab).
Set one shift to zero to follow each single shifted occurrence to its permuted
slot. Integer-shift zero/addition and interchange laws give shift_laws and extraction;
naturality follows because every chain map preserves degree.
6. Insert the existing representative comparisons and exact-pullback factorization.
Their localizations are precisely the specified tensor, compositor and constraint
maps by their normalizations. Fully faithful restriction on every finite tuple in
lem-pur-derived-tensor-additive-constraints descends the chain equalities uniquely.
All calculations take place on the whole system site, including quotient transitions
A_n=R/t^n. Neither normalized-system nor boundedness assumptions are used. -/
theorem diagramPullbackMonoidalShiftModels :
    ∃ S : Models A δ, S.Coherence A δ := by
  classical
  choose T hT using diagramTensorShiftConstraints A δ
  obtain ⟨S, hS⟩ := diagramGeometricTensorPresentations A δ T
  refine ⟨S, ?_⟩
  refine
    { resolutions := simultaneousResolutions A δ
      chain_signed := signedModels A δ
      chain_unit := unitModels A δ
      tensor_shifts := ?_
      chain_pullback := ?_
      derived_pullback := ?_
      compositor_models := compositorModels A δ S
      compositor_shifts := compositorShifts A δ S
      equality_shifts := equalityShifts A δ S }
  · intro W
    rw [hS]
    exact hT W
  · intro X Y v
    exact (diagramTensorPullbackShiftDescent A δ (S.inverseImage v)
      (S.tensorPullback v) (S.constraints Y) (S.constraints X)).1
  · intro X Y v
    exact (diagramTensorPullbackShiftDescent A δ (S.inverseImage v)
      (S.tensorPullback v) (S.constraints Y) (S.constraints X)).2

end WeilConjectures.DiagramPullbackShift
