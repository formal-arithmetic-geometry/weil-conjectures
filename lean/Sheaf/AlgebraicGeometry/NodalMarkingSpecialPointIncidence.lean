/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Special-point incidence on a nodal curve after extension of closed fields

Source: Stacks Project, Curves, Tags 0C59 and 0C5B; Morphisms, Tag 02G7;
Schemes, Tag 0356 and the fibre-product universal property.
(blueprint: lem-trf-nodal-marking-special-point-incidence).

The scalar-extended marking and singular subscheme below are actual fibre products.
The final cardinalities count points on a component, including a self-node only once.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The inclusion of the scalar extension of a closed subscheme into the scalar
extension of its ambient scheme, formed using the canonical fibre-product map.
Source: Stacks Project, Schemes, Section 26.17; Morphisms, Tag 01QR.
(blueprint: lem-trf-nodal-marking-special-point-incidence). -/
def nodalMarkingScalarInclusion {C F S T : Scheme.{u}} (f : C ⟶ S)
    (g : T ⟶ S) (i : F ⟶ C) :
    pullback (C := Scheme.{u}) (i ≫ f) g ⟶ pullback (C := Scheme.{u}) f g :=
  pullback.map (i ≫ f) g f g i (𝟙 T) (𝟙 S)
    (Category.comp_id (i ≫ f))
    ((Category.comp_id g).trans (Category.id_comp g).symm)

/-- Markings and first-Fitting singular points of a finite-type nodal curve over
an algebraically closed field are finite unions of rational points. Scalar extension
replaces each summand by one rational point, preserves the nonsmooth support, and
preserves incidence and the number of distinct special points on reduced components.
No properness or separatedness assumption is made; empty schemes and markings are allowed.

Source: Stacks Project, Curves, Tags 0C59 and 0C5B; Morphisms, Tag 02G7;
Schemes, Tag 0356 and the fibre-product universal property.
(blueprint: lem-trf-nodal-marking-special-point-incidence).

Proof plan, following the six DAG steps:
1. For empty C everything is empty. Otherwise use lem-pc-flat-field and
   pqf-lem-lft-fp-locnoeth over the Noetherian field k, then
   lem-trf-chosen-nodal-fibres-universal to pass the completed-local-ring and
   pure-dimension hypotheses to every algebraically closed geometric fibre.
2. Apply lem-trf-nodal-family-fitting-singular: the actual first-Fitting subscheme
   is unramified, its support is the nonsmooth locus, and this remains true after
   arbitrary base change. No reduction of the singular subscheme is taken.
3. Apply lem-trf-unramified-field-fibre-decomposition to F and Z. By
   lem-weil-pbc-alg-closed-finite-extension-trivial every field summand is k.
   They are quasi-compact closed subschemes of the finite-type curve, so the
   singleton open cover has a finite subcover. Smoothness of the marking makes
   its image disjoint from the singular image.
4. Apply lem-weil-pbc-sets-etale-inverse-image-constant-base-change to the finite
   coproducts. Every summand becomes Spec L compatibly with projection. By
   lem-weil-pbc-closed-immersion-base-change the inclusions remain closed, so
   the projection gives a bijection of the unions of their point sets.
5. If a special point lies on R, its rational summand morphism factors through
   R by lem-weil-pbc-field-point-factors-through-closed-immersion. The fibre-product
   universal property gives its unique scalar-extended point on R_L. Conversely
   a point on R_L projects to a point on R.
6. Restrict the finite bijection to the intersections with R and R_L and take
   cardinalities. These are underlying point sets, so self-nodes count once;
   empty intersections have cardinality zero. No branch or normalization is used.
-/
theorem nodal_marking_special_point_incidence
    (k L : Type u) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L]
    (φ : k →+* L) {C F : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hpure : C.IsPureDimension 1)
    (hnodal : ∀ x : C, ¬ (f.stalkMap x).hom.FormallySmooth →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
            (C.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) :
              MvPowerSeries (Fin 2) k)})))
    (i : F ⟶ C) [IsClosedImmersion i] [Etale (i ≫ f)]
    (hmark : ∀ x : F, (f.stalkMap (i x)).hom.FormallySmooth) :
    (∃ (nF nZ : ℕ)
      (eF : (∐ fun _ : Fin nF ↦ Spec (.of k)) ≅ F)
      (eZ : (∐ fun _ : Fin nZ ↦ Spec (.of k)) ≅
        (Scheme.firstFittingIdealSheaf f).subscheme)
      (eFL : (∐ fun _ : Fin nF ↦ Spec (.of L)) ≅
        pullback (C := Scheme.{u}) (i ≫ f) (Spec.map (CommRingCat.ofHom φ)))
      (eZL : (∐ fun _ : Fin nZ ↦ Spec (.of L)) ≅
        pullback (C := Scheme.{u}) (Scheme.firstFittingSingularSubscheme f ≫ f)
          (Spec.map (CommRingCat.ofHom φ))),
      eF.hom ≫ i ≫ f = Sigma.desc (fun _ : Fin nF ↦ 𝟙 (Spec (.of k))) ∧
      eZ.hom ≫ Scheme.firstFittingSingularSubscheme f ≫ f =
        Sigma.desc (fun _ : Fin nZ ↦ 𝟙 (Spec (.of k))) ∧
      eFL.hom ≫ pullback.snd (i ≫ f) (Spec.map (CommRingCat.ofHom φ)) =
        Sigma.desc (fun _ : Fin nF ↦ 𝟙 (Spec (.of L))) ∧
      eZL.hom ≫ pullback.snd (Scheme.firstFittingSingularSubscheme f ≫ f)
          (Spec.map (CommRingCat.ofHom φ)) = Sigma.desc (fun _ : Fin nZ ↦ 𝟙 (Spec (.of L))) ∧
      (∀ a : Fin nF,
        Sigma.ι (fun _ : Fin nF ↦ Spec (.of L)) a ≫ eFL.hom ≫
            pullback.fst (i ≫ f) (Spec.map (CommRingCat.ofHom φ)) =
          Spec.map (CommRingCat.ofHom φ) ≫ Sigma.ι (fun _ : Fin nF ↦ Spec (.of k)) a ≫ eF.hom) ∧
      (∀ a : Fin nZ,
        Sigma.ι (fun _ : Fin nZ ↦ Spec (.of L)) a ≫ eZL.hom ≫
            pullback.fst (Scheme.firstFittingSingularSubscheme f ≫ f)
              (Spec.map (CommRingCat.ofHom φ)) =
          Spec.map (CommRingCat.ofHom φ) ≫ Sigma.ι (fun _ : Fin nZ ↦ Spec (.of k)) a ≫ eZ.hom)) ∧
    Disjoint (Set.range i) (Set.range (Scheme.firstFittingSingularSubscheme f)) ∧
    Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ))
        (Scheme.firstFittingSingularSubscheme f)) =
      {x | ¬ ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).stalkMap x).hom.FormallySmooth} ∧
    Set.BijOn (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))
      (Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ)) i) ∪
        Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ))
          (Scheme.firstFittingSingularSubscheme f)))
      (Set.range i ∪ Set.range (Scheme.firstFittingSingularSubscheme f)) ∧
    (∀ (R : Scheme.{u}) (r : R ⟶ C) [IsClosedImmersion r] [IsReduced R],
      Set.range r ∈ irreducibleComponents C →
      IsReduced (pullback (C := Scheme.{u}) (r ≫ f) (Spec.map (CommRingCat.ofHom φ))) →
      Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ)) r) ∈
        irreducibleComponents (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom φ))) →
      (∀ aL : pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom φ)),
        aL ∈ Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ)) i) ∪
          Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ))
            (Scheme.firstFittingSingularSubscheme f)) →
        (pullback.fst f (Spec.map (CommRingCat.ofHom φ)) aL ∈ Set.range r ↔
          aL ∈ Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ)) r))) ∧
      Nat.card ↥(Set.range r ∩
          (Set.range i ∪ Set.range (Scheme.firstFittingSingularSubscheme f))) =
        Nat.card ↥(Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ)) r) ∩
          (Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ)) i) ∪
            Set.range (nodalMarkingScalarInclusion f (Spec.map (CommRingCat.ofHom φ))
              (Scheme.firstFittingSingularSubscheme f))))) := by
  sorry

end AlgebraicGeometry
