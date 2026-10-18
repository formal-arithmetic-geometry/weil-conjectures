/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.Thickening
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.GenericResidueFieldAffineLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent
import Sheaf.AlgebraicGeometry.EventuallyProper
import Sheaf.AlgebraicGeometry.DescendClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.DescendSmoothQcqs
import Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent
import Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous
import Sheaf.AlgebraicGeometry.ProperSmoothGeometricComponentsLocallyConstant
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import Sheaf.AlgebraicGeometry.FiniteRadicialAffineShrinking

/-! # Spreading a prescribed generic curve completion

Source: Stacks Project, More on Morphisms, Tag 0GK7, descent and thickening paragraphs.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Spread a componentwise generic normalization with smooth projective completions
over a finite radicial residue-field model, retaining a fibrewise nonempty thickening locus.
Source: Stacks Project, More on Morphisms, Tag 0GK7, the paragraphs beginning
"Thus we may assume S is affine, reduced" and "It remains to prove the existence".
(blueprint: lem-weil-pbc-good-curves-spread-generic-completion)

Proof: The reduced affine model V₀ has local ring equal to its residue field at η₀.
Use e to view the prescribed K-diagram as a diagram over that generic field. Its
isomorphism with the generic fibre of X follows from the compatibility equation he
and the two fibre-product projections. The proved theorem
`generic_residue_field_affine_limit` identifies its spectrum with the limit of affine
neighbourhoods of η₀. Descend all finitely presented objects, arrows and commutativity
equations to a common affine neighbourhood in that cofiltered system.
Keep X with its given model. All models are qcqs and the arrows are locally finitely
presented, by finite presentation over a finite-type intermediate algebra. Descend
finiteness and surjectivity of the normalization map, finite étaleness of the constant
field models, open immersions of the curve opens, smoothness and surjectivity of those
opens, and proper smoothness of their completions. Common later stages work for all
finitely many morphisms. Geometric connectedness spreads by local constancy of proper
smooth geometric component count, and dimension at most one spreads by upper
semicontinuity for proper fibres. Remove the finite images of the bad closed sets.
The prescribed generic normalization is finite and surjective and agrees, over a dense
qc normal subopen, with the reduction closed immersion. Descend this qc open and the
closed-immersion property there. Surjectivity gives a thickening. Its inverse image
meets every generic normalization component. Smoothness makes each such open image
in T_i open. Remove the finite images of their closed complements, so each restricted
open meets every Y_i → T_i fibre. Every shrinking of V₀ can be effected on U₀ by
removing the closed image of its closed complement, using
`exists_affine_shrinking_under_finite_radicial`; choose a principal refinement and
base change all objects. The restricted cover remains finite, surjective and radicial.
For the empty family the finite surjection from its empty coproduct forces the family
X to be empty at the chosen stage, and the empty open has the required properties. -/
theorem exists_good_curves_spread_generic_completion
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (K : Type u) [Field K] [Algebra (S.residueField η) K]
    (U₀ : S.Opens) (hηU₀ : η ∈ U₀) (V₀ : Scheme.{u}) (g₀ : V₀ ⟶ U₀.toScheme)
    [IsAffine U₀.toScheme] [IsAffine V₀] [IsReduced V₀]
    [IsFinite g₀] [Surjective g₀] [UniversallyInjective g₀]
    (η₀ : V₀) (hq : (g₀ ≫ U₀.ι) η₀ = η)
    (hη₀ : ∃ Z ∈ irreducibleComponents V₀, IsGenericPoint η₀ Z)
    (e : V₀.residueField η₀ ≃+* K)
    (he : e.toRingHom.comp
      (((S.residueFieldCongr hq).inv ≫ (g₀ ≫ U₀.ι).residueFieldMap η₀).hom) =
        algebraMap (S.residueField η) K)
    (hcurves :
      ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (hC : ∀ i, IsIntegral (C i))
        (c : ∀ i, C i ⟶ pullback (f.fiberToSpecResidueField η)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))))
        (Y B : Fin n → Scheme.{u})
        (e : ∀ i, Y i ≅ @Scheme.normalization (C i) (hC i))
        (j : ∀ i, Y i ⟶ B i)
        (L : Fin n → Type u) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i))
        (q : ∀ i, B i ⟶ Spec (.of (L i)))
        (p : ∀ i, Y i ⟶ Spec (.of K))
        (ν : (∐ Y) ⟶ pullback (f.fiberToSpecResidueField η)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K)))),
        (∀ i, IsClosedImmersion (c i) ∧
          Set.range (c i) ∈ irreducibleComponents
            (pullback (f.fiberToSpecResidueField η)
              (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))) : Scheme.{u})) ∧
        Function.Injective (fun i ↦ Set.range (c i)) ∧
        (∀ Z ∈ irreducibleComponents
          (pullback (f.fiberToSpecResidueField η)
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))) : Scheme.{u}),
          ∃ i, Set.range (c i) = Z) ∧
        ν = Sigma.desc (fun i ↦ (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i) ∧
        (∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) ∧
          IsOpenImmersion (j i) ∧ DenseRange (j i) ∧ Nonempty (Y i) ∧
          Smooth (q i) ∧ IsHProjective (q i) ∧ GeometricallyIrreducible (q i) ∧
          topologicalKrullDim (B i) ≤ 1 ∧
          (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i ≫
            pullback.snd (f.fiberToSpecResidueField η)
              (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))) = p i ∧
          j i ≫ q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))) = p i ∧
          LocallyOfFinitePresentation (p i) ∧ QuasiCompact (p i) ∧ QuasiSeparated (p i) ∧
          LocallyOfFinitePresentation
            (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiCompact (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiSeparated (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap K (L i))))) ∧
        LocallyOfFinitePresentation (Sigma.desc p) ∧
        QuasiCompact (Sigma.desc p) ∧ QuasiSeparated (Sigma.desc p) ∧
        LocallyOfFinitePresentation (pullback.snd (f.fiberToSpecResidueField η)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K)))) ∧
        QuasiCompact (pullback.snd (f.fiberToSpecResidueField η)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K)))) ∧
        QuasiSeparated (pullback.snd (f.fiberToSpecResidueField η)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K)))) ∧
        (n = 0 ↔ IsEmpty (f.fiber η))) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i) ∧
          ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1) ∧
        ∃ W : (pullback f (g ≫ U.ι)).Opens,
          (∀ (i : Fin n) (s : T i),
            ∃ y : (j i ≫ p i).fiber s,
              ((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) y ∈ W) ∧
          IsThickening (pullback.snd ν W.ι) := by
  sorry

end AlgebraicGeometry
