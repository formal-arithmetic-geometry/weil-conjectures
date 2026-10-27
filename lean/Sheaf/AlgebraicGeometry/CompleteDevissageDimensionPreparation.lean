/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.TraceFormula.CompleteAlgebraDevissage
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.PointCount
import Mathlib.RingTheory.FiniteStability
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg

/-!
# Finite presentation and fibre dimensions of a complete algebraic dévissage

Source: Stacks Project, Tags 05HX, 05HY, 02G1, 02G2 and 0A21
(blueprint: lem-sfb-complete-devissage-fp-dimension-preparation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The canonical localized algebra, written as extension of scalars.
Source: Stacks Project, Tags 05HX and 05HJ
(blueprint: lem-sfb-complete-devissage-fp-dimension-preparation). -/
abbrev completeDevissageLocalizedAlgebra {R : Type u} [CommRing R]
    (f : R) (C : CommAlgCat.{u} R) : CommAlgCat.{u} (Localization.Away f) :=
  CommAlgCat.of (Localization.Away f) (Localization.Away f ⊗[R] C)

/-- The canonical localized module over the canonical localized algebra.
Source: Stacks Project, Tags 05HX and 05HJ
(blueprint: lem-sfb-complete-devissage-fp-dimension-preparation).
Extension along the right tensor inclusion is canonically the fraction module at `f`. -/
noncomputable def completeDevissageLocalizedModule {R : Type u} [CommRing R]
    (f : R) (C : CommAlgCat.{u} R) (M : ModuleCat.{v} C) :
    ModuleCat.{max u v} (completeDevissageLocalizedAlgebra f C) :=
  (ModuleCat.extendScalars (Algebra.TensorProduct.includeRight :
    C →ₐ[R] Localization.Away f ⊗[R] C).toRingHom).obj M

/-- The canonical map from a module to its localization.
Source: Stacks Project, Tags 05HX and 05HJ
(blueprint: lem-sfb-complete-devissage-fp-dimension-preparation). -/
noncomputable def completeDevissageLocalizedUnit {R : Type u} [CommRing R]
    (f : R) (C : CommAlgCat.{u} R) (M : ModuleCat.{v} C) (m : M) :
    completeDevissageLocalizedModule f C M :=
  TensorProduct.tmul C (1 : Localization.Away f ⊗[R] C) m

/-- The structure morphism of a canonically localized dévissage algebra.
Source: Stacks Project, Tags 05HX and 02G2
(blueprint: lem-sfb-complete-devissage-fp-dimension-preparation). -/
noncomputable def completeDevissageLocalizedSpecMap {R : Type u} [CommRing R]
    (f : R) (C : CommAlgCat.{u} R) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (Localization.Away f) (completeDevissageLocalizedAlgebra f C)))

/-- A fibre after arbitrary scheme base change of the canonical localized algebra.
Source: Stacks Project, Tags 02FY and 0A21
(blueprint: lem-sfb-complete-devissage-fp-dimension-preparation). -/
noncomputable abbrev completeDevissageBaseChangeFibre {R : Type u} [CommRing R]
    (f : R) (C : CommAlgCat.{u} R) {T : Scheme.{u}}
    (g : T ⟶ Spec (.of (Localization.Away f))) (t : T) :=
  (pullback.snd (completeDevissageLocalizedSpecMap f C) g).fiber t

/-- The map of this fibre to the spectrum of the base point's residue field.
Source: Stacks Project, Tags 02FY and 0A21
(blueprint: lem-sfb-complete-devissage-fp-dimension-preparation). -/
noncomputable abbrev completeDevissageBaseChangeFibreMap {R : Type u} [CommRing R]
    (f : R) (C : CommAlgCat.{u} R) {T : Scheme.{u}}
    (g : T ⟶ Spec (.of (Localization.Away f))) (t : T) :=
  (pullback.snd (completeDevissageLocalizedSpecMap f C) g).fiberToSpecResidueField t

/-- Finite presentation and dimension preparation for a fixed complete dévissage.

Source: Stacks Project, Tags 05HY, 05HX, 02G1, 02G2, 01VF and 0A21
(blueprint: lem-sfb-complete-devissage-fp-dimension-preparation).

Proof plan:
1. For length zero take f = 1; every indexed conclusion is empty. Otherwise smoothness
   gives flatness and finite presentation of each B_i over R, using
   lem-pc-smooth-flat and lem-weil-pbc-lfp-affine-opens-finite-presentation.
   Compose presentations to obtain finite presentation of A_i over R.
2. Apply lem-weil-pbc-finite-presentation-over-finite-type-algebra to B_i -> A_i;
   the other displayed maps are already finitely presented by the dévissage definition.
3. A finite presentation of a module, augmented by lifts of the finitely many images
   of a finite free basis, presents the quotient by that image.
4. Induct using lem-trf-finite-extension-module-finite-presentation, first on N and
   then on the successive cokernels, to obtain the three module conclusions.
5. By sbc-lem-smooth-relative-dimension-locally-constant, local fibre dimension is
   locally constant. Each fibre is irreducible, hence it has a single dimension value.
   Let a_i be that value on the nonempty fibre over p.
6. The image of the open locus of dimension a_i is open by lem-weil-pbc-flat-lfp-open.
   Constancy within fibres shows this is a saturated locus. Intersect these finitely
   many images and choose a principal neighbourhood D(f) of p inside it.
7. Identify this neighbourhood with Spec R_f by
   lem-weil-pbc-localization-spectrum-embedding. Tensor-localization identifies the
   localized algebra with (B_i)_f and its fibres with the original fibres.
   Smoothness survives by lem-pc-proper-base-change; affine smooth maps are flat
   and of finite presentation by lem-pc-smooth-flat and affine-morphism permanence.
8. Localize every ring, module and displayed map. Finiteness and presentation persist;
   lem-weil-pbc-localization-module-exact identifies the successive cokernels.
   The original first and cokernel identifications localize as well.
9. The extended prime p B_i does not contain f, since the fibre over p is nonempty.
   Apply lem-weil-pbc-localization-prime-residue-field-iso to identify its localized
   residue field and retain bijectivity of alpha_i on that field. This verifies all
   eight conditions of def-trf-complete-algebra-devissage for the localized data.
10. Smooth geometrically irreducible fibres are geometrically integral by
    lem-trf-smooth-connected-fibre-normal-integrality.
11. For arbitrary T and t use lem-sc-fibre-dimension-after-base-change and
    lem-sbc-smooth-relative-dimension-permanence. The fibre is nonempty, integral,
    smooth of relative dimension a_i; lem-sbc-smooth-fixed-dimension-over-field
    gives its dimension a_i, including after every extension of the residue field.
12. Apply lem-sc-closed-irreducible-dimension-trdeg to the fibre and its generic point,
    and then to each point's closure. The latter has dimension at most that of the
    whole fibre, so its residue transcendence degree is at most a_i. Integrality
    supplies the unique generic point. There is no comparison of distinct a_i.

The existential localized dévissage below is constrained by algebra and module
isomorphisms to the canonical tensor extensions. The following equations identify
all ring arrows, alpha on its free basis, and the first and successive cokernel
identifications with their original maps after localization. Thus it is a localization
of the given data, rather than an unrelated dévissage. -/
theorem completeDevissage_fp_dimension_preparation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (N : Type v) [AddCommGroup N] [Module S N] [Module.FinitePresentation S N]
    (p : Ideal R) [p.IsPrime] (D : CompleteAlgebraDevissage R S p N) :
    (∀ i, Algebra.FinitePresentation R (D.A i) ∧
      Algebra.FinitePresentation R (D.B i) ∧
      (D.bToA i).toRingHom.FinitePresentation ∧
      (∀ (hi : i.val = 0), (D.sToA i hi).toRingHom.FinitePresentation) ∧
      (∀ (j : Fin D.n) (hij : j.val = i.val + 1),
        (D.bToAnext i j hij).toRingHom.FinitePresentation) ∧
      Module.FinitePresentation (D.A i) (D.M i) ∧
      Module.FinitePresentation (D.B i)
        ((ModuleCat.restrictScalars (D.bToA i).toRingHom).obj (D.M i)) ∧
      Module.FinitePresentation (D.B i)
        ((ModuleCat.restrictScalars (D.bToA i).toRingHom).obj (D.M i) ⧸
          LinearMap.range (D.alpha i))) ∧
    ∃ (f : R), f ∉ p ∧
      (∃ (p' : PrimeSpectrum (Localization.Away f)),
        p'.asIdeal = Ideal.map (algebraMap R (Localization.Away f)) p ∧
        ∃ (hfin : Module.Finite (completeDevissageLocalizedAlgebra f (CommAlgCat.of R S))
            (completeDevissageLocalizedModule f (CommAlgCat.of R S) (ModuleCat.of S N))),
        ∃ (E : @CompleteAlgebraDevissage (Localization.Away f)
          (completeDevissageLocalizedAlgebra f (CommAlgCat.of R S)) _ _ _ _ p'.asIdeal _
          (completeDevissageLocalizedModule f (CommAlgCat.of R S) (ModuleCat.of S N)) _ _ hfin),
        ∃ (e : Fin D.n ≃ Fin E.n),
        (∀ i, (e i).val = i.val) ∧
        ∃ (a : ∀ i, E.A (e i) ≃ₐ[Localization.Away f]
          completeDevissageLocalizedAlgebra f (D.A i))
          (b : ∀ i, E.B (e i) ≃ₐ[Localization.Away f]
          completeDevissageLocalizedAlgebra f (D.B i))
          (m : ∀ i, E.M (e i) ≃ₗ[E.A (e i)]
            (ModuleCat.restrictScalars (a i).toRingHom).obj
              (completeDevissageLocalizedModule f (D.A i) (D.M i)))
          (hr : ∀ i, E.rIndex (e i) = D.rIndex i),
        (∀ i (x : D.B i),
          a i (E.bToA (e i) ((b i).symm ((1 : Localization.Away f) ⊗ₜ[R] x))) =
            ((1 : Localization.Away f) ⊗ₜ[R] D.bToA i x)) ∧
        (∀ i (hi : i.val = 0) (hi' : (e i).val = 0) (s : S),
          a i (E.sToA (e i) hi' ((1 : Localization.Away f) ⊗ₜ[R] s)) =
            ((1 : Localization.Away f) ⊗ₜ[R] D.sToA i hi s)) ∧
        (∀ i j (hij : j.val = i.val + 1) (hij' : (e j).val = (e i).val + 1)
          (x : D.B i),
          a j (E.bToAnext (e i) (e j) hij' ((b i).symm ((1 : Localization.Away f) ⊗ₜ[R] x))) =
            ((1 : Localization.Away f) ⊗ₜ[R] D.bToAnext i j hij x)) ∧
        (∀ i (j : Fin (D.rIndex i)),
          m i (E.alpha (e i) (Pi.single (Fin.cast (hr i).symm j) 1)) =
            completeDevissageLocalizedUnit f (D.A i) (D.M i)
              (D.alpha i (Pi.single j 1))) ∧
        (∀ i (hi : i.val = 0) (hi' : (e i).val = 0) (x : N),
          m i (E.firstIso (e i) hi'
            (completeDevissageLocalizedUnit f (CommAlgCat.of R S) (ModuleCat.of S N) x)) =
            completeDevissageLocalizedUnit f (D.A i) (D.M i) (D.firstIso i hi x)) ∧
        (∀ i j (hij : j.val = i.val + 1) (hij' : (e j).val = (e i).val + 1)
          (x : D.M i),
          m j (E.cokerIso (e i) (e j) hij'
            (Submodule.Quotient.mk
              ((m i).symm (completeDevissageLocalizedUnit f (D.A i) (D.M i) x)))) =
            completeDevissageLocalizedUnit f (D.A j) (D.M j)
              (D.cokerIso i j hij (Submodule.Quotient.mk x)))) ∧
      ∃ (a : Fin D.n → ℕ), ∀ i,
        Smooth (completeDevissageLocalizedSpecMap f (D.B i)) ∧
        Flat (completeDevissageLocalizedSpecMap f (D.B i)) ∧
        LocallyOfFinitePresentation (completeDevissageLocalizedSpecMap f (D.B i)) ∧
        QuasiCompact (completeDevissageLocalizedSpecMap f (D.B i)) ∧
        QuasiSeparated (completeDevissageLocalizedSpecMap f (D.B i)) ∧
        GeometricallyIntegral (completeDevissageLocalizedSpecMap f (D.B i)) ∧
        SmoothOfRelativeDimension (a i) (completeDevissageLocalizedSpecMap f (D.B i)) ∧
        ∀ (T : Scheme.{u}) (g : T ⟶ Spec (.of (Localization.Away f))) (t : T),
          GeometricallyIntegral (completeDevissageBaseChangeFibreMap f (D.B i) g t) ∧
          IsIntegral (completeDevissageBaseChangeFibre f (D.B i) g t) ∧
          topologicalKrullDim (completeDevissageBaseChangeFibre f (D.B i) g t) =
            (a i : WithBot ℕ∞) ∧
          (∃! ξ : completeDevissageBaseChangeFibre f (D.B i) g t,
            IsGenericPoint ξ Set.univ) ∧
          (∀ ξ : completeDevissageBaseChangeFibre f (D.B i) g t,
            IsGenericPoint ξ Set.univ →
              @Algebra.trdeg (T.residueField t)
                ((completeDevissageBaseChangeFibre f (D.B i) g t).residueField ξ) _ _
                (Scheme.Hom.residueFieldAlgebraMap
                  (completeDevissageBaseChangeFibreMap f (D.B i) g t) ξ).toAlgebra =
                (a i : Cardinal)) ∧
          (∀ x : completeDevissageBaseChangeFibre f (D.B i) g t,
            @Algebra.trdeg (T.residueField t)
              ((completeDevissageBaseChangeFibre f (D.B i) g t).residueField x) _ _
              (Scheme.Hom.residueFieldAlgebraMap
                (completeDevissageBaseChangeFibreMap f (D.B i) g t) x).toAlgebra ≤
              (a i : Cardinal)) := by
  sorry

end AlgebraicGeometry
