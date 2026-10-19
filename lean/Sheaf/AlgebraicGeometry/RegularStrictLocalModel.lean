/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.SmoothColimitRegular
import Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.ExcellentOfWeaklyEtale
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.RegularLocalMaximal
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.RegularComposition
import Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit
import Sheaf.RingTheory.GeometricRegularitySeparableExtension
import Sheaf.RingTheory.RegularBaseChange
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Regular morphisms and compatible strict local models

Source: Illusie--Laszlo--Orgogozo, Exposé XVII, reductions at Lemma 4.3.2.1
and Lemmas 4.3.2.3--4.3.2.4; Stacks Project, Tags 07C0, 07C1, 06LJ and
06LN (blueprint: lem-per-regular-strict-local-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A regular morphism between Noetherian schemes is flat with geometrically regular
fibres, tested after every finite extension of each residue field. The same condition
is written explicitly for each induced morphism.
Source: Stacks Project, More on Algebra, Definition 07BZ and ILO XVII 4.3.2.1
(blueprint: lem-per-regular-strict-local-model).

Proof steps: (1) choose affine charts at the images of the two geometric points and
identify the two strict localizations with strict henselizations of the corresponding
Noetherian local rings, using the etale residue-triple comparison and the localized
strict-henselization lemma; the canonical functoriality map gives `H` and its structural
square and the geometric-point equation. Uniqueness follows from the uniqueness of
pointed etale lifts into a henselian local ring, applied to every neighbourhood.
(2) The strict henselizations are filtered ind-etale colimits, hence weakly
etale; excellence follows from weakly-etale ascent and Noetherianity from the strict
henselization Noetherian theorem. (3) The stalk map of `h` is regular. The target
strict henselization is a filtered colimit of etale algebras; etale maps are smooth and
smooth filtered colimits are regular, so the target strict-henselization map and its
composite from the original base local ring are regular. (4) Flat base change and the
flat tensor-scalar comparison,
followed by flat composition, prove flatness of `H`. (5--6) Tensor the finite separable
fibre decomposition of the base strict henselization with the target; its idempotent
factors are geometrically regular, and separable extension preserves geometric
regularity, proving regularity of every fibre of `H`. (7--8) Apply the flat height
formula to the two strict-henselization maps and to `H` and `h`; their selected fibre
factors are fields, so cancellation gives equality of the two local fibre dimensions.
(9) The same localization argument at ordinary compatible points gives the analogous
assertion. (10) An affine closed subscheme is a quotient; the fibre product is the
corresponding quotient of the target, regularity follows from regular base change, and
Noetherian excellence follows from finite-type localization. The zero quotient includes
the empty closed subscheme. -/
theorem regular_strict_local_model
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hY : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U))
    (h : Y ⟶ X)
    [Flat h]
    (hreg : ∀ (x : X) (L : Type u) [Field L]
      [Algebra (X.residueField x) L] [Module.Finite (X.residueField x) L],
      IsRegularScheme (pullback (h.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) L)))))
    {ΩX ΩY : Type u} [Field ΩX] [IsAlgClosed ΩX] [Field ΩY] [IsAlgClosed ΩY]
    (barX : Spec (.of ΩX) ⟶ X) (barY : Spec (.of ΩY) ⟶ Y)
    (e : ΩX →+* ΩY)
    (hbar : barY ≫ h = Spec.map (CommRingCat.ofHom e) ≫ barX) :
    ∃! (H : Scheme.strictHenselizationScheme barY ⟶
        Scheme.strictHenselizationScheme barX),
      H ≫ Scheme.strictHenselizationStructuralMap barX =
        Scheme.strictHenselizationStructuralMap barY ≫ h ∧
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation barY)) ≫ H =
        Spec.map (CommRingCat.ofHom e) ≫
          Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation barX)) ∧
      IsLocalHom H.appTop.hom ∧
      Flat H ∧
      (∀ (u₀ : Scheme.strictHenselizationScheme barX) (L : Type u) [Field L]
          [Algebra ((Scheme.strictHenselizationScheme barX).residueField u₀) L]
          [Module.Finite ((Scheme.strictHenselizationScheme barX).residueField u₀) L],
        IsRegularScheme (pullback (H.fiberToSpecResidueField u₀)
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((Scheme.strictHenselizationScheme barX).residueField u₀) L))))) ∧
      IsNoetherian (Scheme.strictHenselizationScheme barY) ∧
      IsNoetherian (Scheme.strictHenselizationScheme barX) ∧
      (∀ U : (Scheme.strictHenselizationScheme barY).affineOpens,
        IsExcellent Γ(Scheme.strictHenselizationScheme barY, U)) ∧
      (∀ U : (Scheme.strictHenselizationScheme barX).affineOpens,
        IsExcellent Γ(Scheme.strictHenselizationScheme barX, U)) ∧
      (∀ (v : Scheme.strictHenselizationScheme barY),
        ringKrullDim
            ((H.fiber (H v)).presheaf.stalk (H.asFiber v)) =
          ringKrullDim
            ((h.fiber (h ((Scheme.strictHenselizationStructuralMap barY) v))).presheaf.stalk
              (h.asFiber ((Scheme.strictHenselizationStructuralMap barY) v)))) ∧
      (∀ (C : Scheme.{u}) (i : C ⟶ Scheme.strictHenselizationScheme barX)
          [AlgebraicGeometry.IsClosedImmersion i],
        Flat (pullback.snd H i) ∧
        (∀ (c : C) (L : Type u) [Field L]
            [Algebra (C.residueField c) L] [Module.Finite (C.residueField c) L],
          IsRegularScheme (pullback ((pullback.snd H i).fiberToSpecResidueField c)
            (Spec.map (CommRingCat.ofHom (algebraMap (C.residueField c) L))))) ∧
        IsNoetherian (pullback H i) ∧ IsNoetherian C ∧
        (∀ U : (pullback H i).affineOpens, IsExcellent Γ(pullback H i, U)) ∧
        (∀ U : C.affineOpens, IsExcellent Γ(C, U))) ∧
      (∀ y₀ : Y,
        Flat (Spec.map (h.stalkMap y₀)) ∧
        (∀ (x : Spec (X.presheaf.stalk (h y₀))) (L : Type u) [Field L]
            [Algebra ((Spec (X.presheaf.stalk (h y₀))).residueField x) L]
            [Module.Finite ((Spec (X.presheaf.stalk (h y₀))).residueField x) L],
          IsRegularScheme (pullback ((Spec.map (h.stalkMap y₀)).fiberToSpecResidueField x)
            (Spec.map (CommRingCat.ofHom
              (algebraMap ((Spec (X.presheaf.stalk (h y₀))).residueField x) L))))) ∧
        IsNoetherian (Spec (Y.presheaf.stalk y₀)) ∧
        IsNoetherian (Spec (X.presheaf.stalk (h y₀))) ∧
        (∀ U : (Spec (Y.presheaf.stalk y₀)).affineOpens,
          IsExcellent Γ(Spec (Y.presheaf.stalk y₀), U)) ∧
        (∀ U : (Spec (X.presheaf.stalk (h y₀))).affineOpens,
          IsExcellent Γ(Spec (X.presheaf.stalk (h y₀)), U)) ∧
        ∀ v : Spec (Y.presheaf.stalk y₀),
          ringKrullDim
              (((Spec.map (h.stalkMap y₀)).fiber ((Spec.map (h.stalkMap y₀)) v)).presheaf.stalk
                ((Spec.map (h.stalkMap y₀)).asFiber v)) =
            ringKrullDim
              ((h.fiber (h ((Y.fromSpecStalk y₀) v))).presheaf.stalk
                (h.asFiber ((Y.fromSpecStalk y₀) v)))) := by
  sorry

end AlgebraicGeometry
