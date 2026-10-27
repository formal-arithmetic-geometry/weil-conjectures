/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
import Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.TensorPullbackFreeBasisIso
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.ModuleStrictTransformUniversalExact
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Sheaf.RingTheory.FreeSubtractionFlatness
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Strict-transform flatness for a generically free exact sequence

Source: Stacks Project, flat.tex, Tag 0815, `theorem-flatten-module`, third proof
paragraph; Tag 05I3, `lemma-induction-step`; divisors.tex, Tag 080W,
`lemma-strict-transform-universally-injective`
(blueprint: lem-trf-smooth-free-sequence-transform-flatness).

The cokernel is the actual categorical cokernel of the given map. Quasi-coherence
witnesses needed to form its strict transform are conclusions, not assumptions.
The free pullback comparison is normalized by the pinned structure map on each summand.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- For an affine smooth family with geometrically integral fibres, subtracting a free
subsheaf which is a basis on a surjective open gives the same relative flat locus
for the middle term and its cokernel, after every admissible blowup. The induced
sequence is short exact, its two quotient squares commute, and the basis open
remains surjective with an isomorphism on it.
Source: Stacks Project, Tags 0815 (third proof paragraph), 05I3 and 080W
(blueprint: lem-trf-smooth-free-sequence-transform-flatness).

Proof:
1. The cokernel is quasi-coherent by `lem-weil-pbc-quasi-coherent-module-cokernel-closure`.
   Composing local finite free surjections proves it is finite type. Smoothness gives
   flatness by `sbc-lem-smooth-criterion`, so the free source is flat over the base.
   `lem-trf-module-admissible-blowup-calculus` identifies its strict-transform quotient
   with an isomorphism and makes both other transforms quasi-coherent and finite type.
   The canonical free pullback comparison sends c tensor (a_i) to (c a_i).
2. Apply `lem-trf-strict-transform-universal-exact` to the universally short exact
   sequence and the retained finite-type centre. Use the free-term identification
   from step 1. Pullback maps preserve sections supported on the exceptional locus,
   hence descend to the strict-transform quotients. On quotient classes this gives
   exactly the two displayed commuting squares; epimorphic quotient maps make the
   descended maps unique.
3. `lem-weil-pbc-surjective-base-change` makes the pulled-back basis open surjective.
   Pulling back the inverse of the original basis map gives an isomorphism there.
   It and its inverse identify the exceptional-supported kernels, so their quotient
   is the induced basis isomorphism, even where this open meets the exceptional locus.
4. Take an affine open Spec R of the new base. The full inverse image is affine
   Spec A by `lem-weil-pbc-affine-morphism-permanence`. Smoothness base-changes by
   `lem-pc-proper-base-change`; `sbc-lem-smooth-criterion` and
   `lem-weil-pbc-lfp-affine-opens-finite-presentation` make R to A flat and finitely
   presented. Fibre-product associativity (`def-pc-fibre-product`) identifies its
   field-extended fibres with field extensions of the original integral fibres.
5. The tilde/Gamma adjunction `lem-weil-pbc-affine-tilde-gamma-adjunction` writes the
   middle and quotient transforms as tilde N and tilde Q, with Q the cokernel of
   A^r to N. The module N is finite by `lem-weil-pbc-quasi-coherent-finite-type-affine`.
   `lem-sbc-affine-module-germ-localization` identifies their stalks with localizations.
   Each integral fibre meets the surjective basis open, whose nonempty intersection
   therefore contains the fibre generic point. At that point the middle term is
   free and base-flat, and the map is a basis after tensoring with the residue field.
6. Apply `lem-trf-free-subtraction-flatness` with all the hypotheses from steps 4--5.
   It gives the claimed equivalence at every stalk. The affine-open basis
   `lem-weil-pbc-affine-opens-basis` covers every base point. Taking all stalks and
   using `def-pc-scheme-module-flat-over` proves the final relative-flatness equivalence. -/
theorem smoothFreeSequence_transform_flatness
    {S X : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsAffineHom f] [Smooth f]
    [GeometricallyIntegral f] (U : S.Opens) (hU : IsCompact (U : Set S))
    (F : X.Modules) [hF : F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (α : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ F)
    (W : X.Opens) (hW : Surjective (W.ι ≫ f))
    (hαW : IsIso ((restrictFunctor W.ι).map α)) (hα : Mono α)
    (hbase : ∀ (T : Scheme.{u}) (t : T ⟶ S),
      ∃ w : (tensorPullback (pullback.fst f t)).map α ≫
          (tensorPullback (pullback.fst f t)).map (cokernel.π α) = 0,
        (ShortComplex.mk ((tensorPullback (pullback.fst f t)).map α)
          ((tensorPullback (pullback.fst f t)).map (cokernel.π α)) w).ShortExact) :
    ∃ (hfree : (SheafOfModules.free (R := X.ringCatSheaf)
        (ULift.{u} (Fin r))).IsQuasicoherent) (hH : (cokernel α).IsQuasicoherent),
      ∀ B : IsAdmissible S U, ∃ hI : B.I.toModules.IsFiniteType,
        IsIso (cokernel.π (kernel.ι (moduleStrictTransformRestriction f B.I
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))))) ∧
        ∃ (αb : SheafOfModules.free
              (R := (Limits.pullback f B.I.blowupMap).ringCatSheaf) (ULift.{u} (Fin r)) ⟶
            @moduleStrictTransform X S f B.I hI F hF)
          (βb : @moduleStrictTransform X S f B.I hI F hF ⟶
            @moduleStrictTransform X S f B.I hI (cokernel α) hH)
          (w : αb ≫ βb = 0),
          (ShortComplex.mk αb βb w).ShortExact ∧
          (tensorPullbackFreeBasisIso (pullback.fst f B.I.blowupMap)
              (ULift.{u} (Fin r))).hom ≫ αb =
            (tensorPullback (pullback.fst f B.I.blowupMap)).map α ≫
              cokernel.π (kernel.ι (moduleStrictTransformRestriction f B.I F)) ∧
          cokernel.π (kernel.ι (moduleStrictTransformRestriction f B.I F)) ≫ βb =
            (tensorPullback (pullback.fst f B.I.blowupMap)).map (cokernel.π α) ≫
              cokernel.π (kernel.ι (moduleStrictTransformRestriction f B.I (cokernel α))) ∧
          Surjective (((pullback.fst f B.I.blowupMap) ⁻¹ᵁ W).ι ≫
            pullback.snd f B.I.blowupMap) ∧
          IsIso ((restrictFunctor ((pullback.fst f B.I.blowupMap) ⁻¹ᵁ W).ι).map αb) ∧
          (∀ y : (Limits.pullback f B.I.blowupMap : Scheme.{u}),
            Module.Flat (B.I.blowup.presheaf.stalk ((pullback.snd f B.I.blowupMap) y))
              ((ModuleCat.restrictScalars
                ((pullback.snd f B.I.blowupMap).stalkMap y).hom).obj
                  ((RingedSpace.moduleStalkFunctor
                    (Limits.pullback f B.I.blowupMap).toRingedSpace y).obj
                      (@moduleStrictTransform X S f B.I hI F hF))) ↔
            Module.Flat (B.I.blowup.presheaf.stalk ((pullback.snd f B.I.blowupMap) y))
              ((ModuleCat.restrictScalars
                ((pullback.snd f B.I.blowupMap).stalkMap y).hom).obj
                  ((RingedSpace.moduleStalkFunctor
                    (Limits.pullback f B.I.blowupMap).toRingedSpace y).obj
                      (@moduleStrictTransform X S f B.I hI (cokernel α) hH)))) ∧
          ((@moduleStrictTransform X S f B.I hI (cokernel α) hH).IsFlatOver
              (pullback.snd f B.I.blowupMap) ↔
            (@moduleStrictTransform X S f B.I hI F hF).IsFlatOver
              (pullback.snd f B.I.blowupMap)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
