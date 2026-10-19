/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
import Sheaf.AlgebraicGeometry.StrictTransformDifferentCenters
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Proper

/-!
# Composition and flatness for admissible module strict transforms

Source: Stacks Project, Divisors, Tags 080B, 080D, 080F, 080I; flat.tex Tag 080Y
(blueprint: lem-trf-module-admissible-blowup-calculus).

The comparison is characterized by its composite with the successive quotient maps.
Finite-type and quasi-coherence witnesses needed by the strict-transform interface
are conclusions, rather than additional hypotheses.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical quotient from the ordinary pullback to its module strict transform.
Source: Stacks Project, Tag 080D (1)
(blueprint: lem-trf-module-admissible-blowup-calculus). -/
noncomputable def moduleStrictTransformQuotient {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] (F : X.Modules)
    [F.IsQuasicoherent] :
    (tensorPullback (pullback.fst f I.blowupMap)).obj F ⟶
      moduleStrictTransform f I F :=
  cokernel.π (kernel.ι (moduleStrictTransformRestriction f I F))

/-- Permanence for admissible module strict transforms.
Source: Stacks Project, Tags 080D, 080F (2), and 080Y
(blueprint: lem-trf-module-admissible-blowup-calculus).

Proof: properness of a finite-type blowup and qcqs permanence give a qcqs new base
(lemma-nagata-blowup-proper, lem-pc-separated-quasi-separated,
lem-weil-pbc-qcqs-morphism-permanence). The kernel description
(lem-trf-strict-transform-sheaf-kernel) gives quasi-coherence, the quotient, and its
isomorphism off the centre; admissibility places U in that locus, and
lemma-nagata-admissible-blowup-over-open identifies that locus over U with U itself.
Pullback preserves finite type (lem-weil-pbc-module-pullback-finite-type); composing
its local finite generating surjections with the quotient proves finite type.
If F is flat over S, arbitrary module base change preserves flatness
(lem-pc-relatively-flat-module-pullback). Principalization
(thm-nagata-blowup-principalizes-center) supplies a regular exceptional equation a.
Flat tensor exactness (lem-weil-pbc-flat-tensor-exact) makes multiplication by every
power of a injective. A supported section is killed by such a power
(lem-weil-pbc-affine-module-basic-open-localization), so it vanishes. Thus the kernel
of the quotient is zero, the quotient is an isomorphism and its target is flat.
-/
theorem moduleAdmissibleBlowupPermanence {X S : Scheme.{u}} (U : S.Opens)
    (_hU : IsCompact (U : Set S)) (f : X ⟶ S) (F : X.Modules)
    [hF : F.IsQuasicoherent] [CompactSpace S] [QuasiSeparatedSpace S]
    (B : IsAdmissible S U) :
    ∃ hI : B.I.toModules.IsFiniteType,
      (@moduleStrictTransform _ _ f B.I hI F hF).IsQuasicoherent ∧
      Epi (@moduleStrictTransformQuotient _ _ f B.I hI F hF) ∧
      IsIso ((SheafOfModules.overFunctor _
        ((pullback.snd f B.I.blowupMap) ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ U))).map
          (@moduleStrictTransformQuotient _ _ f B.I hI F hF)) ∧
      (F.IsFiniteType → (@moduleStrictTransform _ _ f B.I hI F hF).IsFiniteType) ∧
      (F.IsFlatOver f →
        IsIso (@moduleStrictTransformQuotient _ _ f B.I hI F hF) ∧
        (@moduleStrictTransform _ _ f B.I hI F hF).IsFlatOver
          (pullback.snd f B.I.blowupMap)) ∧
      CompactSpace B.I.blowup ∧ QuasiSeparatedSpace B.I.blowup := by
  sorry

/-- Composite centres and the canonical comparison of successive module strict transforms.
Source: Stacks Project, Tags 080B and 080I (1)
(blueprint: lem-trf-module-admissible-blowup-calculus).

Proof: apply thm-nagata-composition-of-blowups to the two finite-type centre ideals.
Its centre K has support Z union b(Z1), which misses U by admissibility. Associate the
fibre products using def-pc-fibre-product. The sheaf kernel description
(lem-trf-strict-transform-sheaf-kernel) gives quasi-coherence and the two quotient
maps. Pullback preserves their epimorphisms: use module stalk pullback, stalk
exactness and tensor right exactness (lem-weil-pbc-module-stalk-pullback,
lem-weil-pbc-module-stalk-exact, lem-weil-pbc-tensor-right-exact).
The kernel of the composite quotient is supported over the union centre, so is
contained in the kernel defining the single transform. This gives the comparison.
Principalization makes the first exceptional divisor Cartier
(thm-nagata-blowup-principalizes-center). The first transform has no supported
sections there. Apply lem-trf-strict-transform-different-centers to the second centre
and that divisor, using lemma-nagata-blowup-invertible-factor to compare the blowups.
The second transform has no sections supported over their union. Its inverse image
is exactly that of K: off Z, b is an isomorphism
(lemma-nagata-admissible-blowup-over-open), and above Z both unions contain all points.
Thus the comparison kernel vanishes and the comparison is an isomorphism. Its
commuting square with the epimorphic successive quotient uniquely determines it.
-/
theorem moduleAdmissibleBlowupCalculus {X S : Scheme.{u}} (U : S.Opens)
    (_hU : IsCompact (U : Set S)) (f : X ⟶ S) (F : X.Modules)
    [hF : F.IsQuasicoherent] [CompactSpace S] [QuasiSeparatedSpace S]
    (B : IsAdmissible S U)
    (C : IsAdmissible B.I.blowup (B.I.blowupMap ⁻¹ᵁ U)) :
    ∃ (hI : B.I.toModules.IsFiniteType) (hJ : C.I.toModules.IsFiniteType)
      (hF1 : (@moduleStrictTransform _ _ f B.I hI F hF).IsQuasicoherent)
      (K : S.IdealSheafData) (hK : K.toModules.IsFiniteType),
      (K.support : Set S) = (B.I.support : Set S) ∪
        B.I.blowupMap '' (C.I.support : Set B.I.blowup) ∧
      ∃ (e : C.I.blowup ≅ K.blowup)
        (m : Limits.pullback (pullback.snd f B.I.blowupMap) C.I.blowupMap ⟶
          Limits.pullback f K.blowupMap)
        (hm : pullback.fst (pullback.snd f B.I.blowupMap) C.I.blowupMap ≫
          pullback.fst f B.I.blowupMap = m ≫ pullback.fst f K.blowupMap),
        e.hom ≫ K.blowupMap = C.I.blowupMap ≫ B.I.blowupMap ∧
        m ≫ pullback.snd f K.blowupMap =
          pullback.snd (pullback.snd f B.I.blowupMap) C.I.blowupMap ≫ e.hom ∧
        IsIso m ∧
        ∃! a :
          @moduleStrictTransform _ _ (pullback.snd f B.I.blowupMap) C.I hJ
            (@moduleStrictTransform _ _ f B.I hI F hF) hF1 ⟶
          (tensorPullback m).obj (@moduleStrictTransform _ _ f K hK F hF),
          IsIso a ∧
          (tensorPullback
            (pullback.fst (pullback.snd f B.I.blowupMap) C.I.blowupMap)).map
              (@moduleStrictTransformQuotient _ _ f B.I hI F hF) ≫
            @moduleStrictTransformQuotient _ _ (pullback.snd f B.I.blowupMap) C.I hJ
              (@moduleStrictTransform _ _ f B.I hI F hF) hF1 ≫ a =
          (tensorPullbackCompositionIso
            (pullback.fst (pullback.snd f B.I.blowupMap) C.I.blowupMap)
            (pullback.fst f B.I.blowupMap) (m ≫ pullback.fst f K.blowupMap) hm).inv.app F ≫
          (tensorPullbackCompositionIso m (pullback.fst f K.blowupMap)
            (m ≫ pullback.fst f K.blowupMap) rfl).hom.app F ≫
          (tensorPullback m).map (@moduleStrictTransformQuotient _ _ f K hK F hF) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
