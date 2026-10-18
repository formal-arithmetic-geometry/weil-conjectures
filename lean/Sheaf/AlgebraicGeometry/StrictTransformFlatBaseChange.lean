/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Compactification.FiniteTypeExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Sober
import WeilConjectures.Blowup.Complement
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Strict transform under flat base change

Source: Stacks Project, Tag 081I, `lemma-flat-base-change-scheme-theoretic-image`,
and Tag 080D, `definition-strict-transform`
(blueprint: lem-trf-strict-transform-flat-etale-base-change).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Strict transform of a closed subscheme commutes with flat base change, with the
specified generic-point hypothesis. The first equality uses the canonical blowup comparison;
the second identifies the same ideal with the scheme-theoretic closure of the common open
inverse image of the complement of the center. Ideals, rather than supports, retain nilpotents.
An etale base change is included since an etale morphism is flat.

Source: Stacks Project Tags 081I and 080D
(blueprint: lem-trf-strict-transform-flat-etale-base-change).

Proof:
1. The flat blowup comparison identifies the base-changed blowup with the blowup of the
extended ideal (`def-nagata-blowup-flat-base-change-map`,
`thm-nagata-blowup-flat-base-change`). On affine opens the complements are the same finite
union of principal opens. The blowup is an isomorphism over that complement
(`thm-nagata-global-blowup-complement`), compatibly with the structure maps.
2. In `Z ×_X Bl_I X`, the preserved open has quasi-compact inclusion: locally the ideal
has finitely many generators and the complement is the finite union of their principal
opens. Its scheme-theoretic closure is the strict transform (`def-nagata-strict-transform`).
Restriction of its defining kernel to the open is zero, so this open embeds into the closure.
The same finite-principal-open argument makes this factorization quasi-compact.
3. The closure is cut out by the kernel of restriction to that open
(`lemma-nagata-scheme-image-ideal-qc`). The quotient by this kernel injects into the
pushforward of the open's structure sheaf. Thus the open is schematically dense in its
closure, including its nonreduced structure.
4. Base change along the flat map preserves this schematic density
(`lem-weil-pbc-flat-morphism-base-change`, `lemma-nagata-dense-flat-pullback`). The
base-changed preserved open still has quasi-compact inclusion, by the same local generators.
5. The map from the ambient structure sheaf to the preserved open factors through the
base-changed closure. Its second map has zero kernel, so the ambient kernel is exactly the
ideal of that closure. This is the strict-transform ideal after base change. The ambient
closed immersion into the base-changed blowup preserves equality of these ideals
(`def-weil-closed-immersion`). The generic-point hypothesis is retained, although flatness
alone suffices for this proof. Etale morphisms are flat (`def-weil-etale-morphism`). -/
theorem strictTransform_flat_baseChange
    {X Z W : Scheme.{u}} (I : X.IdealSheafData) (_hI : I.ofFiniteType)
    (i : Z ⟶ X) [IsClosedImmersion i] (v : W ⟶ X) [Flat v]
    (_hgeneric : ∀ C ∈ irreducibleComponents ↥(pullback i v),
      ∀ ξ : ↥(pullback i v), IsGenericPoint ξ C →
        ∃ D ∈ irreducibleComponents Z, IsGenericPoint (pullback.fst i v ξ) D) :
    (AlgebraicGeometry.strictTransformMap i I.blowupMap I.support.compl).ker.comap
        (pullback.fst I.blowupMap v) =
      (AlgebraicGeometry.strictTransformMap (pullback.snd i v) (I.comap v).blowupMap
        (I.comap v).support.compl).ker.comap (I.blowupFlatBaseChangeIso v).inv ∧
    (AlgebraicGeometry.strictTransformMap i I.blowupMap I.support.compl).ker.comap
        (pullback.fst I.blowupMap v) =
      ((AlgebraicGeometry.strictTransformOpen (pullback.snd i v)
          (pullback.snd I.blowupMap v) (v ⁻¹ᵁ I.support.compl)).ι ≫
        pullback.snd (pullback.snd i v) (pullback.snd I.blowupMap v)).ker := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
