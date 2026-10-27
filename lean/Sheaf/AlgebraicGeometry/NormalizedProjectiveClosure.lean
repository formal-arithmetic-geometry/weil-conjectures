/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q77
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Compactification.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
import Sheaf.AlgebraicGeometry.NagataAffineOpensProjective
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Normalization of a specified projective closure of an affine curve

Source: Stacks Project, Curves, Tags 0BY1 (theorem-curves-rational-maps), final
compactify-then-normalize alternative, and 0BY3 (lemma-nonsingular-model-smooth);
Morphisms, Tag 056B (lemma-scheme-theoretic-image-reduced).
(blueprint: lem-trf-normalized-projective-closure).

The four construction abbreviations retain the given affine embedding. The projective
space is the base-change realization of relative Proj; its standard chart is the published
coordinate map `T_i / T_0`, with homogeneous coordinate `none` denoting `T_0` and `some i`
denoting the remaining coordinates. Function fields are the actual generic stalks.

## Main declarations

* `NormalizedProjectiveClosure.embedding`, `scheme`, `ι`, `toBase`: the specified closure.
* `normalized_projective_closure`: its geometry and its normalized function-field comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace NormalizedProjectiveClosure

variable {k : Type u} [Field k] {U : Scheme.{u}} (n : ℕ)
  (i : U ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k)))

/-- The given affine embedding followed by the standard chart `D_+(T_0)`.
Source: Stacks Project, Curves, Tag 0BY1, final compactification alternative;
standard chart `T_i / T_0` as in the relative-Proj interface.
(blueprint: lem-trf-normalized-projective-closure). -/
noncomputable abbrev embedding : U ⟶ ℙ(Option (ULift.{u} (Fin n)); Spec (.of k)) :=
  i ≫ AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin n)) (Spec (.of k))

/-- The scheme-theoretic closure of the specified embedding, not an arbitrary completion.
Source: Stacks Project, Curves, Tag 0BY1, final compactification alternative;
Morphisms, Tag 056B for its reducedness.
(blueprint: lem-trf-normalized-projective-closure). -/
noncomputable abbrev scheme : Scheme.{u} := (embedding n i).image

/-- The canonical factorization from the affine curve into its specified closure.
Source: Stacks Project, Curves, Tag 0BY1, final compactification alternative.
(blueprint: lem-trf-normalized-projective-closure). -/
noncomputable abbrev ι : U ⟶ scheme n i := (embedding n i).toImage

/-- The structure map of the specified closure, obtained from its closed embedding in
projective space over the given field.
Source: Stacks Project, Curves, Tag 0BY1, final compactification alternative.
(blueprint: lem-trf-normalized-projective-closure). -/
noncomputable abbrev toBase : scheme n i ⟶ Spec (.of k) :=
  (embedding n i).imageι ≫ (ℙ(Option (ULift.{u} (Fin n)); Spec (.of k)) ↘ Spec (.of k))

end NormalizedProjectiveClosure

open NormalizedProjectiveClosure

/-- The scheme-theoretic closure of a specified affine embedding of an integral curve is
integral, projective and one-dimensional; its canonical normalization is an integral smooth
proper finite-type curve. The generic-stalk isomorphisms are induced by the specified open
immersion and normalization, and their composite is an isomorphism over the given field.

Source: Stacks Project, Curves, Tags 0BY1 (theorem-curves-rational-maps), final
compactify-then-normalize alternative, and 0BY3 (lemma-nonsingular-model-smooth);
Morphisms, Tag 056B (lemma-scheme-theoretic-image-reduced).
(blueprint: lem-trf-normalized-projective-closure).

Proof:
1. The field spectrum is Noetherian. The projective-closure construction of
   det-nagata-affine-opens-projective works for the given embedding and makes this very
   scheme-theoretic image projective and proper and its factorization a dense open immersion.
2. By lem-trf-reduced-scheme-image the closure is reduced, and its underlying space is the
   closure of the nonempty irreducible image of U. It is therefore integral.
3. Apply lem-sc-integral-locally-algebraic-opens-dimension to the nonempty open image of U:
   the dimension of the closure is dim U = 1.
4. By lem-sc-normalization-exists its normalization is finite and surjective, proper over k,
   and of the same dimension. By def-fin-normalization-extension and def-sc-normalization,
   above a nonempty affine Spec A it is Spec of the integral closure A' in k(X).
   By lem-sc-integral-function-field-affine-fraction, A and A' are domains with the same
   fraction field. Their zero-prime generic points agree on affine overlaps and glue to the
   generic point of the normalization. This proves integrality and identifies the actual
   generic-stalk map of the normalization with the fraction-field isomorphism.
5. Apply lem-sc-normalized-curve-smooth over the perfect field to this normalization.
6. Scheme sobriety (lem-sc-scheme-sober) identifies the image of the generic point under
   the dense open immersion with the generic point of the closure. Restricting the structure
   sheaf to this open leaves its generic stalk unchanged. Thus its actual generic-stalk map
   is also an isomorphism; the normalization case was established in step 4.
7. Both maps are over k. Functoriality of sections and germs shows their generic-stalk
   isomorphisms commute with k-scalars. The inverse of the normalization isomorphism also
   commutes with scalars, as does its composite with the open-immersion isomorphism.
-/
theorem normalized_projective_closure
    {k : Type u} [Field k] [PerfectField k] {U : Scheme.{u}}
    (p : U ⟶ Spec (.of k)) [IsAffine U] [IsIntegral U]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim U = 1) (n : ℕ)
    (i : U ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k))) [IsClosedImmersion i]
    (hi : i ≫ (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) = p) :
    ∃ _hX : IsIntegral (scheme n i),
      IsHProjective (toBase n i) ∧ topologicalKrullDim (scheme n i) = 1 ∧
      IsOpenImmersion (ι n i) ∧ DenseRange (ι n i) ∧
      ∃ _hC : IsIntegral (scheme n i).normalization,
        Smooth ((scheme n i).fromNormalization ≫ toBase n i) ∧
        IsProper ((scheme n i).fromNormalization ≫ toBase n i) ∧
        LocallyOfFiniteType ((scheme n i).fromNormalization ≫ toBase n i) ∧
        QuasiCompact ((scheme n i).fromNormalization ≫ toBase n i) ∧
        topologicalKrullDim (scheme n i).normalization = 1 ∧
        ∃ (hj : (ι n i) (genericPoint U) = genericPoint (scheme n i))
          (hν : (scheme n i).fromNormalization (genericPoint (scheme n i).normalization) =
            genericPoint (scheme n i)),
          ∃ (ej : (scheme n i).functionField ≅ U.functionField)
            (eν : (scheme n i).functionField ≅ (scheme n i).normalization.functionField),
            ej.hom = (ι n i).functionFieldMap hj ∧
            eν.hom = (scheme n i).fromNormalization.functionFieldMap hν ∧
            ((Scheme.ΓSpecIso (.of k)).inv ≫ (toBase n i).appTop ≫
                (scheme n i).presheaf.germ ⊤ (genericPoint (scheme n i)) trivial) ≫ ej.hom =
              (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
                U.presheaf.germ ⊤ (genericPoint U) trivial ∧
            ((Scheme.ΓSpecIso (.of k)).inv ≫ (toBase n i).appTop ≫
                (scheme n i).presheaf.germ ⊤ (genericPoint (scheme n i)) trivial) ≫ eν.hom =
              (Scheme.ΓSpecIso (.of k)).inv ≫
                ((scheme n i).fromNormalization ≫ toBase n i).appTop ≫
                (scheme n i).normalization.presheaf.germ ⊤
                  (genericPoint (scheme n i).normalization) trivial ∧
            ((Scheme.ΓSpecIso (.of k)).inv ≫
                ((scheme n i).fromNormalization ≫ toBase n i).appTop ≫
                (scheme n i).normalization.presheaf.germ ⊤
                  (genericPoint (scheme n i).normalization) trivial) ≫
                (eν.symm ≪≫ ej).hom =
              (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
                U.presheaf.germ ⊤ (genericPoint U) trivial := by
  sorry

end AlgebraicGeometry
