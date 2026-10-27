/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedOpenSpreading
import Sheaf.AlgebraicGeometry.SmoothConnectedFibreNormalIntegrality

/-!
# Spreading a geometrically irreducible smooth-fibre open

Source: Stacks Project, Tag 057J (`lemma-normal-morphism-irreducible`), specialized to
smooth morphisms using Tag 056W, as applied in Tag 057K
(blueprint: lem-trf-geometrically-integral-fibre-neighbourhood).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A geometrically irreducible open in a fibre of a smooth finitely presented morphism
spreads to a quasi-compact open with geometrically integral fibres over an affine elementary
étale neighbourhood. The last equality is in the lattice of opens of the new ambient fibre:
the comparison is the canonical pullback map induced by `a` and its residue-field map,
followed by transport along `hs`. Thus it specifies equality as open subschemes, including
their embeddings, rather than an abstract isomorphism of schemes.

Source: Stacks Project, Tag 057J, smooth specialization via Tag 056W used in Tag 057K
(blueprint: lem-trf-geometrically-integral-fibre-neighbourhood).

Proof:
1. Geometric irreducibility implies geometric connectedness: every field base change is
   irreducible and therefore nonempty and connected.
2. Apply `lem-trf-smooth-connected-open-spreading` to obtain the affine elementary étale
   neighbourhood and quasi-compact open `V`. Its structure morphism is smooth and
   geometrically connected, and it has precisely the prescribed embedded open fibre.
3. Apply `lem-trf-smooth-connected-fibre-normal-integrality` to that structure morphism.
   For every base point and every extension of its residue field, the extended fibre is
   integral. Mathlib's field-extension criterion and fibrewise criterion turn this into
   geometric integrality of `V` over the new base. All other witnesses and the embedded
   fibre equality are retained from step 2.
-/
theorem exists_geometricallyIntegral_fibre_neighbourhood {Y S : Scheme.{u}}
    (h : Y ⟶ S) [Smooth h] [LocallyOfFinitePresentation h] [QuasiCompact h]
    [QuasiSeparated h] (s : S) (T : (h.fiber s).Opens)
    [GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField s)] :
    ∃ (S₁ : Scheme.{u}) (a : S₁ ⟶ S) (s₁ : S₁) (hs : a s₁ = s),
      IsAffine S₁ ∧ Etale a ∧ IsIso (a.residueFieldMap s₁) ∧
      ∃ V : (pullback h a).Opens,
        IsCompact (V : Set ↥(pullback h a)) ∧
        GeometricallyIntegral (V.ι ≫ pullback.snd h a) ∧
        (pullback.snd h a).fiberι s₁ ⁻¹ᵁ V =
          (pullback.map (pullback.snd h a) (S₁.fromSpecResidueField s₁)
              h (S.fromSpecResidueField (a s₁))
              (pullback.fst h a) (Spec.map (a.residueFieldMap s₁)) a
              (pullback.condition (f := h) (g := a)).symm
              (a.SpecMap_residueFieldMap_fromSpecResidueField s₁).symm ≫
            eqToHom (congrArg h.fiber hs)) ⁻¹ᵁ T := by
  have : GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField s) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  obtain ⟨S₁, a, s₁, hs, haff, het, hres, V, hcompact, hsmooth, hconn, hfibre⟩ :=
    exists_smooth_geometricallyConnected_fibre_neighbourhood h s T
  have : Smooth (V.ι ≫ pullback.snd h a) := hsmooth
  have : GeometricallyConnected (V.ι ≫ pullback.snd h a) := hconn
  refine ⟨S₁, a, s₁, hs, haff, het, hres, V, hcompact, ?_, hfibre⟩
  rw [GeometricallyIntegral.iff_geometricallyIntegral_fiber]
  intro t
  constructor
  refine (geometrically_iff_of_commRing (R := S₁.residueField t) (P := IsIntegral)
    (f := (V.ι ≫ pullback.snd h a).fiberToSpecResidueField t)).mpr ?_
  intro K _ _ Z fst snd hZ
  have : IsIntegral (pullback ((V.ι ≫ pullback.snd h a).fiberToSpecResidueField t)
      (Spec.map (CommRingCat.ofHom (algebraMap (S₁.residueField t) K)))) :=
    (smooth_connected_fibre_normal_integrality (V.ι ≫ pullback.snd h a)
      (fun _ ↦ inferInstance) t K).1
  exact IsIntegral.of_isIso hZ.isoPullback.inv

end AlgebraicGeometry
