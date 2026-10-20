/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Strictly semistable curves

Source: Temkin, Stable Modification of Relative Curves, arXiv:0707.3953v3,
§1.2 and §4.3, p. 27 (blueprint: def-trf-strictly-semistable-curve).

The nodal chart reuses the universal chart and parameter map from
`lem-trf-nodal-family-etale-local-model`: its pullback along `a` is
`Spec A[u,v]/(uv-a)`. The base and source neighbourhoods here are Zariski opens.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A strictly semistable curve is flat and finitely presented, with fibres of pure
 dimension one, and Zariski locally on source and base has an étale affine-line or
 nodal chart over the base. Finite presentation includes quasi-compactness and
 quasi-separatedness; neither separatedness nor properness is required.

Source: Temkin, Stable Modification of Relative Curves, arXiv:0707.3953v3,
§1.2 and §4.3, p. 27 (blueprint: def-trf-strictly-semistable-curve).

For an affine base neighbourhood `V`, the nodal pullback is canonically the spectrum
of `Γ(V, ⊤)[u,v]/(uv-a)`. The two chart equations specify the given structure morphism,
so the étale maps are maps over that base neighbourhood, not unrelated scheme maps.
The pure-dimension condition allows empty fibres, including the empty curve. -/
def IsStrictlySemistableCurve {C T : Scheme.{u}} (f : C ⟶ T) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
    (∀ t : T, (f.fiber t).IsPureDimension 1) ∧
    ∀ c : C, ∃ (U : C.Opens) (V : T.Opens) (hV : IsAffineOpen V), c ∈ U ∧
      ((∃ h : U.toScheme ⟶ Spec (.of (Polynomial Γ(T, V))),
          Etale h ∧
            h ≫ Spec.map (CommRingCat.ofHom Polynomial.C) ≫ hV.fromSpec = U.ι ≫ f) ∨
        ∃ (a : Γ(V.toScheme, ⊤))
          (h : U.toScheme ⟶ pullback nodalModelBaseMap (nodalBaseMap a)),
          Etale h ∧
            h ≫ pullback.snd nodalModelBaseMap (nodalBaseMap a) ≫ V.ι = U.ι ≫ f)

end AlgebraicGeometry
