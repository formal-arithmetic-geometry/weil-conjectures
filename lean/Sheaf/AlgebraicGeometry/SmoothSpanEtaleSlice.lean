/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.SmoothPointEtaleImmersion
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-! # Restriction of a pointed étale span to an étale slice

Source: Stacks Project, Tag 0GDX, lemma-relative-map-approximation-pre, final paragraph;
Tag 057G, lemma-slice-smooth (blueprint: lem-trf-smooth-span-etale-slice).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A pointed étale span over a smooth base restricts to a closed étale slice.
Source: Stacks Project, Tags 0GDX (final proof paragraph) and 057G.
(blueprint: lem-trf-smooth-span-etale-slice)

The maps `j`, `qV`, and `τ` are the specified composites, not additional choices.
The four equations for `kX` and `kY` uniquely characterize the canonical restriction
maps to the old base changes. The four equations for `aV` and `cV` characterize the
restricted span. The comparison isomorphisms `eX` and `eY` preserve both projections.
The canonical map from the fibre over `h` to its residue-field spectrum is an
isomorphism; its unique point gives the uniquely determined point `w` over `h`.

Proof:
1. The residue-field isomorphism makes `s'` a rational point of the fibre of `q`.
   It is closed: in an affine neighbourhood of any specialization, evaluation into
   the base field is surjective, so its kernel is maximal. Apply
   lem-trf-smooth-point-etale-immersion (Tag 057G). Factor the immersion as a closed
   immersion into an open neighbourhood `O`, followed by `O.ι`. This gives `V`, `i`,
   `v`, an étale composite `qV`, and its singleton underlying fibre.
2. Open and closed immersions induce residue-field isomorphisms, by
   lem-weil-pbc-residue-field-point-naturality and
   lem-weil-pbc-closed-immersion-residue-field-iso. Compose with the assumed
   isomorphism for `q` to obtain the one for `qV`. Naturality of canonical residue
   point morphisms lifts Spec κ(s') to `V`, and then lifts Spec κ(h) to `V`.
3. By def-pc-fibre-product the fibre of `W → H` over `h` is
   `V ×[S'] Spec κ(h)`. The point map factors through `O`; closed-immersion base
   change (lem-weil-pbc-proper-fp-permanence (b)) makes this a closed subscheme of
   Spec κ(h). The preceding lift makes it nonempty. A proper ideal of a field is
   zero, so the canonical projection is an isomorphism. By def-pc-scheme-fibre
   its sole point gives the unique `w` over `h`. The residue maps split the identity
   of κ(h); injectivity of field maps shows that both maps are isomorphisms.
4. Use the universal property in def-pc-fibre-product: retain the `X` and `V`
   components to construct `kX` and `aV`, and recover the `S'` component using `j`.
   The same construction with `Y` uses `τ = j ≫ lam`. The resulting comparison maps
   are inverse isomorphisms by uniqueness, giving `eX`, `eY` and their projection
   equations, including all triangles over `S` and `V`.
5. By lem-weil-pbc-etale-scheme-base-change the restricted legs are étale, as is
   `X ×[S] V → X`. Compose using lem-weil-pbc-etale-composition-cancellation (2).
   The projection equations give the images of `w` and `τ(v) = lam(s')`. Finally,
   residue-field functoriality (def-weil-residue-field) identifies the map from
   κ(x) to κ(w) with the composite of the three stipulated isomorphisms. -/
theorem Smooth.exists_pointed_span_etale_slice
    {X Y S T S' H : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ T)
    (q : S' ⟶ S) (lam : S' ⟶ T) [Smooth q]
    (s' : S') (hs : IsIso (q.residueFieldMap s'))
    (r : H ⟶ S') (a : H ⟶ pullback f q) (c : H ⟶ pullback g lam)
    [Etale a] [Etale c]
    (ha : a ≫ pullback.snd f q = r) (hc : c ≫ pullback.snd g lam = r)
    (h : H) (hh : r h = s')
    (hx : IsIso ((pullback.fst f q).residueFieldMap (a h)))
    (haκ : IsIso (a.residueFieldMap h)) (hcκ : IsIso (c.residueFieldMap h)) :
    ∃ (O : S'.Opens) (V : Scheme.{u}) (i : V ⟶ O.toScheme) (v : V)
      (j : V ⟶ S') (qV : V ⟶ S) (τ : V ⟶ T),
      s' ∈ O ∧ IsClosedImmersion i ∧ j = i ≫ O.ι ∧ qV = j ≫ q ∧ τ = j ≫ lam ∧
      j v = s' ∧ Etale qV ∧ IsIso (qV.residueFieldMap v) ∧
      qV ⁻¹' {q s'} = {v} ∧
      ∃ (kX : pullback f qV ⟶ pullback f q) (kY : pullback g τ ⟶ pullback g lam),
        kX ≫ pullback.fst f q = pullback.fst f qV ∧
        kX ≫ pullback.snd f q = pullback.snd f qV ≫ j ∧
        kY ≫ pullback.fst g lam = pullback.fst g τ ∧
        kY ≫ pullback.snd g lam = pullback.snd g τ ≫ j ∧
        ∃ (aV : pullback r j ⟶ pullback f qV) (cV : pullback r j ⟶ pullback g τ),
          aV ≫ pullback.fst f qV = pullback.fst r j ≫ a ≫ pullback.fst f q ∧
          aV ≫ pullback.snd f qV = pullback.snd r j ∧
          cV ≫ pullback.fst g τ = pullback.fst r j ≫ c ≫ pullback.fst g lam ∧
          cV ≫ pullback.snd g τ = pullback.snd r j ∧
          ∃ (eX : pullback r j ≅ pullback a kX) (eY : pullback r j ≅ pullback c kY),
            eX.hom ≫ pullback.fst a kX = pullback.fst r j ∧
            eX.hom ≫ pullback.snd a kX = aV ∧
            eY.hom ≫ pullback.fst c kY = pullback.fst r j ∧
            eY.hom ≫ pullback.snd c kY = cV ∧
            IsIso ((pullback.fst r j).fiberToSpecResidueField h) ∧
            Etale aV ∧ Etale cV ∧ Etale (aV ≫ pullback.fst f qV) ∧
            (aV ≫ pullback.fst f qV) ≫ f = pullback.snd r j ≫ qV ∧
            ∃ (w : ↥(pullback r j : Scheme.{u})),
              (pullback.fst r j) ⁻¹' {h} = {w} ∧
              IsIso ((pullback.fst r j).residueFieldMap w) ∧
              (aV ≫ pullback.fst f qV) w = (pullback.fst f q) (a h) ∧
              (pullback.snd r j) w = v ∧ τ v = lam s' ∧
              IsIso ((aV ≫ pullback.fst f qV).residueFieldMap w) := by
  sorry

end AlgebraicGeometry
