/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-! # Ordinary semilinear squares under the canonical module pullback comparison

For a unital morphism `a : R ⟶ T` of commutative condensed rings and a scheme morphism
`f : X ⟶ S`, a square of semilinear module maps `v, w, p, q` whose underlying sheaf square
commutes (after the specified adjunction transposes of `p` and `q`) commutes as a square of
module maps through the canonical comparison `comapUpperStarIso a f`.

Source: blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), final sentence: coefficient
functors commute with pullback; ordinary module boundary of the coefficient-unit square.
(blueprint: lem-sfb-ordinary-semilinear-pullback-square)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ordinary semilinear pullback square for module morphisms.  The hypothesis is
transported through the specified underlying sheaf adjunction transposes, and the
conclusion uses the canonical coefficient comparison `comapUpperStarIso`.

Source: blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), final sentence.
(blueprint: lem-sfb-ordinary-semilinear-pullback-square)

Proof (from the node; composition written left to right with `;`):
1. Expand the composed adjunction `upperStarLowerStarAdjunction` by
   `upperStarLowerStarAdjunction_homEquiv_hom` and apply the inverse sheaf bijection to the
   unit formula of `f⁻¹ ⊣ f_*`: `p♭ = upperStarUnitHom R f M; p` and
   `q♭ = upperStarUnitHom T f N; q` (def-sfb-module-upper-lower-adjunction,
   def-sfb-modobj-extend-restrict-adjunction).
2. Maps out of an extension of scalars are determined by their composite with its unit
   (`Mod.hom_ext_of_extendUnitHom`, applied to `mapMod(f⁻¹) M` and `condensedPullbackHom R f`).
   So it suffices to compare `upperStarUnitHom R f M; L` and `upperStarUnitHom R f M; H` for
   `L = G_R(v); σ_N⁻¹; V_X(q)` and `H = p; w`.
3. Naturality of the unit (`upperStarUnitHom_map_hom`) gives
   `upperStarUnitHom R f M; G_R(v) = F(v); upperStarUnitHom R f (V_S N)`, and the normalized
   comparison identity `upperStarUnitHom_comapUpperStarIso_inv_app_hom` gives
   `upperStarUnitHom R f (V_S N); σ_N⁻¹ = upperStarUnitHom T f N` on underlying arrows
   (def-sfb-comap-upper-star-iso, def-sfb-extend-comap-iso-of-iso).
4. Restriction leaves underlying arrows unchanged, so by steps 1 and 3 the two sides become
   `F(v); q♭` and `p♭; w`, which the hypothesis equates. No flatness of `a` and no
   invertibility of `v, w, p, q` is used. -/
theorem ordinarySemilinearPullbackSquare
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj R S))
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj T S))
    (M' : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X))
    (N' : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj T X))
    (v : M ⟶ (Mod.comap (coefficientMap a S)).obj N)
    (w : M' ⟶ (Mod.comap (coefficientMap a X)).obj N')
    (p : (upperStar R f).obj M ⟶ M')
    (q : (upperStar T f).obj N ⟶ N')
    (h : (f)^*[Ab.{u + 1}].map v.hom ≫
        ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv
          N.X N'.X).symm
          ((upperStarLowerStarAdjunction T f).homEquiv N N' q).hom =
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv
          M.X M'.X).symm
          ((upperStarLowerStarAdjunction R f).homEquiv M M' p).hom ≫ w.hom) :
    (upperStar R f).map v ≫
        (comapUpperStarIso a f).inv.app N ≫
        (Mod.comap (coefficientMap a X)).map q =
      p ≫ w := by
  have hp :
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv
        M.X M'.X).symm
        ((upperStarLowerStarAdjunction R f).homEquiv M M' p).hom =
      upperStarUnitHom R f M ≫ p.hom := by
    apply ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv
      M.X M'.X).injective
    rw [Equiv.apply_symm_apply, upperStarLowerStarAdjunction_homEquiv_hom,
      Adjunction.homEquiv_unit]
  have hq :
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv
        N.X N'.X).symm
        ((upperStarLowerStarAdjunction T f).homEquiv N N' q).hom =
      upperStarUnitHom T f N ≫ q.hom := by
    apply ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv
      N.X N'.X).injective
    rw [Equiv.apply_symm_apply, upperStarLowerStarAdjunction_homEquiv_hom,
      Adjunction.homEquiv_unit]
  rw [hp, hq] at h
  apply Mod.hom_ext_of_extendUnitHom (condensedPullbackHom R f)
  change upperStarUnitHom R f M ≫ _ = upperStarUnitHom R f M ≫ _
  simp only [Mod.comp_hom', Mod.comap_map_hom]
  rw [upperStarUnitHom_map_hom_assoc,
    upperStarUnitHom_comapUpperStarIso_inv_app_hom_assoc]
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
