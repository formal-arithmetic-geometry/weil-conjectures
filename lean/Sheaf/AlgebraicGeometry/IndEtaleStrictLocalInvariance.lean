/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing

/-! # Ind-etale invariance of strict localizations

Source: Stacks Project, Tags 05WR and 0GIP
(blueprint: lem-trf-ind-etale-strict-local-invariance).
This module records the full strict-local, base-change, and structural-map clauses.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- An ind-etale morphism induces the canonical strict-local isomorphism at every geometric
point, compatibly with arbitrary scheme base change and with the structural map.
Source: Stacks Project, Tags 05WR and 0GIP.
(blueprint: lem-trf-ind-etale-strict-local-invariance).
Proof steps:
1. Choose affine charts around the source and target points. The strict-henselization limit
   construction and functoriality give strictly henselian local rings, the structural square,
   and the canonical local homomorphism whose residue map is the inclusion of separable closures.
2. The affine-chart ind-etale lemma makes both strict-henselization rings ind-etale over the
   target affine ring. Stability under composition and relative maps makes the canonical local
   homomorphism weakly etale.
3. Olivier's theorem for a weakly etale map from a strictly henselian local ring makes this
   homomorphism an isomorphism. Its spectrum is the required canonical isomorphism over the base,
   and the residue compatibility is exactly the displayed evaluation equation.
4. After an arbitrary base change, intersect the inverse images of the chosen affine charts and
   identify the resulting affine open with the tensor-product fibre-product chart. Ind-etaleness
   is stable under this base change, so steps 1--3 apply to every resulting geometric point.
5. For the structural map localized at its closed geometric point, put
   `s̃ = Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barS))`. The same
   argument applies to `s̃` and `strictHenselizationStructuralMap barS`; the canonical map
   `strictHenselizationMap (strictHenselizationStructuralMap barS) s̃` is therefore an
   isomorphism (and has the two canonical structural and evaluation equations).
-/
theorem indEtale_strictLocal_invariance
    {S T : Scheme.{u}} (u : T ⟶ S)
    (hlocal : ∀ (t : T), ∃ (V : T.Opens) (U : S.Opens),
      t ∈ V ∧ IsAffine V.toScheme ∧ IsAffine U.toScheme ∧
      ∃ e : V.toScheme ⟶ U.toScheme,
        e ≫ U.ι = V.ι ≫ u ∧ proAffineEtale e) :
    ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (barT : Spec (.of Ω) ⟶ T) (barS : Spec (.of Ω) ⟶ S)
      (hbar : barS = barT ≫ u),
      ∃ e : strictHenselizationScheme barT ≅ strictHenselizationScheme barS,
        e.hom ≫ strictHenselizationStructuralMap barS =
          strictHenselizationStructuralMap barT ≫ u ∧
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barT)) ≫ e.hom =
          Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barS)) ∧
        (∀ (S' : Scheme.{u}) (g : S' ⟶ S)
          {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
          (barT' : Spec (.of Ω') ⟶ pullback u g),
          ∃ e' : strictHenselizationScheme barT' ≅
              strictHenselizationScheme (barT' ≫ pullback.snd u g),
            e'.hom ≫ strictHenselizationStructuralMap (barT' ≫ pullback.snd u g) =
              strictHenselizationStructuralMap barT' ≫ pullback.snd u g ∧
            Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barT')) ≫
                e'.hom =
              Spec.map (CommRingCat.ofHom
                (strictHenselizationPointEvaluation (barT' ≫ pullback.snd u g)))) ∧
        IsIso (strictHenselizationMap (strictHenselizationStructuralMap barS)
          (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barS)))) := by
  sorry

end AlgebraicGeometry.Scheme
