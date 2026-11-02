/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.DeligneLaumon.CondensedFiniteEtale.CondensedFiniteEtaleStalkCycles
import WeilConjectures.SixFunctors.Finite.Stalk

/-! # Purity under finite etale pushforward

Source: latest blueprint,
part-weights-riemann-hypothesis/sec-deligne-laumon-a1/sec-arbitrary-curves/
sk-lem-wft-finite-map,
`lem-a1-finite-map-purity` (blueprint: lem-a1-finite-map-purity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.CondensedWeil

/-- The canonical Weil module obtained by finite etale direct image.
Source: the finite etale pushforward in the blueprint
(blueprint: lem-a1-finite-map-purity). -/
noncomputable def finiteEtaleLowerStar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (g₀ : X₀ ⟶ Y₀) [IsFinite g₀.left]
    (M : NativeL2.WeilModule D l X₀) : NativeL2.WeilModule D l Y₀ :=
  Endofunctor.IsoAlgebra.mk
    (CondensedFiniteEtale.directImage D l g₀ M.carrier)
    (CondensedFiniteEtale.directImageWeil D l g₀
      (by
        let := Fintype.ofFinite D.k₀
        apply pullback.hom_ext
        · simp only [Category.assoc, CondensedFiniteEtale.geometricMap,
            Over.pullback_map_left, pullback.lift_fst]
          simp only [← Category.assoc, FiniteFieldDatum.geometricFrobenius]
          rw [(D.galoisMap_projections _ _).1]
          rw [Category.assoc, (D.galoisMap_projections _ _).1]
          simp only [pullback.lift_fst]
        · simp only [Category.assoc, CondensedFiniteEtale.geometricMap,
            Over.pullback_map_left, pullback.lift_snd]
          simp only [FiniteFieldDatum.geometricFrobenius]
          rw [(D.galoisMap_projections _ _).2]
          rw [(D.galoisMap_projections _ _).2]
          rw [← Category.assoc, pullback.lift_snd]) M.carrier M.str)

/-- A finite etale direct image preserves punctual purity of the source Weil module.
Source: latest blueprint,
part-weights-riemann-hypothesis/sec-deligne-laumon-a1/sec-arbitrary-curves/
sk-lem-wft-finite-map,
`lem-a1-finite-map-purity.proof.md` (blueprint: lem-a1-finite-map-purity).
Proof: fix a closed target point y and a geometric lift. The finite-stalk formula
(lemma-weil-pbc-finite-stalk-formula) supplies the finite-sum shape, and the condensed
refinement lem-a1-condensed-finite-etale-stalk-cycles identifies this stalk with the
sum of source stalks, grouped into Frobenius-stable blocks indexed by closed points x.
Each block has residue degree e >= 1 and its e-th return is the local operator at x.
For a nonzero eigenvector of eigenvalue lambda, choose a nonzero block component and
then a nonzero stalk component in that block. The return equation makes this component
an eigenvector of the source local operator with eigenvalue lambda^e. Source purity
(def-weil-punctual-weights) gives the norm of iota(lambda^e) as q_x^(w/2). The residue
cardinality relation q_x = q_y^e therefore gives
|iota(lambda)|^e = (q_y^(w/2))^e. Since q_y > 0 and e >= 1, injectivity of the e-th
power on nonnegative reals gives the required norm. This holds for every closed y,
every geometric lift and every eigenvalue. Empty fibres and zero stalks contribute
no eigenvalues; no diagonalizability is needed.
-/
theorem pure_finiteEtaleLowerStar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (g₀ : X₀ ⟶ Y₀) [IsFinite g₀.left] [Etale g₀.left]
    (M : NativeL2.WeilModule D l X₀)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (hpure : NativeL2.Pure D l X₀ M iota w) :
    NativeL2.Pure D l Y₀ (finiteEtaleLowerStar D l hl g₀ M) iota w := by
  sorry

end WeilConjectures.CondensedWeil
