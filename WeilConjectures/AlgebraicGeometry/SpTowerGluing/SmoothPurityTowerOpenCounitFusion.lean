/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerOriginalCoverMaps

/-! # Fusion of a nested-open counit and compact-support open composition

Source: latest smooth-purity blueprint, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The nested-open adjunction mate and the compact-support open compositor
have the same actual counit normalization.
Source: latest smooth-purity blueprint, Gluing, compatibility of the local counits
with nested open extensions (blueprint: lem-sp-tower-open-counit-fusion).

Proof. Work first in the ordinary section-normalized categories. Recover the ordinary
composition normalization from comp_termwise and comp_evaluation on complexes
concentrated in degree zero. Full faithfulness of the degree-zero embedding and
joint faithfulness of ordinary level evaluations identify ordinaryComp with the
canonical geometric compositor. Thus its triple-open associativity is the actual
ordinary inverse-image associativity; no faithfulness of derived evaluations is used.
The two extensions
by zero compose by the unique left-adjoint comparison to ordinaryComp. The equation
leftAdjointUniq_hom_app_counit identifies the counit of that composite adjunction
with the direct open counit, with the specified pullback compositor. Apply the
exact derived functor construction to this equation. The fields comp_termwise,
unit_termwise and counit_termwise identify the derived comparison and both sides
with the recorded derived open adjunctions; composition comparisons for derived
exact functors cancel. Transport through the three section-preserving realization
equivalences. Cancel their intermediate counit isomorphisms and triangle identities.
Naturality moves the arbitrary local isomorphism e and its compact-support image
through the comparison. Whisker the resulting equality with the proper pushforward
in c, and then with epsU. After the equality of nested and composite open maps,
these are precisely originalOpenAlpha, originalOpenCounit and normalizedOpenCounit
in the displayed formula. This is a universal equality for one chain of opens:
it needs no cover, constructibility, descent, representability, or target counit
on H. It does not infer an equality of derived morphisms from level evaluations. -/
theorem tower_open_counit_fusion
    {X Y U W : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (j : U ⟶ X) (a : W ⟶ U) (i : W ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a] [IsOpenImmersion i]
    (w : a ≫ j = i)
    (H : spDerivedCoefficientTowers l E X (q.abelian X))
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y))
    (HU : spDerivedCoefficientTowers l E U (q.abelian U))
    (e : (SpTowerCalculus.etalePullback l E b o q j).obj H ≅ HU)
    (epsU : (SpTowerCalculus.F l E b o q (c.precomp j)).obj HU ⟶ K) :
    (SpTowerCalculus.F l E b o q c).map
        (originalOpenAlpha l E b o q a j i w H) ≫
      originalOpenCounit l E b o q c j H K HU e epsU =
    (SpTowerCalculus.openComposition l E b o q i c).hom.app _ ≫
      (SpTowerCalculus.F l E b o q (c.precomp i)).map
        ((originalRestrictionComp l E b o q a j i w).inv.app H ≫
          (SpTowerCalculus.etalePullback l E b o q a).map e.hom) ≫
      normalizedOpenCounit l E b o q c j a i w HU K epsU := by sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
