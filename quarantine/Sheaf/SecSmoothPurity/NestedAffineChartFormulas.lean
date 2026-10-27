module

public import Sheaf.SecSmoothPurity.NestedAffineFormulaData

/-! # The two chart restriction formulas before regrouping

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, proof (1).
(blueprint: lem-sp-nested-affine-chart-formulas).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.NestedAffine

/-- The two chart restriction formulas before regrouping.

Source: composition-factors proof (1).
(blueprint: lem-sp-nested-affine-chart-formulas).

Proof:
1. Restrict f, g and their composite to U, V and S. Target-open base change
   for orientations and dualizing sigma locality identify the specified r with
   the canonical restriction of the dualizing object. Source-etale chart mate
   coherence preserves these restrictions and the exceptional compositor.
2. The total chart is k = ut followed by affineTraceMap vt d. The actual affine
   square is Cartesian, its base-change map is etale, and chartComposite gives
   its equation over the composite. Apply diagonalOrientationCharts to this
   total chart, invert its orientation equation, and use hn at rank d+e.
   This gives lhs = chartPull total, with the blockEq transport in total.
3. Apply etale_cartesian_tower_tensor_comparison to q, p, vt, ut, b and k.
   Only the square with b and vt is Cartesian. Its first factor is the pullback
   of the q-orientation by orientation base change; its second factor is the
   pullback of the p-orientation by the v chart equation. This identifies rhs
   with the pullback of the affine tensor route, with the very same compositor.
4. Use hn first at the coefficient unit for p, then at H = omega_p for q.
   Its finite-Tor assertion permits this input. Factor the tensor of the two
   orientations into (q^* gammaUnit tensor identity), then
   (identity tensor gammaUnit). Tensor functoriality and the hn equation for
   gamma identify the latter factor followed by theta with gamma at omega_p.
   The result is exactly chartPull iterated. All comparisons are the canonical
   ones, so the zero ranks and empty charts retain their existing unit constraints.
-/
theorem nested_affine_chart_formulas
    (P : PurityFiniteSetting.{u}) (_hE : P.extension = ⊥)
    (hn : NormalizedInputs P)
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k))
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (S : Z.Opens) (V : Y.Opens) (U : X.Opens)
    [IsAffine S.toScheme] [IsAffine V.toScheme] [IsAffine U.toScheme]
    (hV : V ≤ g ⁻¹ᵁ S) (hU : U ≤ f ⁻¹ᵁ V)
    (v : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin e)) S.toScheme)
    (u : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme)
    [Etale v] [Etale u]
    (hv : (v ≫ (affineTraceAffineSpaceIso S.toScheme e).inv) ≫
      affineTraceProjection S.toScheme e = g.resLE S V hV)
    (hu : (u ≫ (affineTraceAffineSpaceIso V.toScheme d).inv) ≫
      affineTraceProjection V.toScheme d = f.resLE V U hU) :
  letI := P.noetherian aZ
  letI := P.noetherian (g ≫ aZ)
  letI := P.noetherian (f ≫ g ≫ aZ)
  letI := isNoetherian_of_locallyOfFiniteType S.ι
  letI := isNoetherian_of_locallyOfFiniteType V.ι
  letI := isNoetherian_of_locallyOfFiniteType U.ι
  letI := affineTraceNoetherian S.toScheme e
  letI := affineTraceNoetherian (affineTraceTower S.toScheme e) d
  letI : SmoothOfRelativeDimension (d + e) (f ≫ g) :=
    smoothOfRelativeDimension_comp (n := d) (m := e) f g
  letI := Dnc.compactifiable P f (g ≫ aZ)
  letI := Dnc.compactifiable P g aZ
  letI := Dnc.compactifiable P (f ≫ g) aZ
  let fU := f.resLE V U hU
  let gV := g.resLE S V hV
  let h0 := fU ≫ gV
  let vt := v ≫ (affineTraceAffineSpaceIso S.toScheme e).inv
  let ut := u ≫ (affineTraceAffineSpaceIso V.toScheme d).inv
  let k := ut ≫ affineTraceMap vt d
  letI : Etale (affineTraceMap vt d) := mapEtale vt d
  letI : Etale k := inferInstance
  let wk := chartComposite d e ut vt fU gV hu hv
  letI : IsSeparated
      (k ≫ (affineTraceProjection (affineTraceTower S.toScheme e) d ≫
        affineTraceProjection S.toScheme e)) := wk.symm ▸ inferInstanceAs (IsSeparated h0)
  letI := IsSeparated.of_comp k
    (affineTraceProjection (affineTraceTower S.toScheme e) d ≫
      affineTraceProjection S.toScheme e)
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ g ≫ aZ⟩
  letI : Z.Over (Spec (.of P.field.k)) := ⟨aZ⟩
  letI : U.toScheme.Over (Spec (.of P.field.k)) := ⟨U.ι ≫ f ≫ g ≫ aZ⟩
  letI : S.toScheme.Over (Spec (.of P.field.k)) := ⟨S.ι ≫ aZ⟩
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ g ≫ aZ))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ g ≫ aZ))
  letI : LocallyOfFiniteType (Z ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aZ)
  letI : QuasiCompact (Z ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aZ)
  letI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ f ≫ g ≫ aZ))
  letI : QuasiCompact (U.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (U.ι ≫ f ≫ g ≫ aZ))
  letI : LocallyOfFiniteType (S.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (S.ι ≫ aZ))
  letI : QuasiCompact (S.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (S.ι ≫ aZ))
  letI : (f ≫ g).IsOver (Spec (.of P.field.k)) := ⟨by
      change (f ≫ g) ≫ aZ = f ≫ g ≫ aZ
      simp [Category.assoc]⟩
  letI : U.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : S.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : h0.IsOver (Spec (.of P.field.k)) :=
    ⟨by
      change h0 ≫ (S.ι ≫ aZ) = U.ι ≫ f ≫ g ≫ aZ
      simp [h0, fU, gV, Category.assoc]⟩
  let sq : CommSq U.ι h0 (f ≫ g) S.ι :=
    ⟨by simp [h0, fU, gV, Category.assoc]⟩
  ∀ N : Etale.EtaleCompactSupportNormalization P.Coefficient,
    let r :=
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).mapIso
        (NestedAffineCoordinates.chartDualizingUnit P (f ≫ g)).symm ≪≫
      ProEtale.DualizingLocality.restriction P (f ≫ g) h0 U.ι S.ι sq ≪≫
      NestedAffineCoordinates.chartDualizingUnit P h0
    let lhs := (twistPull P U.ι (f ≫ g ≫ aZ) (d + e)).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).map
        (orientation P (d + e) (f ≫ g) aZ) ≫ r.hom
    let rhs := (twistPull P U.ι (f ≫ g ≫ aZ) (d + e)).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).map
        (tensorRoute P d e f g aZ ≫
          (finiteExceptionalComposition P.Coefficient f g).inv.app
            (Etale.ordinaryFiniteUnit P.Coefficient Z)) ≫ r.hom
    let aff := chartPull P S.toScheme (S.ι ≫ aZ) d e k h0 wk N
      (total P S.toScheme (S.ι ≫ aZ) d e N)
    let it := chartPull P S.toScheme (S.ι ≫ aZ) d e k h0 wk N
      (iterated P S.toScheme (S.ι ≫ aZ) d e)
    lhs = aff ∧ rhs = it := by sorry


end WeilConjectures.PurityFiniteSetting.NestedAffine
