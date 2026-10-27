module

public import Sheaf.SecSmoothPurity.NestedAffineFormulaData

import Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs
import Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping
import Sheaf.SecSmoothPurity.NestedAffineChartFormulas
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-! # Nested affine chart orientations

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, proof (1)
(blueprint: lem-sp-nested-affine-orientation).

The equations are in canonical ordinary-etale coordinates for the ordinary
constant-coefficient pro-etale category. Exact finite site comparison, together
with its tensor, pullback and exceptional comparisons, identifies these equations
with the displayed pro-etale equations. Every arrow below is constructed from
these recorded comparisons, never supplied as an independent orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.NestedAffine

attribute [local irreducible] twistPull gammaUnit gamma source orientation tensorRoute
  total iterated chartPull zeroSource

set_option maxRecDepth 4096

/-- Nested chart orientations equal the ordered affine composites.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, proof (1)
(blueprint: lem-sp-nested-affine-orientation).

Proof:
1. Form the Cartesian affine-projection square over v. Its base-change map b and
   k=bu are etale. All schemes and opens are Noetherian and finite type over k;
   their separated morphisms have compactifications. Preservation and etale
   chart-domain results put G_p R and all intermediate inputs in Dctf.
2. Projection-purity-agreement identifies each Gamma with the smooth purity map.
   Expanding that map gives theta(1 tensor a); its unit case gives a=Gamma_R.
3. Restrict f,g,h to the three opens. Target-open base change, sigma locality and
   chart exceptional-mate coherence identify their orientations with the affine
   ones. The total coordinate chart gives the first displayed identity.
4. Apply the etale Cartesian tower tensor comparison to (q,p,v,u,b,k). Its two
   factors identify the restricted tensor of orientations with the pullback of
   the affine tensor map. The same normalized compositor is used on both sides.
5. Factor the tensor of the two affine orientations; the Gamma normalization
   identifies the resulting tensor mate with the displayed iterated integration.
6. For positive ranks apply affine-space purity composition. For an empty block
   apply ordered adjoint-tower regrouping with its identity endpoint. The even
   block swap has sign (-1)^(4de)=1. Both zero gives the unit identity.
7. Pull this affine equality back along k and substitute the two chart formulas.
   The two arrows now agree in exactly the common target used in Statement.
-/
theorem nested_affine_orientation
    (P : PurityFiniteSetting.{u}) (_hE : P.extension = ⊥)
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
    Statement P _hE d e f g aZ S V U hV hU v u hv hu := by
  let := P.noetherian aZ
  let := P.noetherian (g ≫ aZ)
  let := P.noetherian (f ≫ g ≫ aZ)
  let := P.finiteComparedInvertibleExponent aZ
  let := Dnc.compactifiable P g aZ
  have hg := Etale.constructibleFiniteTor_rightDerivedUpperShriek P.Coefficient aZ g
    (P.chartCoefficientUnit_finiteTor Z)
  have hf := Etale.constructibleFiniteTor_leftDerivedUpperStar
    (ModuleCat.{u + 1} P.Coefficient) f hg
  have hn := nested_affine_normalized_inputs P
  have hc := nested_affine_chart_formulas P _hE hn d e f g aZ S V U hV hU v u hv hu
  have hs : (-1 : ℤ) ^ ((2 * d) * (2 * e)) = 1 :=
    ((even_two_mul d).mul_right (2 * e)).neg_one_pow
  dsimp only [Statement]
  intro N
  dsimp only at hc
  obtain ⟨hl, hr⟩ := hc N
  have ha := nested_affine_integration_regrouping P S.toScheme (S.ι ≫ aZ) d e N
  refine And.intro hl ?_
  refine And.intro hr ?_
  refine And.intro ha ?_
  refine And.intro ?_ ?_
  · rw [ha]
  refine And.intro ?_ ⟨hn, hg, hf, hs⟩
  rw [ha] at hl
  exact hl.trans hr.symm

end WeilConjectures.PurityFiniteSetting.NestedAffine
