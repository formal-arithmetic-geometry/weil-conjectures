/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
import WeilConjectures.AlgebraicGeometry.DominantAffineChartData
import WeilConjectures.AlgebraicGeometry.AffineLocalDimensionTermComparison
import WeilConjectures.RingTheory.AffineDimensionInequality

/-!
# Local dimension inequality for an integral dominant morphism

Source: literature/stacks-project/morphisms.tex, Tag 02JU, lemma-dimension-formula;
the inequality clause (blueprint: lem-trf-local-dimension-formula).

## Main statement

The local Krull dimension inequality is stated for a locally finite type dominant
morphism between integral schemes over a locally Noetherian base.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option warn.classDefReducibility false in
/--
The algebra structure on function fields induced by a dominant morphism: the existing
function-field map `Scheme.Hom.functionFieldMap` (the stalk map at the generic point),
for the equality that a dominant morphism sends the generic point of the source to the
generic point of the target.
Source: literature/stacks-project/morphisms.tex, Tag 02JU, proof of
lemma-dimension-formula (blueprint: lem-trf-local-dimension-formula).
-/
def Scheme.Hom.dominantFunctionFieldAlgebra
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [IsDominant f] : Algebra S.functionField X.functionField :=
  let h : f (genericPoint X) = genericPoint S := by
    refine ((genericPoint_spec S).eq ?_).symm
    have hi := (genericPoint_spec X).image f.continuous
    rw [Set.image_univ, f.denseRange.closure_range] at hi
    exact hi
  (f.functionFieldMap h).hom.toAlgebra

/--
For a locally Noetherian base, a locally finite type dominant morphism between
integral schemes satisfies the local dimension inequality
`dim O_{X,x} ≤ dim O_{S,f(x)} + trdeg_{R(S)} R(X) - trdeg_{κ(f(x))} κ(x)`, stated in the
additive form `dim O_{X,x} + trdeg_{κ(f(x))} κ(x) ≤ dim O_{S,f(x)} + trdeg_{R(S)} R(X)`.
Source: literature/stacks-project/morphisms.tex, Tag 02JU, lemma-dimension-formula;
the inequality clause (blueprint: lem-trf-local-dimension-formula).

Proof: choose affine neighbourhoods of `f x` and `x` with Noetherian base
ring and finite type domain upstairs; identify the local rings, generic stalks,
and residue fields with the corresponding localizations, fraction fields, and
residue fields.  Apply the affine dimension inequality of Tag 02IJ and the
localization-height identification, then use the domain transcendence-degree
tower identity to identify the generic term.  The cited statements are
`lem-trf-affine-dimension-inequality`,
`lem-weil-pbc-affine-open-spec-points`,
`lem-weil-pbc-affine-open-stalk-localization`,
`lem-weil-pbc-lft-affine-pairs`,
`lem-weil-pbc-localization-dimension-chains-below-prime`, and
`lem-exc-domain-transcendence-degree-tower`, together with the definition
nodes for integral schemes, generic points, residue fields, transcendence degree,
and Krull dimension.
-/
theorem local_dimension_formula
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [IsDominant f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) +
        (Cardinal.toENat
          (@Algebra.trdeg (S.residueField (f x)) (X.residueField x) _ _
            (f.residueFieldMap x).hom.toAlgebra) : WithBot ℕ∞) ≤
      ringKrullDim (S.presheaf.stalk (f x)) +
        (Cardinal.toENat
          (@Algebra.trdeg S.functionField X.functionField _ _
            (Scheme.Hom.dominantFunctionFieldAlgebra f)) : WithBot ℕ∞) := by
  obtain ⟨U, V, hV, hVU, _, hx, _, _, hN, hA, hB, hft, hinj, _⟩ :=
    dominant_affine_chart_data f f.denseRange
      (fun U : S.affineOpens ↦ (U : S.Opens)) (fun U ↦ U.property)
      (fun U ↦ IsLocallyNoetherian.component_noetherian U)
      (iSup_affineOpens_eq_top S) x
  let y : V := ⟨x, hx⟩
  let p := U.property.primeIdealOf ⟨f x, hVU hx⟩
  let q := hV.primeIdealOf y
  obtain ⟨hc, eS, eX, _, _, _, hdimS, hdimX, rS, rX, _, _, _, hres, hgen⟩ :=
    affine_local_dimension_term_comparison f U U.property V hV hVU y p q rfl rfl
  let : IsNoetherianRing Γ(S, U) := hN
  let : IsDomain Γ(S, U) := hA
  let : IsDomain Γ(X, V) := hB
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra.FiniteType Γ(S, U) Γ(X, V) := hft
  have h := Ideal.height_add_trdeg_residueField_le hinj p.asIdeal q.asIdeal hc
  rw [hdimX, hdimS, hres]
  change (q.asIdeal.height : WithBot ℕ∞) + _ ≤
    (p.asIdeal.height : WithBot ℕ∞) +
      (Cardinal.toENat
        (@Algebra.trdeg S.functionField X.functionField _ _
          (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra) : WithBot ℕ∞)
  rw [← hgen]
  exact_mod_cast h

end AlgebraicGeometry
