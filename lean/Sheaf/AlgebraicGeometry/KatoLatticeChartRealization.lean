/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogDifferentialStalk
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.TraceFormula.FgCommutativeMonoidFinitePresentation
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.LfpUniqueInfinitesimalLiftsEtale
import Sheaf.AlgebraicGeometry.PointedEtaleStalk

/-!
# Kato's prescribed lattice chart

Source: Illusie--Laszlo--Orgogozo, Exposé XVI, Proposition 3.6.3 proof,
printed p.252; Kato, Theorem 3.5 (blueprint: lem-per-kato-lattice-chart-realization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The subgroup of the logarithmic stalk group represented by strict-local units.
Source: ILO XVI, Proposition 3.6.3 proof, p.252
(blueprint: lem-per-kato-lattice-chart-realization). -/
noncomputable def EtaleLogHom.stalkUnitSubgroup
    {X Y : FineSaturatedLogScheme.{u}} (_f : EtaleLogHom X Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme) :
    Subgroup (Algebra.GrothendieckGroup (X.logStructure.toEtalePrelogStructure.stalk x)) :=
  Subgroup.map
    ((Algebra.GrothendieckGroup.of (M := X.logStructure.toEtalePrelogStructure.stalk x)).comp
      (X.logStructure.unitsIn x)) ⊤

/-- The inverse-image monoid used by Kato's chart construction.
Source: ILO XVI, Proposition 3.6.3 proof, p.252
(blueprint: lem-per-kato-lattice-chart-realization). -/
noncomputable def EtaleLogHom.inverseImageMonoid
    {X Y : FineSaturatedLogScheme.{u}} (_f : EtaleLogHom X Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme)
    {G : Type u} [CommGroup G] (h : G →* Algebra.GrothendieckGroup
      (X.logStructure.toEtalePrelogStructure.stalk x)) : Submonoid G :=
  { carrier := {g | ∃ m : X.logStructure.toEtalePrelogStructure.stalk x, h g =
      Algebra.GrothendieckGroup.of m}
    one_mem' := ⟨1, by simp⟩
    mul_mem' := by
      intro a b ha hb
      obtain ⟨ma, hma⟩ := ha
      obtain ⟨mb, hmb⟩ := hb
      exact ⟨ma * mb, by rw [map_mul, hma, hmb, map_mul]⟩ }

/-- Prescribed-lattice realization of a logarithmic chart. Source: ILO XVI,
Proposition 3.6.3 proof, printed p.252; Kato, Theorem 3.5
(blueprint: lem-per-kato-lattice-chart-realization).

Proof (the ten steps of the node):
1. Choose an fs chart `R` at `x` and the face `F` mapping to strict-local units.
A product in a local ring is a unit exactly when each factor is. The chart pushout
identifies the stalk with `R_F ⊕_{F^gp} Aˣ`. By `lem-trf-fs-face-sharpening`, its
characteristic monoid is the sharp fs monoid `R_F/F^gp`, with finite free group
`C = B/Aˣ`. The stalk is the full inverse image of that characteristic monoid in `B`:
a group element with the same characteristic as a monoid element differs by a unit.
2. Let `ρ : G → C` be the quotient of `h`, and `K = ker ρ`. Surjectivity allows
lifting a finite basis of `C`, giving a section `s` and `G = K ⊕ s(C)`. The subgroup
theorem `lem-weil-subgroup-finite-free-abelian-group-free` makes `K` finite free.
The inverse-image description gives the actual submonoid `P = K ⊕ s(Mbar)`.
3. Lift finite generators of `Mbar`, and adjoin both signs of a basis of `K`.
They generate `P`; integrality follows from its embedding in `G`. Saturation follows
by applying `ρ` and using saturation of `Mbar`. These generators generate all of `G`
as a group, so inclusion induces `P^gp ≃ G`. The extension equation gives
`h(i(0,q)) = f♭(q)`, so the prescribed element `i(0,q)` belongs to this very `P`.
4. The inverse image of `Aˣ` in `P` is `K = Pˣ`. The pushout map
`P ⊕_K Aˣ → M_x` is surjective by lifting characteristics and correcting by units.
If `h(p)v = h(p')v'`, their characteristics agree, hence `p' = p+k` for `k ∈ K`;
cancellation gives `v = h(k)v'`, exactly the pushout relation. Thus the given germ
`h|P` is a stalk chart, with no replacement of the germ.
5. Apply `lem-trf-fine-log-stalk-chart-spreading` to that stalk chart. The two
maps from `Q` have equal germs. Spread these equalities for finitely many generators
on one pointed refinement, so the fixed base chart is retained. The chart map into
the monoid spectrum, by `lem-weil-pbc-morphism-into-affine-scheme`, and the
fibre-product universal property give the comparison `c : W → Z`.
6. The sections `T_j` supplied by `i(e_j,0)` have germs `t_j`. By
`lem-per-log-smooth-infinitesimal-calculus`, logarithmic differentials are finite
locally free and have the prescribed stalk. Refine to a free frame, then invert the
determinant of the columns `dlog T_j`; the adjugate formula makes them a basis on
`W`. Spread the inverse of `n` and its defining equation as well. For `r = 0`,
the differential sheaf has rank zero and the empty determinant is `1`.
7. The same calculus makes `W → Y` locally finitely presented. Finite monoid
presentations (`lem-trf-fg-commutative-monoid-finite-presentation`) give the finite
presentation of `D = R ⊗_{ℤ[Q]} ℤ[P]` on an affine base. The monoid relations give
binomials, and generators of `Q` give the compatibility equations. If the source
algebra is `B = R[x]/(f)` and `y_j` generate `D`, represent their images by `b_j(x)`.
Then `B = D[x]/(f,y_j-b_j(x))`, so `c` is locally finitely presented.
8. Test `c` on an arbitrary affine square-zero immersion `T₀ → T` with ideal `I`.
Give `T` the log structure from its prescribed `P`-chart over `Z`, and restrict it to
`T₀`. By `lem-per-integral-chart-logification-thickening`, these are integral fine
log structures, the immersion is strict, and the map from `T₀` is a log morphism.
Log-smooth calculus gives an étale-local lift over `Y`. Its discrepancy from the
prescribed `P`-map is uniquely `1+ε(p)`, since integrality makes the `1+I` action
free. Square-zero multiplication makes `ε` additive; it extends to `G = P^gp`
and vanishes on `i(Q^gp)` because both maps are over `Y`.
9. The basis `dlog T_j` determines the log derivation with values
`-ε(i(e_j,0))`. Acting by it corrects the lift so its error vanishes on `i(L)`.
For every `g`, the quotient hypothesis gives `n^k g ∈ i(L)`. Thus `n^k ε(g)=0`,
and invertibility of `n` makes the corrected error zero. Agreement on `P` gives
agreement on all monomials of `ℤ[P]`, hence on `Z` by the affine-morphism and
fibre-product universal properties. This supplies étale-local ordinary lifts.
10. Two ordinary lifts over `Z` are log lifts over `Y` via the same `P`-chart.
Their difference derivation vanishes on the basis `dlog T_j`, hence is zero.
This uniqueness holds after every étale localization. The representable sheaf
lemma `lem-weil-pbc-small-etale-representable-presheaf-sheaf` glues the local lifts
of `T ×_Z W` uniquely. With step 7, the criterion
`lem-per-lfp-unique-infinitesimal-lifts-etale` proves `c` étale. Steps 3--5 give the
other conclusions, the prescribed germ, and the unchanged chart of `Y`.
-/
theorem kato_lattice_chart_realization
    {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    (hf : f.IsLogSmooth)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme)
    (q₀ : Type u) [CommMonoid q₀]
    (hq₀ : IsFineSaturatedMonoid q₀)
    (hq₀tors : IsMulTorsionFree (Algebra.GrothendieckGroup q₀))
    (chart₀ : q₀ →* Y.logStructure.monoidSheaf.obj.obj
      (op (Scheme.Etale.mk (𝟙 Y.scheme))))
    (chart₀_isChart : Y.logStructure.IsChart (Scheme.Etale.mk (𝟙 Y.scheme)) chart₀)
    {r : ℕ} (t : Fin r → X.logStructure.toEtalePrelogStructure.stalk x)
    (ht : ∃ b : Module.Basis (Fin r) (strictLocalRing X.scheme x)
      (f.LogDifferential x), ∀ j : Fin r, b j = f.logDLog x (t j))
    (n : ℕ) (hn : 0 < n)
    (hnunit : IsUnit (n : strictLocalRing X.scheme x))
    {G : Type u} [CommGroup G]
    (hGfree : ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ (Additive G)))
    (i : (Multiplicative (Fin r → ℤ) × Algebra.GrothendieckGroup q₀) →* G)
    (hi : Function.Injective i)
    (hquot : ∃ k : ℕ, ∀ g : G, g ^ (n ^ k) ∈ i.range)
    (h : G →* Algebra.GrothendieckGroup
      (X.logStructure.toEtalePrelogStructure.stalk x))
    (hhi : ∀ (a : Fin r → ℤ) (q : Algebra.GrothendieckGroup q₀),
      h (i (Multiplicative.ofAdd a, q)) =
        (∏ j : Fin r, Algebra.GrothendieckGroup.of (t j) ^ (a j)) *
          Algebra.GrothendieckGroup.lift
            ((Algebra.GrothendieckGroup.of).comp (f.baseChartGerm x chart₀)) q)
    (hsurj : Function.Surjective (fun g ↦
      QuotientGroup.mk' (f.stalkUnitSubgroup x) (h g))) :
    IsFineSaturatedMonoid (f.inverseImageMonoid x h) ∧
      (∃ e : Algebra.GrothendieckGroup (f.inverseImageMonoid x h) ≃* G,
        ∀ p, e (Algebra.GrothendieckGroup.of p) = p.1) ∧
      ∃ (hP : f.inverseImageMonoid x h →*
          X.logStructure.toEtalePrelogStructure.stalk x),
        (∀ p, Algebra.GrothendieckGroup.of (hP p) = h p.1) ∧
      ∃ (W : X.scheme.Etale) (w : (Scheme.pointSmallEtale x).fiber.obj W)
        (hW : (f.inverseImageMonoid x h) →*
          X.logStructure.monoidSheaf.obj.obj (op W))
        (u : q₀ →* f.inverseImageMonoid x h),
        (∀ q : q₀, (u q).1 = i (1, Algebra.GrothendieckGroup.of q)) ∧
        X.logStructure.IsChart W hW ∧
        (X.logStructure.toEtalePrelogStructure.germ x W w).hom.comp hW = hP ∧
        (∀ q, f.sectionMap (Scheme.Etale.mk (𝟙 Y.scheme)) W (W.hom ≫ f.base)
          (by
            change (W.hom ≫ f.base) ≫ 𝟙 _ = W.hom ≫ f.base
            exact Category.comp_id _) (chart₀ q) = hW (u q)) ∧
        ∃ c : W.left ⟶ pullback
            (Y.logStructure.chartToSpec (Scheme.Etale.mk (𝟙 Y.scheme)) chart₀)
            (Spec.map (CommRingCat.ofHom
              (MonoidAlgebra.mapDomainRingHom ℤ u))),
          c ≫ pullback.fst _ _ = W.hom ≫ f.base ∧
          c ≫ pullback.snd _ _ = X.logStructure.chartToSpec W hW ∧
          Etale c := by
  sorry

end AlgebraicGeometry
