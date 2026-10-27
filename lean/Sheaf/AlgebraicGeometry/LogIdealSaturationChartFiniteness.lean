module

public import Sheaf.AlgebraicGeometry.LogIdealAffineAtlas
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.GroupTheory.FineMonoidFiniteSaturation

/-! # Cartesian generator charts and finite saturation comparison

Source: ILO VIII 3.1.17, 3.2.9 (finiteness sentence), 3.3.9, printed pp. 101, 104, 108
(blueprint: lem-trf-log-ideal-saturation-chart-finiteness).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The saturation inclusions glue to a finite log morphism with exactly the saturated
generator charts as affine preimages. Each chart is its generator locus. Every finite
translate cover supplies the displayed monomial module generators; such covers exist.
The log morphism, affine chart squares and finiteness commute with strict étale change
of the base chart. Multiplicative notation renders the source's additive monoids.

Source: ILO VIII 3.1.17 (printed p. 101), 3.2.9, finiteness sentence only (p. 104),
3.3.9 (p. 108) (blueprint: lem-trf-log-ideal-saturation-chart-finiteness).

Proof:
1. The generators of P and the finite list h/e generate Q_e. This is integral inside
P^gp, and its group completion is P^gp because it contains P. Apply
`lem-trf-fine-monoid-finite-saturation` to get finite translate covers of its root
saturation. The root subset is a submonoid, so the recorded closure is that subset.
2. The fine lifting criterion `lem-trf-log-ideal-chart-lifting-criterion` gives the
local lift from the saturated e-chart to the ordinary e-chart. It sends every monomial
to the same monomial. On double overlaps the same criterion says these lifts, including
their log maps, agree. The sheaf condition glues them to s over the base log scheme.
3. At a geometric point of an f-chart where e also generates the ideal, cancellation
in the integral log stalk makes e/f a unit. Its structural image is a ring unit, so
the point belongs to the assumed monomial overlap with the e-chart. Conversely e
generates throughout its chart. As the f-charts cover, this proves the locus assertion.
4. On each saturated f-chart, s fixes the monomial e/f. The inverse image of the
ordinary e/f principal open is therefore exactly the saturated e/f principal open.
Taking the union over f proves the inverse-image equality. The restricted morphism
is the normalized tensor chart map; the open-immersion universal property gives the
Cartesian square (`def-pc-fibre-product`). Its log chart equation is the inclusion.
5. For any finite translate cover F, write q=f*p with f in F and p in Q_e. Then
(a tensor z^q)=(a tensor z^p)(1 tensor z^f). Expand monoid-algebra elements and pure
tensors to get the stated finite sums. This does not require injectivity of the ring
map and also applies when a tensor ring is zero.
6. The finite translate set and Step 5 make each chart ring map finite. Use
`lem-weil-pbc-spec-finite-ring-map-finite` on each full affine preimage from Step 4,
and `lem-weil-pbc-finite-local-on-target` on the ordinary affine cover. This proves
s finite, including the assertion for every affine open (`def-weil-finite-integral-morphism`).
7. The arbitrary-ring-base-change clause of `lem-trf-log-ideal-affine-atlas-gluing`
identifies each base-changed chart and overlap with the same tensor chart for A'.
The coefficient/monomial normalization gives the same comparison map in both orders.
Hence the log maps glue compatibly, as do their Cartesian chart squares. The same F
and finite-sum calculation prove spanning and finiteness after base change. For strict
étale change the log structure is the pulled-back one. Work on affine pieces; the
identifications agree on overlaps. This proves all compatibility assertions.
-/
theorem logIdeal_saturation_chart_finiteness
    (A P : Type u) [CommRing A] [CommMonoid P]
    (hfg : Monoid.FG P)
    (hP : Function.Injective (Algebra.GrothendieckGroup.of (M := P)))
    (α : P →* A) (E : Finset P) (hE : E.Nonempty)
    (M : EtaleLogStructure (Spec (.of A)))
    (c : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A))))))
    (hc : M.IsChart (Scheme.Etale.mk (𝟙 (Spec (.of A)))) c)
    (hα : ∀ p, M.alpha.app (op (Scheme.Etale.mk (𝟙 (Spec (.of A))))) (c p) =
      (Scheme.ΓSpecIso (.of A)).inv (α p))
    (X₀ Xₛ : Scheme.{u}) (N₀ : EtaleLogStructure X₀) (Nₛ : EtaleLogStructure Xₛ)
    (b₀ : EtaleLogMap N₀ M) (bₛ : EtaleLogMap Nₛ M)
    (D₀ : LogIdealAffineAtlas α E c b₀
      (fun e ↦ logIdealChartMonoid E e.val) (fun e ↦ logIdealChartInclusion E e.val))
    (Dₛ : LogIdealAffineAtlas α E c bₛ
      (fun e ↦ logIdealSaturatedChartMonoid E e.val)
      (fun e ↦ logIdealSaturatedChartInclusion E e.val)) :
    ∃ s : EtaleLogMap Nₛ N₀,
      D₀.FiniteComparison Dₛ s ∧ D₀.GeneratorLoci ∧ Dₛ.GeneratorLoci ∧
      LogIdealSaturationSpanning α E ∧
      ∀ (A' : Type u) [CommRing A'] (ρ : A →+* A')
        (M' : EtaleLogStructure (Spec (.of A'))) (f : EtaleLogMap M' M),
        f.base = Spec.map (CommRingCat.ofHom ρ) → f.IsStrictEtale →
        ∃ (C₀ : D₀.BaseChange ρ f) (Cₛ : Dₛ.BaseChange ρ f)
          (s' : EtaleLogMap Cₛ.N' C₀.N') (v : EtaleLogMap Cₛ.N' N₀),
          C₀.atlas.FiniteComparison Cₛ.atlas s' ∧
          C₀.atlas.GeneratorLoci ∧ Cₛ.atlas.GeneratorLoci ∧
          LogIdealSaturationSpanning (ρ.toMonoidHom.comp α) E ∧
          s'.CompEq C₀.q v ∧ Cₛ.q.CompEq s v ∧
          IsPullback s'.base Cₛ.q.base C₀.q.base s.base := by
  sorry

end AlgebraicGeometry
