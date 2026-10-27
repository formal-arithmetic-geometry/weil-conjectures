module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.DirectSum.Module
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Fibrewise dense opens of smooth schemes under base change

Source: Bosch--Lütkebohmert--Raynaud, *Néron Models*, §2.5, preliminaries and
Lemma 1(b), printed pp.55--56; Lemma 3, printed pp.56--57, removes quasi-compactness
of the open. The affine injectivity argument uses Stacks Project, Tag 0AT9.
(blueprint: lem-sfb-smooth-fibrewise-dense-open-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An open dense in every fibre of a smooth family stays fibrewise dense after arbitrary
base change, and its base-changed inclusion induces an injective structure-sheaf map.
The inverse image of `Set.range j` under `f.fiberι t` is the open fibre `V_t` inside `Y_t`.
The inclusion `j'` is the underlying map of `(Over.pullback g).map (Over.homMk j rfl)`.
Injectivity on every open is precisely injectivity of `𝒪_{Y'} ⟶ j'_*𝒪_{V'}`.

Source: BLR, *Néron Models*, §2.5, preliminaries and Lemma 1(b), printed pp.55--56,
with Lemma 3, printed pp.56--57; Stacks Project, Tags 0383 and 0AT9.
(blueprint: lem-sfb-smooth-fibrewise-dense-open-base-change).

Proof:
1. For `t'` over `t`, identify the changed fibre with the extension of `Y_t` by
   `κ(t')/κ(t)`, using def-pc-base-change. The projection is open by
   lem-sc-scheme-over-field-universally-open. Every nonempty open has nonempty open
   image, which meets `V_t`, so it meets the changed open fibre. Empty fibres are
   vacuous. The changed inclusion is open by lem-weil-pbc-open-immersion-base-change.
2. Smoothness gives flatness and local finite presentation by lem-pc-smooth-flat.
   Apply lem-sfb-scheme-flat-smooth-point-base-change at every changed point and
   lem-weil-pbc-smooth-local-on-source to see that the changed family is smooth.
3. Work on finite-presentation affine charts `Spec B` over `Spec A`, supplied by
   def-sbc-locally-finite-presentation. Open restrictions are smooth by
   lem-weil-pbc-smooth-local-on-source; lem-pc-smooth-flat and
   lem-weil-pbc-flat-ring-map-iff-flat-affine give a flat finitely presented algebra.
   The open remains fibrewise dense in each chart. By
   lem-sfb-smooth-fibre-dense-quasi-compact-selection, choose a quasi-compact
   fibrewise dense open inside it and a finite principal cover `⋃ D(b_i)` of that open.
4. Each `B_{b_i}` is flat over `A` by
   lem-pc-affine-flat-module-localization-preserves-flatness, and their finite product
   is flat by lem-weil-pbc-finite-product-flat-modules. Smooth fibres are reduced by
   sbc-lem-smooth-geometrically-reduced. Apply
   lemma-nagata-reduced-dense-image-schematic and lemma-nagata-scheme-image-ideal-qc
   to the quasi-compact dense open of each reduced fibre. The sheaf axiom for the
   principal cover gives injectivity of the tuple of fibre restriction maps.
5. Tensoring the finite product commutes with its finite direct-sum description.
   By lem-weil-pbc-localization-tensor-over-base, the fibre tuple is the tensor of
   `B → ∏ B_{b_i}` with the residue field. Apply
   lem-sfb-flat-finitely-presented-module-fibre-injectivity with `Σ = {1}`, `N = B`
   and `Q = A` to obtain injectivity of the original tuple.
6. A section vanishing on `V` vanishes on all these principal opens, hence is zero
   on each affine chart. The sheaf axiom on the affine chart basis gives injectivity
   on every open. Apply this to the changed smooth family from steps 1--2.
   Empty charts have zero section rings, so empty covers cause no exception. -/
theorem Smooth.fibrewise_dense_open_baseChange
    {Y T V : Scheme.{u}} (f : Y ⟶ T) [Smooth f] (j : V ⟶ Y) [IsOpenImmersion j]
    (hdense : ∀ t : T, Dense ((f.fiberι t) ⁻¹' Set.range j))
    {T' : Scheme.{u}} (g : T' ⟶ T) :
    (∀ t' : T', Dense
      (((pullback.snd f g).fiberι t' ≫ pullback.fst f g) ⁻¹' Set.range j)) ∧
    ∀ W : (pullback f g).Opens,
      Function.Injective
        ((((Over.pullback g).map
          (Over.homMk j rfl : Over.mk (j ≫ f) ⟶ Over.mk f)).left.app W)) := by
  sorry

end AlgebraicGeometry
