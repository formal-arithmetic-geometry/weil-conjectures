module

public import Sheaf.AlgebraicGeometry.StacksBigSiteCategory
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Sheaf.AlgebraicGeometry.QuasiCompactLocallyFiniteTypeSchemeSize
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Bounded affine locally finite type coproducts in a fixed big site

Source: Stacks Project, sets.tex, Tags 04T7, 000Q, 000J and 000R (6), and
topologies.tex, Tags 021R and 021S
(blueprint: lem-sfb-bounded-affine-lft-coproduct).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A bounded family of affine schemes locally of finite type over `T` has its scheme
coproduct represented over `T` in the fixed big fppf site. The chosen full category is
that of [def-sfb-stacks-big-site-category]; an object of `Over T` is exactly an object
of its slice big site. Its fppf topology affects coverings, not object membership.
No flatness, separatedness, finite presentation or nonemptiness is assumed.

Source: Stacks Project, sets.tex, Tags 04T7 (lemma-bound-finite-type), 000Q
(lemma-bound-size), 000J (lemma-construct-category), 000R (lemma-what-is-in-it) (6),
and topologies.tex, Tags 021R and 021S
(blueprint: lem-sfb-bounded-affine-lft-coproduct).

Proof plan:
1. Each affine W_j is isomorphic to Spec of its global ring and is quasi-compact,
using [lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact] (iii). Apply
[lem-sfb-qc-lft-scheme-size-bound] to obtain s(W_j) ≤ s(T). Only compactness of
W_j is used; neither T nor the morphism is required to be quasi-compact.
2. By [lem-weil-pbc-scheme-coproduct-family], the coprojections are open immersions
and cover the scheme coproduct. Their image open subschemes are isomorphic to W_j,
so their sizes agree. Set κ = s(T). The index bound implies |J| ≤ κ ≤ κ^ℵ₀,
and each image has size at most κ^ℵ₀. For the empty family the coproduct is empty
and the same inequalities and covering assertion apply.
3. The fixed big site contains T. Apply [lem-sfb-big-site-open-cover-size-closure]
to that open cover and these bounds, obtaining a representative W₀ and an
isomorphism e : W₀ ≅ ∐ W in the chosen full category's ambient scheme category.
4. Give W₀ the map e.hom ≫ Sigma.desc f to T. Fullness makes it a morphism of the
chosen category, hence an object of its slice. The resulting e is an isomorphism
over T by this defining equation. The fppf conditions constrain covers only and
impose none of flatness, separatedness or finite presentation on the f_j. -/
theorem bounded_affine_locallyOfFiniteType_coproduct
    (code : Scheme.{u} ↪ ZFSet.{u + 1}) (S₀ : Set Scheme.{u})
    (α : Ordinal.{u + 1}) (hsite : IsStacksBigSiteCategory code S₀ α)
    (T : StacksBigSiteCategory code α) (J : Type u)
    (hJ : Cardinal.mk J ≤ max Cardinal.aleph0 (Cardinal.mk T.obj.affineOpens))
    (W : J → Scheme.{u}) [∀ j : J, IsAffine (W j)]
    (f : ∀ j : J, W j ⟶ T.obj) [∀ j : J, LocallyOfFiniteType (f j)] :
    ∃ W₀ : Over T, ∃ e : W₀.left.obj ≅ ∐ W,
      e.hom ≫ Sigma.desc f = W₀.hom.hom := by
  sorry

end AlgebraicGeometry.Scheme
