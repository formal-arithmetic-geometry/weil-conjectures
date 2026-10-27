/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.CategoryTheory.Yoneda
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.GroupoidSourcePullbackTranslation

/-! # Descent of a source-open locus through a scheme equivalence relation

Source: Stacks Project, More on Groupoids, Tag 04LH, `lemma-local-source`,
specialized to `g = id` and both base-change properties flat and locally of finite
presentation; Groupoids, Tags 0233 and 03C6
(blueprint: lem-sfb-relation-open-locus-descent).

Open subschemes are represented by their canonical opens. The assignment is defined
only for flat locally finitely presented morphisms over the fixed base. Its two
compatibility hypotheses express invariance under isomorphisms of morphisms and
under the indicated cartesian squares. The identity section is specified by its
source and target identities; injectivity and reflexivity on sections ensure its
existence and uniqueness, without any flatness assumption on that section.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A source-open locus compatible with isomorphisms and flat locally finitely
presented base change descends through a flat locally finitely presented scheme
equivalence relation. The descended open is the inverse image along its identity.

Source: Stacks Project, More on Groupoids, Tag 04LH, `lemma-local-source`, case
`g = id`; Groupoids, Tags 0233 and 03C6
(blueprint: lem-sfb-relation-open-locus-descent).

Proof:
1. Reflexivity, symmetry and transitivity on sections give identity, inverse and
   composition. Injectivity forces these operations to be natural and their laws
   to hold. Yoneda (`lem-pc-yoneda`) produces the corresponding scheme morphisms
   and the groupoid of `def-a1-groupoid-scheme`, with identity the supplied `e`.
2. Set `A = R ×[t,V,t] R`, with projections `p₀,p₁`, and define
   `d(a,b) = i(a) ∘ b`. The translation isomorphism of
   `lem-a1-groupoid-source-pullback-translation`, with inversion and interchange
   of factors, identifies `A` with `R ×[t,V,s] R` by `(a,b) ↦ (d(a,b),a)` and
   with `R ×[s,V,s] R` by `(a,b) ↦ (d(a,b),b)`. Their inverses are
   `(z,a) ↦ (a,a ∘ z)` and `(z,b) ↦ (b ∘ i(z),b)`. The groupoid laws verify
   the inverse identities. Thus the squares `(d,p₀;t,s)` and `(d,p₁;s,s)`
   are cartesian (`def-pc-fibre-product`).
3. Both squares express `d` as a base change of `s`, along `t` and `s`.
   Flatness and local finite presentation of `d` follow from
   `lem-weil-pbc-flat-morphism-base-change` and clause (3) of
   `lem-weil-pbc-qcqs-morphism-permanence`. Compatibility of the assignment,
   including its invariance under the displayed isomorphisms, gives
   `D_d = p₀⁻¹(D_s) = p₁⁻¹(D_s)`.
4. The identity `e ≫ t = id` defines `j : R → A`, `r ↦ (r,e(t(r)))`,
   by the pullback universal property. Pull back the preceding equality along
   `j` to obtain `D_s = t⁻¹(e⁻¹(D_s))`. The latter inner inverse image is open.
   Opens determine the canonical restricted structure sheaves, so the equality
   is also an equality of open subschemes (`def-weil-open-immersion`).
-/
theorem relation_open_locus_descent
    {S : Scheme.{u}}
    (D : ∀ {X Y : Over S} (f : X ⟶ Y),
      Flat f.left → LocallyOfFinitePresentation f.left → X.left.Opens)
    (hiso : ∀ {X Y X' Y' : Over S} (f : X ⟶ Y) (f' : X' ⟶ Y')
      (hf : Flat f.left) (hlfp : LocallyOfFinitePresentation f.left)
      (hf' : Flat f'.left) (hlfp' : LocallyOfFinitePresentation f'.left)
      (a : X' ≅ X) (b : Y' ≅ Y),
      a.hom ≫ f = f' ≫ b.hom →
      D f' hf' hlfp' = a.hom.left ⁻¹ᵁ (D f hf hlfp))
    (hbase : ∀ {X Y X' Y' : Over S}
      (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X)
      (hf : Flat f.left) (hlfp : LocallyOfFinitePresentation f.left)
      (hg : Flat g.left) (hglfp : LocallyOfFinitePresentation g.left)
      (hf' : Flat f'.left) (hlfp' : LocallyOfFinitePresentation f'.left),
      IsPullback p.left f'.left f.left g.left →
      D f' hf' hlfp' = p.left ⁻¹ᵁ (D f hf hlfp))
    {V R : Over S} (s t : R ⟶ V)
    (hinj : ∀ T : Over S,
      Function.Injective (fun r : T ⟶ R ↦ (r ≫ s, r ≫ t)))
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [hs : Flat s.left] [ht : Flat t.left]
    [hslfp : LocallyOfFinitePresentation s.left]
    [htlfp : LocallyOfFinitePresentation t.left]
    (e : V ⟶ R) (hes : e ≫ s = 𝟙 V) (het : e ≫ t = 𝟙 V) :
    D s hs hslfp = t.left ⁻¹ᵁ (e.left ⁻¹ᵁ (D s hs hslfp)) := by
  sorry

end AlgebraicGeometry
