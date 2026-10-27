/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # The universal finite part of a scheme groupoid

Source: Stacks Project, Tags 04RI, 04RR, 04RU, and the first paragraph of Tag 0DTC,
`spaces-more-groupoids.tex`, section-finite-part-groupoid
(blueprint: lem-sfb-scheme-groupoid-universal-finite-part).

The auxiliary predicate expresses membership on test schemes, rather than just on
underlying topological points. The structure bundles the conclusion, including the
universal property and the translation formula. Its fields are data and propositions;
no construction is selected from an unproved existence assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A pair of morphisms factors through an open subscheme of a fibre product.
This retains the scheme structure and is the test-scheme meaning of membership in the
universal finite family in Stacks, section-finite-part-groupoid, preceding Tag 04RU
(blueprint: lem-sfb-scheme-groupoid-universal-finite-part). -/
def SchemeGroupoidFinitePartContains {U R M H : Scheme.{u}}
    (s : R ⟶ U) (g : M ⟶ U) (W : (pullback s g).Opens)
    (r : H ⟶ R) (m : H ⟶ M) : Prop :=
  ∃ w : H ⟶ W.toScheme,
    w ≫ W.ι ≫ pullback.fst s g = r ∧ w ≫ W.ι ≫ pullback.snd s g = m

/-- The data and properties asserted by the universal finite-part theorem.
Source: Stacks, Tags 04RI, 04RR, 04RU and 0DTC, first proof paragraph
(blueprint: lem-sfb-scheme-groupoid-universal-finite-part).

`represents` is the natural representing bijection written as a unique classifying
morphism: two open subschemes agree precisely when their subfunctors on all test schemes
agree. The inverse associates to a classifying morphism the pullback of `W`. Thus
naturality is built into precomposition, without choosing any maps of finite parts.

The arrow scheme is `W.toScheme`, its arrow map is `W.ι ≫ pullback.fst s g`, and its
source is `W.ι ≫ pullback.snd s g`. `translated_target` specifies the translated open
subscheme by its entire functor of points. The map `j` goes to the restricted relation
`(R ×[U] M) ×[U] M`; its two projection identities and the operation identities specify
the morphism of groupoids that is the identity on objects. The restricted relation has
the groupoid operations inherited componentwise from the original groupoid. -/
structure SchemeGroupoidUniversalFinitePart {S U R : Scheme.{u}} (b : U ⟶ S)
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R) where
  /-- The scheme representing section-marked finite open source parts. -/
  M : Scheme.{u}
  /-- Forget the selected finite open part. -/
  g : M ⟶ U
  /-- The forgetful morphism is separated. -/
  separated : IsSeparated g
  /-- The forgetful morphism is etale. -/
  etale : Etale g
  /-- The universal open subscheme; its scheme is the arrow scheme. -/
  W : (pullback s g).Opens
  /-- The universal open subscheme is also closed. -/
  closed : IsClosed W.carrier
  /-- The universal family contains the pulled-back unit. -/
  contains_unit : SchemeGroupoidFinitePartContains s g W (g ≫ e) (𝟙 M)
  /-- Every finite open family containing the unit has a unique classifying map.
  Equality with the pullback family is expressed on every test scheme. -/
  represents : ∀ (T : Scheme.{u}) (a : T ⟶ U) (Z : (pullback s a).Opens),
    IsFinite (Z.ι ≫ pullback.snd s a) →
    SchemeGroupoidFinitePartContains s a Z (a ≫ e) (𝟙 T) →
    ∃! m : T ⟶ M, m ≫ g = a ∧
      ∀ (H : Scheme.{u}) (r : H ⟶ R) (h : H ⟶ T),
        (SchemeGroupoidFinitePartContains s g W r (h ≫ m) ↔
          SchemeGroupoidFinitePartContains s a Z r h)
  /-- The target object is the finite open translated by the inverse arrow. -/
  target : W.toScheme ⟶ M
  /-- The unit arrow. -/
  unit : M ⟶ W.toScheme
  /-- Inversion of a universal finite-part arrow. -/
  inv : W.toScheme ⟶ W.toScheme
  /-- Composition of universal finite-part arrows. -/
  comp : pullback (W.ι ≫ pullback.snd s g) target ⟶ W.toScheme
  /-- All groupoid laws, on all test schemes. -/
  groupoid : IsGroupoidScheme (W.ι ≫ pullback.snd s g) target unit inv comp
  /-- Both structure morphisms are morphisms over the original base. -/
  over_base : target ≫ g ≫ b = (W.ι ≫ pullback.snd s g) ≫ g ≫ b
  /-- The arrow projection respects the target. Its source identity is the pullback square. -/
  target_arrow : target ≫ g = W.ι ≫ pullback.fst s g ≫ t
  /-- The arrow projection respects units. -/
  unit_arrow : unit ≫ W.ι ≫ pullback.fst s g = g ≫ e
  /-- The arrow projection respects inverses. -/
  inv_arrow : inv ≫ W.ι ≫ pullback.fst s g = W.ι ≫ pullback.fst s g ≫ i
  /-- The arrow projection respects composition on every test scheme. -/
  comp_arrow : ∀ (H : Scheme.{u}) (a₁ a₂ : H ⟶ W.toScheme)
    (hQ : a₁ ≫ (W.ι ≫ pullback.snd s g) = a₂ ≫ target)
    (hR : (a₁ ≫ W.ι ≫ pullback.fst s g) ≫ s =
      (a₂ ≫ W.ι ≫ pullback.fst s g) ≫ t),
    pullback.lift a₁ a₂ hQ ≫ comp ≫ W.ι ≫ pullback.fst s g =
      pullback.lift (a₁ ≫ W.ι ≫ pullback.fst s g)
        (a₂ ≫ W.ι ≫ pullback.fst s g) hR ≫ c
  /-- Translation by `i(z)` identifies the selected source and target families.
  `v` encodes the composable pair `(r,i(z))`; all further test changes `h` are included. -/
  translated_target : ∀ (T : Scheme.{u}) (q : T ⟶ W.toScheme)
    (H : Scheme.{u}) (h : H ⟶ T) (r : H ⟶ R) (v : H ⟶ pullback s t),
    v ≫ pullback.fst s t = r →
    v ≫ pullback.snd s t = h ≫ q ≫ W.ι ≫ pullback.fst s g ≫ i →
    (SchemeGroupoidFinitePartContains s g W r
        (h ≫ q ≫ W.ι ≫ pullback.snd s g) ↔
      SchemeGroupoidFinitePartContains s g W (v ≫ c) (h ≫ q ≫ target))
  /-- The source projection is finite locally free, including finiteness of the family. -/
  source_finiteLocallyFree : (W.ι ≫ pullback.snd s g).IsFiniteLocallyFree
  /-- The target projection is finite locally free. -/
  target_finiteLocallyFree : target.IsFiniteLocallyFree
  /-- The induced map to the restricted relation, retaining both endpoint objects. -/
  j : W.toScheme ⟶ pullback (pullback.fst s g ≫ t) g
  /-- Forgetting the target object gives the universal open inclusion. -/
  j_fst : j ≫ pullback.fst (pullback.fst s g ≫ t) g = W.ι
  /-- The other endpoint is the target object. -/
  j_snd : j ≫ pullback.snd (pullback.fst s g ≫ t) g = target
  /-- The induced morphism of groupoids is an open immersion on arrows. -/
  openImmersion : IsOpenImmersion j

/-- The universal finite part of a separated flat locally finitely presented scheme
 groupoid is represented by schemes, and its source and target are finite locally free.
Source: Stacks, Tags 04RI (lemma-finite-separated-flat-locally-finite-presentation),
04RR (lemma-finite-plus-section), 04RU (lemma-finite-part-groupoid), section-finite-part-groupoid,
and Tag 0DTC (lemma-splitting), first paragraph
(blueprint: lem-sfb-scheme-groupoid-universal-finite-part).

Proof plan, following the four steps of the DAG node:
1. Apply lem-sfb-section-marked-finite-parts-scheme to `s` with section `e`.
   The unit identity gives `e ≫ s = 1`. This gives the representing scheme `M`, the
   separated etale map `g`, and the universal clopen family `W`, finite over `M` and
   containing the unit. Its natural universal property is exactly `represents`.
2. Local finite presentation implies local finite type. Apply
   lem-sfb-universal-finite-parts-groupoid to the universal family. Translation
   `r ↦ c(r,i(z))`, whose inverse is `r ↦ c(r,z)`, defines the target; the formulas
   for unit, inverse and composition give the groupoid and its morphism to `(U,R)`.
   Both projections are finite. These are the test-scheme identities recorded above.
3. The arrow map `W → R` is etale: the open inclusion followed by a base change of
   `g`. Use lem-weil-pbc-etale-scheme-base-change and
   lem-weil-pbc-etale-composition-cancellation. Apply
   lem-sfb-scheme-etale-source-target-properties to the source and target squares,
   to deduce flatness and local finite presentation. Together with finiteness this
   is the recorded Scheme.Hom.IsFiniteLocallyFree definition.
4. Forgetting the target endpoint of the restricted relation is a separated etale
   base change of `g`. Pull it back along the universal open inclusion. The induced
   map gives a section, open by lem-weil-pbc-etale-section-clopen-immersion.
   Its composite with the base change of the universal open inclusion is `j`, an
   open immersion by lem-weil-pbc-open-immersion-base-change and composition.
   Separatedness is preserved by lem-weil-pbc-separated-base-change.
   The projection identities show that `j` is the induced morphism of groupoids
   identical on objects. No affine, quasi-finite or stabilizer assumption is used. -/
theorem exists_schemeGroupoidUniversalFinitePart
    (S U R : Scheme.{u}) (b : U ⟶ S) (s t : R ⟶ U)
    (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : IsGroupoidScheme s t e i c) (hS : s ≫ b = t ≫ b)
    [IsSeparated s] [IsSeparated t] [Flat s] [Flat t]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t] :
    Nonempty (SchemeGroupoidUniversalFinitePart b s t e i c) := by
  sorry

end AlgebraicGeometry
