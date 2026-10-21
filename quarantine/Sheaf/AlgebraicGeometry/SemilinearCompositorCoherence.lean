/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingOperations
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Coherence of normalized semilinear compositors

Source: Stacks Project, Tags 0D6D and 0D6E; section-normalized coherence on ringed
sequence sites (blueprint: lem-sf-semilinear-compositor-coherence).

The inverse-image functor denoted `P` in the node is `VaryingRing.G`; its direct-image
functor `S` is `VaryingRing.P`. The forward inverse-image compositor is `gComp.inv`.
All functors, compositors and identity comparisons are those of the specified adjunctions.
The associativity clauses allow independently named intermediate and total composites.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.VaryingRing

attribute [local irreducible] gComp pComp jComp gId pId jId

/-- Associativity and both unit laws for the three normalized semilinear compositors,
including transport along arbitrary equalities identifying intermediate and total maps.
Source: Stacks Project, Tags 0D6D, 0D6E, 0B65, 0DV0 and 04VG
(blueprint: lem-sf-semilinear-compositor-coherence).

Proof:
1. The two ordinary direct-image pastings restrict sections along the same map of
iterated fibre products: their projections agree. The fibre-product universal property
(def-pc-fibre-product) identifies these maps. The same projection check identifies
identity composition with the graph-normalized modulePId.
2. Apply lem-trf-adjoint-composition-coherence to the ordinary inverse-image adjoints,
using the inverses of these section comparisons on the right adjoints. The composite
adjunction is def-weil-pbc-composite-adjunction. Unit-compatible uniqueness from
lem-weil-pbc-conjugate-iso-unit-equation identifies the resulting comparisons with
moduleGComp, hence proves their associativity.
3. For identities, insert the explicit composite-adjunction unit. Naturality of the
ordinary unit and modulePId makes each whiskered identity comparison satisfy the
same unit equation as moduleGComp. Unit-compatible uniqueness gives both unit laws.
No two distinct adjunction structures are identified.
4. Localize the exact ordinary inverse images termwise, using
lem-weil-pbc-exact-functor-derived-factorization. After postcomposition by the
factorization isomorphism, both pastings reduce to the corresponding ordinary pastings;
naturality cancels the intermediate factorization maps. They agree by steps 2 and 3.
Part (3) of lem-weil-pbc-localization-universal-property promotes equality on every
localized complex to equality on the entire unbounded derived category.
5. Invert inverse-image coherence and take its conjugate under the fixed derived
adjunctions (def-weil-pbc-adjunction-conjugate). Composition of conjugates and
lem-weil-pbc-mate-pasting (2) identify the two pastings with the pComp pastings.
Apply the same argument to inverse unit equations, using mate-pasting (4) for identities.
6. Apply lem-trf-adjoint-composition-coherence to ordinary open extension left adjoints
and inverse-image right adjoints, using step 2 for the right-adjoint hypothesis.
Unit-compatible uniqueness identifies the result with moduleJComp. Repeat step 3's
unit calculation for these open adjunctions to obtain both ordinary open unit laws.
7. Localize these exact open functors as in step 4. Ordinary open coherence becomes
jComp coherence by the factorization isomorphisms and localization extensionality.
Localized units have the same unit equation as jId; unit-compatible uniqueness
identifies them with this specified derived identity normalization.
8. Eliminate the supplied equalities of intermediate and total scheme maps, one at
a time. The transports then become identities and the claims are precisely the
coherence and unit equations already obtained. Proof irrelevance identifies the
open-immersion instances under this transport. -/
theorem semilinear_compositor_coherence
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n) :
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ T),
      (G R φ f).map ((gComp R φ g h).inv.app M ≫
          (eqToIso (congrArg (G R φ) egh)).hom.app M) ≫
        (gComp R φ f l).inv.app M ≫ (eqToIso (congrArg (G R φ) efl)).hom.app M =
      (gComp R φ f g).inv.app ((G R φ h).obj M) ≫
        (eqToIso (congrArg (G R φ) efg)).hom.app ((G R φ h).obj M) ≫
        (gComp R φ k h).inv.app M ≫ (eqToIso (congrArg (G R φ) ekh)).hom.app M) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ X),
      (P R φ h).map ((pComp R φ f g).hom.app M ≫
          (eqToIso (congrArg (P R φ) efg)).hom.app M) ≫
        (pComp R φ k h).hom.app M ≫ (eqToIso (congrArg (P R φ) ekh)).hom.app M =
      (pComp R φ g h).hom.app ((P R φ f).obj M) ≫
        (eqToIso (congrArg (P R φ) egh)).hom.app ((P R φ f).obj M) ≫
        (pComp R φ f l).hom.app M ≫ (eqToIso (congrArg (P R φ) efl)).hom.app M) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion m]
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ X),
      (J R φ h).map ((jComp R φ f g).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Z // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Z) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ g, inferInstance⟩ ⟨k, inferInstance⟩ efg))).hom.app M) ≫
        (jComp R φ k h).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨k ≫ h, inferInstance⟩ ⟨m, inferInstance⟩ ekh))).hom.app M =
      (jComp R φ g h).hom.app ((J R φ f).obj M) ≫
        (eqToIso (congrArg
          (fun a : {a : Y ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (Y ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨g ≫ h, inferInstance⟩ ⟨l, inferInstance⟩ egh))).hom.app
          ((J R φ f).obj M) ≫
        (jComp R φ f l).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ l, inferInstance⟩ ⟨m, inferInstance⟩ efl))).hom.app M) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ Y),
      (gComp R φ (𝟙 X) f).inv.app M ≫
          (eqToIso (congrArg (G R φ) (Category.id_comp f))).hom.app M =
        (gId R φ X).hom.app ((G R φ f).obj M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ Y),
      (gComp R φ f (𝟙 Y)).inv.app M ≫
          (eqToIso (congrArg (G R φ) (Category.comp_id f))).hom.app M =
        (G R φ f).map ((gId R φ Y).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X),
      (pComp R φ (𝟙 X) f).hom.app M ≫
          (eqToIso (congrArg (P R φ) (Category.id_comp f))).hom.app M =
        (P R φ f).map ((pId R φ X).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X),
      (pComp R φ f (𝟙 Y)).hom.app M ≫
          (eqToIso (congrArg (P R φ) (Category.comp_id f))).hom.app M =
        (pId R φ Y).hom.app ((P R φ f).obj M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Derived R φ X),
      (jComp R φ (𝟙 X) f).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
              ⟨𝟙 X ≫ f, inferInstance⟩ ⟨f, inferInstance⟩ (Category.id_comp f)))).hom.app M =
        (J R φ f).map ((jId R φ X).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Derived R φ X),
      (jComp R φ f (𝟙 Y)).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ 𝟙 Y, inferInstance⟩ ⟨f, inferInstance⟩ (Category.comp_id f)))).hom.app M =
        (jId R φ Y).hom.app ((J R φ f).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
