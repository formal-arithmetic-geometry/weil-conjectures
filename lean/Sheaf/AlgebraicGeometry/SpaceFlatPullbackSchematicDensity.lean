/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceOpenChartTests
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Flat pullback of a schematically dense quasi-compact open subspace

Source: Stacks Project, Morphisms of Spaces, Tag 089D,
`lemma-flat-morphism-scheme-theoretically-dense-open`
(blueprint: lem-sfb-space-flat-pullback-schematic-density).

The cartesian square identifies `XV` with the sheaf fibre product. Quasi-compactness
is tested on affine objects of the small étale site. Injectivity of the structure
sheaf map is expressed by joint detection of regular functions on the scheme charts
of the inverse image, using the ordinary global-section restriction maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flat pullback preserves quasi-compact open immersions and their schematic density.
The density clauses are the sectionwise injectivity of the structure-sheaf maps:
sections of the direct image are compatible families on all charts over the test object.
Source: Stacks Project, Morphisms of Spaces, Tag 089D
(blueprint: lem-sfb-space-flat-pullback-schematic-density).

Proof:
1. Choose a scheme atlas `Y₀ → Y`. Representability of the open immersion makes
   `V₀ = V ×_Y Y₀` an open subscheme. Its restrictions over affine opens of `Y₀`
   are quasi-compact by the affine étale chart hypothesis, so `V₀ → Y₀` is
   quasi-compact. Open immersions are monomorphisms, hence separated and
   quasi-separated. Scheme tests of `jX` are also scheme tests of `j`, so they
   are open immersions (def-a1-space-open-subspace, lem-a1-space-open-chart-tests,
   lem-trf-space-chartwise-etale-permanence, def-weil-finite-type-morphism,
   def-weil-closed-immersion).
2. For an étale scheme chart `T → X`, set `P = T ×_Y Y₀`. This is a scheme
   surjectively étale over `T`, and `P → X` is étale. The compatible-chart
   definition of flatness makes `P → Y₀` flat
   (lem-trf-space-fibre-products-etale-covers,
   lem-trf-space-chartwise-etale-permanence, def-sfb-space-morphism-properties).
3. Choosing `T → X` to be an atlas gives an atlas `P → X` on which the pullback
   open is quasi-compact by lem-pc-quasi-compact-base-change. Its diagonal is
   an isomorphism, hence closed. Descend the conjunction of quasi-compactness
   and separatedness by lem-trf-space-qc-separated-etale-local. In particular
   every affine étale test has quasi-compact inverse image.
4. Restrict the assumed injection to `Y₀`. The section formula of
   lem-trf-space-etale-module-pushforward-restriction gives the injection for
   `V₀ → Y₀`. Its kernel is zero, so its scheme-theoretic image is `Y₀`
   (def-nagata-scheme-theoretic-image). Apply lemma-nagata-dense-flat-pullback
   to `P → Y₀`: the quasi-compact open `V₀ ×_{Y₀} P → P` has image `P`.
   By lemma-nagata-scheme-image-ideal-qc its global-section restriction is
   injective; quasi-compactness is supplied by lem-pc-quasi-compact-base-change.
5. Two functions on any `T → X` with equal restrictions on the inverse image
   become equal on `P` by step 4 and the direct-image section formula of
   lem-trf-space-etale-module-pushforward-restriction. Uniqueness in the
   structure-sheaf axiom for the surjective étale cover `P → T` makes the
   original functions equal (def-trf-algebraic-space). This proves the
   structure-sheaf injection, hence schematic density. -/
theorem flat_pullback_schematicDensity {S : Scheme.{u}} {X Y V XV : AlgebraicSpace S}
    (f : X ⟶ Y) (j : V ⟶ Y) (jX : XV ⟶ X) (g : XV ⟶ V)
    (hcart : IsPullback g.hom jX.hom j.hom f.hom)
    (hf : MapIsFlat f)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (hqc : ∀ T : Y.EtaleSite, IsAffine T.obj.left.left →
      ∃ (U : Over S) (p : U ⟶ T.obj.left) (r : yoneda.obj U ⟶ V.obj.obj),
        IsPullback r (yoneda.map p) j.hom.hom T.obj.hom ∧ CompactSpace U.left)
    (hdense : ∀ (T : Y.EtaleSite) (a b : Y.structureSheaf.obj.obj (op T)),
      (∀ (U : V.EtaleSite) (p : U.obj.left ⟶ T.obj.left),
        U.obj.hom ≫ j.hom.hom = yoneda.map p ≫ T.obj.hom →
        (Scheme.Γ.map p.left.op).hom a = (Scheme.Γ.map p.left.op).hom b) → a = b) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) jX.hom.hom ∧
      (∀ T : X.EtaleSite, IsAffine T.obj.left.left →
        ∃ (U : Over S) (p : U ⟶ T.obj.left) (r : yoneda.obj U ⟶ XV.obj.obj),
          IsPullback r (yoneda.map p) jX.hom.hom T.obj.hom ∧ CompactSpace U.left) ∧
      (∀ (T : X.EtaleSite) (a b : X.structureSheaf.obj.obj (op T)),
        (∀ (U : XV.EtaleSite) (p : U.obj.left ⟶ T.obj.left),
          U.obj.hom ≫ jX.hom.hom = yoneda.map p ≫ T.obj.hom →
          (Scheme.Γ.map p.left.op).hom a = (Scheme.Γ.map p.left.op).hom b) → a = b) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
