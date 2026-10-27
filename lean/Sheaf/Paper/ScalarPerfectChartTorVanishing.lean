/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U7
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-! # Tensor cohomology vanishing on one scalar-perfect chart

Source: the internal-Hom stability proof, paragraphs 2--3, and Stacks Project,
Tags 08JH, 08JJ, 08G1 and 07A4.
(blueprint: lem-sfb-scalar-perfect-chart-tor-vanishing).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- A fixed bounded scalar-perfect model kills tensor cohomology off its window,
and its relative dual kills tensor cohomology off the reflected window, after
restriction to that one chart. No cover, compactness or admissibility is assumed.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.proof.md,
paragraph 2 final sentence and paragraph 3 parenthetical; Stacks 08JH, 08JJ,
08G1 and 07A4. (blueprint: lem-sfb-scalar-perfect-chart-tor-vanishing).

Proof: identify U_proet with the slice S_proet/U by
lem-weil-proetale-weakly-etale-localization. Abelian inverse image agrees with
slice restriction, and the coefficient comparison g^*Λ_S ≅ Λ_U identifies its
module-object pullback with restriction for this actual coefficient ring.
Then use lem-sfb-module-object-ringed-site-derived-comparison on the chart.
The pointwise scalar extension sends each specified finite-free splitting to a
finite-free splitting on the chart, without needing flatness of scalar extension.
Apply lem-sfb-split-perfect-dual-tor-window to that bounded complex and its
splittings. It computes the dual by the signed Hom complex into B[0], in degrees
[-b,-a], and proves both tensor vanishings for every degree-zero chart module.
The slice internal-Hom comparison of the module-object/ringed-site comparison
identifies this dual with the restriction of RHom(P,B). Exact inverse image
commutes with cohomology and degree-zero objects, and its canonical derived
tensor comparison identifies the restricted global tensor with the local tensor
against the inverse image of N. Apply the two local vanishings to that inverse
image. The comparison preserves the underlying abelian sheaves, giving exactly
the two asserted vanishings. The same calculation handles rank zero, the zero
complex, empty charts and arbitrary integral endpoints; no test module is
required to be flat. -/
theorem scalarPerfect_chart_tor_vanishing
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] {S U : Scheme.{u}} (g : U ⟶ S) [WeaklyEtale g]
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S)))
    (F : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) ℤ)
    (a b : ℤ) (hab : a ≤ b)
    (hF : ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n))
    (hproj : ∀ n : ℤ, ∃ r : ℕ, ∃ i : F.X n ⟶ Mod.finiteFree Λ.X r,
      ∃ p : Mod.finiteFree Λ.X r ⟶ F.X n, i ≫ p = 𝟙 (F.X n))
    (hG : ((upperStarFromPoint U).mapMod Λ.X).PreservesZeroMorphisms)
    (hrep : letI := hG
      Nonempty (((CondensedRing.upperStar Λ.X g).mapDerivedCategory).obj P ≅
        DerivedCategory.Q.obj
          ((((upperStarFromPoint U).mapMod Λ.X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F))) :
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S))
      (q : ℤ),
      (q < a ∨ b < q → IsZero ((upperStar Ab.{u + 1} g).obj
        (((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.derivedTensor Λ.X S).obj P).obj
            ((DerivedCategory.singleFunctor _ 0).obj N))).X))) ∧
      (q < -b ∨ -a < q → IsZero ((upperStar Ab.{u + 1} g).obj
        (((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.derivedTensor Λ.X S).obj
            (((CondensedRing.derivedHom Λ.X S).obj (Opposite.op P)).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (Mod.regular (condensedRingObj Λ.X S))))).obj
            ((DerivedCategory.singleFunctor _ 0).obj N))).X))) := by sorry

end AlgebraicGeometry.ProEtale
