/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullbackCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients

/-!
# Finite geometric representing objects and geometric properties

Source: latest blueprint,
`part-six-operations/sec-six-functors/sec-the-remaining-operations/`
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, opening locality/restriction step
(blueprint: lem-sfb-finite-geometric-verdier-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The two constructible representing objects and geometric properties, before constructing
any comparison between the two dualizing objects.
Source: latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`det-prop-sf-biduality-general.proof.md`, opening locality argument.

Proof: use the normalized finite-discrete internal-module/ordinary-module equivalence
and finite etale realization. Exact inverse image carries bounded flat constructible
representatives to such representatives with the same Tor interval. Its tensorator is
strong monoidal and respects the Koszul symmetry on homogeneous terms. A field extension
is faithfully flat, so its projection is an fpqc cover; exact faithful inverse image
reflects acyclicity of cones, hence isomorphisms. Transport these assertions through the
specified coefficient equivalences. Compact-support base change for the chosen
compactification is the open-extension comparison followed by the proper mate. Proper
base change and the open comparison make this exact displayed composite invertible.

Apply the current exceptional-inverse-image existence theorem over k and kbar to the
structure morphisms. The coefficient unit is constructible with Tor interval [0,0].
The constructible exceptional right adjoints evaluated at that unit give W and Wbar,
with constructible finite-Tor membership. Their adjunction counits and the full-subcategory
Hom equivalences give precisely the displayed bijections into the ambient categories.
Compactification coherence transfers these bijections from the Nagata support models to
R and Rbar for the specified c and its base change. This constructs the data before any
comparison between W and Wbar. Finite or algebraically closed k supplies Brown existence;
kbar is algebraically closed. Zero coefficients and the empty scheme give the same
representing statements in the zero category, with no nonzero-coefficient assumption.
(blueprint: new-lem-sfb-finite-geometric-verdier-base) -/
theorem finite_geometric_verdier_base_exists
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell : A) ^ r = 0)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a) :
    let Λ := cartesianFinitePointRing A
    let h := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
    let G := detSfDerivedPullback Λ (pullback.fst a h)
    let H := detSfDerivedPullback Λ h
    let C := finiteFieldModuleDerived (CommMon.mk Λ) X
    let D := finiteFieldModuleDerived (CommMon.mk Λ) (pullback a h)
    let S := constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _
    let Sbar := constantModelBoundedConstructible Λ (pullback a h) ⊓
      DerivedCategory.finiteTorAmplitude _
    let R := detSfCompactSupport Λ c
    let Rbar := detSfCompactSupport Λ (c.baseChange h)
    let alpha := detSfCompactSupportBaseChangeComposite Λ a h c
      (compactSupportOpenBaseChangeIso Λ a h c)
    ∃ (W : C) (Wbar : D) (counit : R.obj W ⟶ 𝟙_ _)
      (counitBar : Rbar.obj Wbar ⟶ 𝟙_ _),
      S W ∧ Sbar Wbar ∧
      (∀ P : S.FullSubcategory,
        Function.Bijective (fun f : P.obj ⟶ W ↦ R.map f ≫ counit)) ∧
      (∀ P : Sbar.FullSubcategory,
        Function.Bijective (fun f : P.obj ⟶ Wbar ↦ Rbar.map f ≫ counitBar)) ∧
      (∀ K L : C, Functor.LaxMonoidal.μ G K L ≫
          G.map (finiteFieldDerivedBraiding (CommMon.mk Λ) X K L).hom =
        (finiteFieldDerivedBraiding (CommMon.mk Λ) (pullback a h)
          (G.obj K) (G.obj L)).hom ≫ Functor.LaxMonoidal.μ G L K) ∧
      (∀ K : S.FullSubcategory, Sbar (G.obj K.obj)) ∧
      (∀ (K L : C) (f : K ⟶ L), S K → S L → IsIso (G.map f) → IsIso f) ∧
      (∀ K : S.FullSubcategory, IsIso (alpha.app K.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
