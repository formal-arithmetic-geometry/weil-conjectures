/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Sheaf.AlgebraicGeometry.CohomologyFractionPresentation
public import Sheaf.AlgebraicGeometry.Ample

/-! # Tensor-unit comparisons for raw section cohomology

Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-section-cohomology-unit-comparisons).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation of a pushforward resolution agrees with derived sections on the inverse
image open, compatibly with restriction and multiplication by a tensor power of a function.

Source: Stacks Project, Tag 01E4, Lemma 20.7.3, and Tag 01E1, restriction of injectives.
(blueprint: lem-pc-section-cohomology-unit-comparisons).

Proof: Put Y = f inverse W and G = F restricted to Y. Restrict I termwise to Y.
Restriction is exact and preserves injectives, so this is a resolution of G. Evaluation
of pushforward identifies its sections on Y with the section complex K(W). Restricting
again to D(b) identifies sections with K(D(a)), because pullback commutes with the
nonvanishing locus. Compute the derived section functors using these resolutions;
exact evaluation of presheaves and forgetting scalars commute with homology. This gives
the additive comparison
e. The tensor powers of the tensor unit have canonical isomorphisms to the unit,
constructed recursively with the unitors. Tensoring these with G gives isomorphisms
G tensor unit^n to G. Apply derived sections on Y and on U and then the preceding
comparisons to obtain c and d. Naturality of the derived section comparison for
restriction gives the second equation. Degreewise, the map induced by tensoring with
s^n is multiplication by b^n, under the unitors. The section comparisons are semilinear
for pullback of functions, and hence on homology multiplication by b^n corresponds
to the a^n action restricted along the structure-sheaf restriction. This is the first
equation. No compactness, separation, affineness, or quasi-coherence is needed: this
is only an identification of resolutions and their scalar and restriction maps.
For a=0 the open U and the target complex are empty; the same comparisons still apply.
For n=0 the scalar is 1 and the tensor-power comparison is the right unitor. -/
theorem sectionCohomology_unit_comparisons {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F)
    (q : ℕ) (W : T.Opens) (a : Γ(T, W)) :
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let L := 𝟙_ Y.Modules
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let s : Γ(L, ⊤) := unitSectionsEquiv ⊤ b
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
      Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
    ∀ (U : Y.Opens), (U : Set Y) = nonvanishingLocus L s →
      ∃ e : (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G ≃+
          P.obj (op (T.basicOpen a)),
      ∃ c : ∀ n : ℕ,
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj
          (G ⊗ L.tensorPow n : Y.Modules) ≃+ P.obj (op W),
      ∃ d : ∀ n : ℕ,
        (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj
          (G ⊗ L.tensorPow n : Y.Modules) ≃+ P.obj (op (T.basicOpen a)),
      (∀ (n : ℕ) (z : (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G),
        d n ((RingedSpace.openModuleCohomology Y.toRingedSpace q U).map
          (((ρ_ G).inv ≫ G ◁ tensorPowSection (homOfGlobalSection L s) n) :
            G ⟶ (G ⊗ L.tensorPow n : Y.Modules)) z) = a ^ n • e z) ∧
      (∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj
          (G ⊗ L.tensorPow n : Y.Modules)),
        d n ((RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
          (homOfLE (le_top : U ≤ ⊤))).app (G ⊗ L.tensorPow n : Y.Modules) ξ) =
            (P.map (homOfLE (T.basicOpen_le a)).op).hom (c n ξ)) := by sorry

end AlgebraicGeometry.Scheme.Modules
