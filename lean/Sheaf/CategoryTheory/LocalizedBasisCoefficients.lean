/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Localization of a specified internal finite basis

Source: Stacks, sites-modules.tex, Tags 0EMC (lemma-simple-invert) and 0EMD
(lemma-simple-invert-module), and the inverting-ell sentence in blueprint
`det-prop-sfb-cartesian-coefficients-finite-free`.
(blueprint: lem-sfb-localized-basis-coefficients)

Global sections are maps from the tensor unit. Invertibility of a section is expressed
by invertibility of its multiplication endomorphism. The finite-sum map in the square
is the componentwise localization map, written using the module biproduct projections
and inclusions. No assertion about objectwise localization of section rings is made.
-/

@[expose] public section

set_option autoImplicit false

universe u v uI uC vC w

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

/-- The precise finite-basis localization assertion in a given tensor category.
The predicate packages the assertion rather than asserting it for arbitrary categories.
The first conjunct supplies tensor additivity; the remaining assertion is independent
of the choice of that proof. A global section is invertible exactly when multiplication
by it is an isomorphism: applying the inverse to the unit gives its inverse section.
The summand formulas specify the finite-sum formulas on every local tuple.

Source: Stacks Tags 0EMC/0EMD and the blueprint parent's inverting-ell sentence.
(blueprint: lem-sfb-localized-basis-coefficients)
-/
def LocalizedBasisCoefficients
    {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
    [Abelian H] : Prop :=
  Nonempty (MonoidalPreadditive H) ∧
  ∀ [MonoidalPreadditive H]
    (R T A B : H) [MonObj R] [MonObj T] [MonObj A] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj T] [IsCommMonObj A] [IsCommMonObj B]
    (φ : Mon.mk R ⟶ Mon.mk T) (t : 𝟙_ H ⟶ R)
    (I : Type uI) [Fintype I] (b : I → (𝟙_ H ⟶ T))
    (q : (⨁ fun _ : I ↦ regular R) ≅ (comap φ.hom).obj (regular T)),
    (∀ i : I,
      (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫ q.hom.hom =
        φ.hom ≫ (ρ_ T).inv ≫ T ◁ b i ≫ μ[T]) →
    ∀ (jR : Mon.mk R ⟶ Mon.mk A) (jT : Mon.mk T ⟶ Mon.mk B),
      IsIso ((λ_ A).inv ≫ (t ≫ jR.hom) ▷ A ≫ μ[A]) →
      (∀ (D : H) [MonObj D] [IsCommMonObj D] (f : Mon.mk R ⟶ Mon.mk D),
        IsIso ((λ_ D).inv ≫ (t ≫ f.hom) ▷ D ≫ μ[D]) →
        ∃! g : Mon.mk A ⟶ Mon.mk D, jR ≫ g = f) →
      IsIso ((λ_ B).inv ≫ (t ≫ φ.hom ≫ jT.hom) ▷ B ≫ μ[B]) →
      (∀ (D : H) [MonObj D] [IsCommMonObj D] (f : Mon.mk T ⟶ Mon.mk D),
        IsIso ((λ_ D).inv ≫ (t ≫ φ.hom ≫ f.hom) ▷ D ≫ μ[D]) →
        ∃! g : Mon.mk B ⟶ Mon.mk D, jT ≫ g = f) →
      ∃ ψ : Mon.mk A ⟶ Mon.mk B,
        jR ≫ ψ = φ ≫ jT ∧
        (∀ ψ' : Mon.mk A ⟶ Mon.mk B, jR ≫ ψ' = φ ≫ jT → ψ' = ψ) ∧
        ∃ qt : (⨁ fun _ : I ↦ regular A) ≅ (comap ψ.hom).obj (regular B),
          (∀ i : I,
            (biproduct.ι (fun _ : I ↦ regular A) i).hom ≫ qt.hom.hom =
              ψ.hom ≫ (ρ_ B).inv ≫ B ◁ (b i ≫ jT.hom) ≫ μ[B]) ∧
          ((∑ i : I,
            (biproduct.π (fun _ : I ↦ regular R) i).hom ≫ jR.hom ≫
              (biproduct.ι (fun _ : I ↦ regular A) i).hom) ≫ qt.hom.hom =
            q.hom.hom ≫ jT.hom) ∧
          (∀ f : (⨁ fun _ : I ↦ regular A) ⟶ (comap ψ.hom).obj (regular B),
            (∑ i : I,
              (biproduct.π (fun _ : I ↦ regular R) i).hom ≫ jR.hom ≫
                (biproduct.ι (fun _ : I ↦ regular A) i).hom) ≫ f.hom =
              q.hom.hom ≫ jT.hom → f = qt.hom)

/-- Localization preserves the specified finite basis, with the unique scalar map,
its explicit summand formula, its integral-to-localized square, and linear uniqueness.

Source: Stacks, sites-modules.tex, Tags 0EMC (lemma-simple-invert) and 0EMD
(lemma-simple-invert-module); blueprint parent
`det-prop-sfb-cartesian-coefficients-finite-free`, inverting-ell sentence.
(blueprint: lem-sfb-localized-basis-coefficients)

Proof:
1. Using sk-def-sfb-sheaf-tensor, ring-object multiplication and module actions are
compatible bilinear operations on sections. The finite biproduct is the tuple sheaf.
The inverse of q gives restriction-compatible R-linear coordinates c_i, with
u = sum phi(c_i(u)) b_i and c_i(sum phi(r_j)b_j) = r_i.
2. The composite jT phi inverts t. The universal property of jR gives the unique
psi, and psi sends s = jR(t) and its inverse to v = jT(phi(t)) and its inverse.
3. Apply lem-sfb-ring-localization-sheafification to both localizations. Together with
lem-pc-sites-sheafification-underlying-sets and
lem-weil-pbc-site-sheafification-sections-local this expresses local sections as
jR(r)s^(-n) or jT(u)v^(-n). Equality of fractions holds locally precisely after a
further restriction and multiplication by a sufficiently large power of t or phi(t).
Denominators and powers may vary over the cover.
4. Define Q(a_i) = sum psi(a_i) jT(b_i). Ring distributivity and the restriction action
of sk-def-sfb-change-of-scalars give an A-linear morphism of the internal modules in
sk-def-sfb-module-objects. The scalar square gives Q jR^I = jT q.
5. Locally write x = jT(u)v^(-n). The tuple jR(c_i(u))s^(-n) maps to x, so Q is
locally surjective, using the local fraction description of step 3.
6. For Q(a_i) = 0, finitely refine the covers and clear denominators to write all
coordinates as jR(r_i)s^(-N). Then sum phi(r_i)b_i is killed locally by phi(t)^k.
Apply c_i to obtain t^k r_i = 0. Since s is invertible, every a_i vanishes locally,
hence globally by separatedness. This uses killing powers, never cancellation.
7. The local preimages from step 5 agree on overlaps by step 6. Sheaf gluing produces
a unique global preimage, compatible with restrictions, addition and A-scalars.
Consequently Q is the required internal A-module isomorphism qt.
8. A competing A-linear map satisfying the square agrees with Q on each standard
generator, whose image is jT(b_i). Linearity forces equality on all tuples. For empty
I all sums are empty and the same statements hold; in step 6 use N = 0.
-/
theorem sheaf_localizedBasisCoefficients
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    @LocalizedBasisCoefficients.{_, _, uI} (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory
      (@sheafIsAbelian C _ Ab.{w} _ _ J
        (hasSheafifyEssentiallySmallSite J Ab.{w})) := by
  sorry

end CategoryTheory.Mod
