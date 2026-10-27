/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# Signed boundary of the product Hom complex

Source: Stacks Project, More on Algebra, Tag 0A5X, and Derived Categories, Tag 0152;
the extension to abelian categories and signed comparison are the node's explicit argument
(blueprint: lem-sfb-product-hom-ses-boundary).

The product complex is Mathlib's `CochainComplex.HomComplex`. The two auxiliary
constructions give precomposition and its canonical cohomology-to-derived-Hom map.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CochainComplex.HomComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition on the product Hom complex, using the actual chain map in every coordinate.
Source: Stacks Project, Tag 0A5X, differential formula and its functoriality
(blueprint: lem-sfb-product-hom-ses-boundary). -/
def precompMap {X Y : CochainComplex 𝒜 ℤ} (a : X ⟶ Y) (I : CochainComplex 𝒜 ℤ) :
    CochainComplex.HomComplex Y I ⟶ CochainComplex.HomComplex X I where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ (Cochain.ofHom a).comp z (zero_add n)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun z z' ↦ Cochain.comp_add _ z z' _ }
  comm' _ m _ := AddCommGrpCat.ext (fun z ↦ δ_ofHom_comp a z m)

/-- The canonical map from product-Hom cohomology to morphisms in the derived category.
It first passes to chain-homotopy classes, then localizes, then uses `Q`'s shift comparison.
Source: Stacks Project, Tags 0A5X and 070I
(blueprint: lem-sfb-product-hom-ses-boundary). -/
noncomputable def homologyToDerived [HasDerivedCategory.{w} 𝒜]
    (X I : CochainComplex 𝒜 ℤ) (n : ℤ)
    (z : (CochainComplex.HomComplex X I).homology n) :
    DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj I)⟦n⟧ :=
  (DerivedCategory.quotientCompQhIso 𝒜).inv.app X ≫
    DerivedCategory.Qh.map (CohomologyClass.toHom ((homologyAddEquiv X I n) z)) ≫
    (DerivedCategory.quotientCompQhIso 𝒜).hom.app (I⟦n⟧) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app I

/-- A termwise injective K-injective target turns a degreewise SES into a SES of product
Hom complexes. Under the canonical cohomology-to-derived-Hom identification, its degree-zero
boundary is negative composition with the signed derived SES boundary.
Source: Stacks Project, Tag 0A5X (product Hom), Tag 070I (K-injective localization),
and Tag 0152 (the derived boundary `-pr_A q⁻¹`); the signed comparison is agent-written
(blueprint: lem-sfb-product-hom-ses-boundary).

Proof: the mixed terms in two applications of the product-Hom differential cancel, so
`D² = 0`; precomposition by a chain map commutes with `D`. These are already built into
`HomComplex` and `precompMap`. In each coordinate, precomposition by the epimorphism `p`
is injective, its image is the kernel of restriction along `i` by the cokernel property,
and restriction along `i` is surjective by injectivity of the corresponding term of `I`.
Choose the extensions for all integer coordinates; no products in the abelian category
and no degreewise splitting are needed. This supplies `w` and the asserted short exactness.

A degree-j cocycle is a chain map to `I[j]`. Boundaries are exactly null-homotopic maps,
with the degree-minus-one homotopy rescaled by `(-1)^j`. Thus `homologyAddEquiv` followed
by `CohomologyClass.toHom` is the specified homotopy-class identification. The shift lemma
`lem-weil-pbc-kinjective-shift` and the localization bijection
`lem-weil-pbc-kinjective-hom-derived` make `homologyToDerived` bijective in every degree.

For `f : A ⟶ I`, choose a degree-zero graded extension `g : B → I`. Factor `Dg = hp`.
Then `Dh = 0`, since `D²g = 0` and `p` is degreewise epi. The lift-differentiate convention
for Mathlib's cohomology boundary gives `∂[f] = [h]`. Changing `g` by `tp` changes `h` by
`Dt`; changing `f` by a boundary and extending its homotopy leaves the class unchanged.
The cone-projection lemma `lem-pc-cone-short-exact-quasi-iso` inverts the actual map
`q : Cone(i) → C`. On the cone, the homotopy with components `H(x,a) = g(x)` has
differential `(-d_I g + g d_B, gi) = (-hp,f)`, hence identifies `hq` with `f[1] pr_A`.
Localize and cancel `Qq`: `Qh = Q(f)[1] Q(pr_A) (Qq)⁻¹ = -Q(f)[1] b`.
The component calculations apply to unbounded complexes and to nonsplit sequences. -/
theorem productHom_ses_boundary [HasDerivedCategory.{w} 𝒜]
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] [∀ r : ℤ, Injective (I.X r)] :
    (∀ (X : CochainComplex 𝒜 ℤ) (j : ℤ), Function.Bijective (homologyToDerived X I j)) ∧
      ∃ (w₀ : precompMap S.g I ≫ precompMap S.f I = 0)
        (hH : (ShortComplex.mk (precompMap S.g I) (precompMap S.f I) w₀).ShortExact),
        ∀ f : S.X₁ ⟶ I,
          homologyToDerived S.X₃ I 1
            ((hH.δ 0 1 (by decide))
              ((homologyAddEquiv S.X₁ I 0).symm (CohomologyClass.mk (Cocycle.ofHom f)))) =
            -(DerivedCategory.triangleOfSESδ hS ≫ (DerivedCategory.Q.map f)⟦(1 : ℤ)⟧') := by
  sorry

end CochainComplex.HomComplex
