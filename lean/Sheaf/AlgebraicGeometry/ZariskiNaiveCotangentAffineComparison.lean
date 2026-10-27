/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.CategoryTheory.SheafPolynomialCotangentComparison
public import Sheaf.RingTheory.NaiveCotangentComparison
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.Topology.InverseImageStalk
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Etale.Kaehler

/-! # Affine Zariski comparison for the naive cotangent complex

Source: Stacks Project, More on Morphisms, Tag 0D0I (lemma-NL-affine).
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ZariskiNaiveCotangent

variable {R B : CommRingCat.{u}} (φ : R ⟶ B)

/-- The standard polynomial presentation, with every element of B as a generator.
Source: Stacks, Algebra, section-netherlander and More on Morphisms, Tag 0D0I
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison). -/
def presentation : Algebra.CotangentResolution.Naive.Presentation (Arrow.mk φ) where
  ring := CommRingCat.of (MvPolynomial B R)
  base := CommRingCat.ofHom MvPolynomial.C
  augmentation := CommRingCat.ofHom (MvPolynomial.eval₂Hom φ.hom id)
  triangle := by ext r; simp
  surjective b := ⟨MvPolynomial.X b, MvPolynomial.eval₂_X φ.hom id b⟩

/-- Apply the existing tilde functor termwise to the standard ring complex.
Source: Stacks, Tag 0D0I
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison). -/
def associatedComplex : CochainComplex (Spec B).Modules ℤ :=
  ((tilde.functor B).mapHomologicalComplex (.up ℤ)).obj
    (Algebra.CotangentResolution.Naive.complex (presentation φ))

/-- The canonical sheaf presentation of O_U over f⁻¹ O_V.
Source: Stacks, Tags 0D0I and 08TW
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison). -/
abbrev sheafPresentation :=
  SheafPolynomialCotangent.canonical (Scheme.Modules.tensorPullbackRingMap (Spec.map φ))

/-- Send a base-ring element to a section of the actual inverse-image ring sheaf.
Source: Stacks, Tag 0D0I, construction from the inverse-image adjunction unit
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison). -/
def coefficientSection (W : (Spec B).Opens) :
    R →+* (TopCat.Sheaf.inverseImageRing (Spec.map φ).base (Spec R).sheaf).obj.obj
      (op W) :=
  (((TopCat.Sheaf.inverseImageRing (Spec.map φ).base (Spec R).sheaf).obj.map
    (homOfLE (le_top : W ≤ ⊤)).op).hom).comp
    ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (TopologicalSpace.Opens.map (Spec.map φ).base) CommRingCat.{u} _ _).unit.app
        (Spec R).sheaf).hom.app (op ⊤)).hom.comp (Scheme.ΓSpecIso R).inv.hom)

/-- A ring element as a regular function on an arbitrary open of its spectrum.
Source: Stacks, Tags 01HV and 0D0I
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison). -/
def functionSection (W : (Spec B).Opens) : B →+* (Spec B).sheaf.obj.obj (op W) :=
  ((Spec B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp (Scheme.ΓSpecIso B).inv.hom

/-- The polynomial on local coefficients and local variables, followed by sheafification.
Source: Stacks, Tag 0D0I, canonical map of presentations
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison). -/
def polynomialSection (W : (Spec B).Opens) :
    MvPolynomial B R →+*
      (SheafPolynomialCotangent.polynomialSheaf
        (TopCat.Sheaf.inverseImageRing (Spec.map φ).base (Spec R).sheaf)
        (sheafPresentation φ).generators).obj.obj (op W) :=
  ((toSheafify _ (SheafPolynomialCotangent.polynomials
    (TopCat.Sheaf.inverseImageRing (Spec.map φ).base (Spec R).sheaf)
    (sheafPresentation φ).generators)).app (op W)).hom.comp
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (coefficientSection φ W))
        (fun b ↦ MvPolynomial.X (functionSection W b)))

open Algebra.CotangentResolution.Naive

/-- A canonical comparison, pinned on conormal classes and universal differential tensors.
The target is any model of the canonical presentation provided by the existing sheaf
cotangent interface; its quotient and degree-zero coordinates are part of that interface.
Source: Stacks, Tag 0D0I
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison). -/
structure Comparison (K : SheafPolynomialCotangent.Model (sheafPresentation φ)) where
  map : associatedComplex φ ⟶ K.complex
  quasiIso : QuasiIso map
  derived : (SheafPolynomialCotangent.localization (Spec B).sheaf).obj
      (associatedComplex φ) ≅
    (SheafPolynomialCotangent.localization (Spec B).sheaf).obj K.complex
  derived_hom : derived.hom =
    (SheafPolynomialCotangent.localization (Spec B).sheaf).map map
  conormal_formula : ∀ (W : (Spec B).Opens)
    (h : RingHom.ker (presentation φ).augmentation.hom),
    ∃ j : (SheafPolynomialCotangent.kernelIdeal (sheafPresentation φ)).sections W,
      (j : (SheafPolynomialCotangent.polynomialSheaf
        (TopCat.Sheaf.inverseImageRing (Spec.map φ).base (Spec R).sheaf)
        (sheafPresentation φ).generators).obj.obj (op W)) =
          polynomialSection φ W (h : (presentation φ).ring) ∧
      (map.f (-1)).val.app (op W)
        (tilde.toOpen ((complex (presentation φ)).X (-1)) W
          ((conormalIso (presentation φ)).inv (kernelClass (presentation φ) h))) =
        K.quotient.val.app (op W) j
  differential_formula : ∀ (W : (Spec B).Opens) (b : B) (h : MvPolynomial B R),
    K.degreeZero.hom.val.app (op W)
      ((map.f 0).val.app (op W)
        (tilde.toOpen ((complex (presentation φ)).X 0) W
          ((differentialsIso (presentation φ)).inv
            (tensorGenerator (presentation φ) b h)))) =
      SheafPolynomialCotangent.tensorD (sheafPresentation φ) (op W)
        (functionSection W b) (polynomialSection φ W h)

/-- The canonical affine Zariski comparison is a quasi-isomorphism, hence an isomorphism
in the unbounded derived category. No finiteness, Noetherian or flatness assumptions occur.
Source: Stacks Project, More on Morphisms, Tag 0D0I (lemma-NL-affine)
(blueprint: lem-sfb-zariski-naive-cotangent-affine-comparison).

Proof, following the five DAG steps:
1. The inverse-image adjunction unit maps R to sections of f⁻¹ O_V. Restrict coefficients
   and send x_b to the variable of the regular function b. Evaluation commutes with this
   polynomial map, so it maps the kernel into the sheaf kernel and its square into the
   local kernel square. Universal differentials give the degree-zero map. Both boundaries
   send [h] to dh. The tilde/Gamma adjunction of
   lem-weil-pbc-affine-tilde-gamma-adjunction gives the chain map with these formulas.
2. At p in Spec B, put q = φ⁻¹(p). The affine stalk and tilde-stalk localization nodes,
   and lem-weil-pbc-topological-inverse-image-stalk, identify the stalks with B_p, R_q
   and the localization of the ring complex. The germ of each global element is its
   fraction over 1. The map R to B_p extends to R_q since φ(R\q) consists of units.
3. Exact module localization, the polynomial differential basis, H1 localization and
   the cokernel/differentials comparison identify the cohomology of the canonical map
   (C_{B/R})_p to C_{B_p/R}. Degree -1 is H1 localization; degree 0 is localization of
   Kaehler differentials. Both are isomorphisms, and all other degrees vanish.
4. lem-sfb-naive-cotangent-localize-base gives the comparison to C_{B_p/R_q}.
   lem-sfb-naive-cotangent-stalk-comparison identifies the sheaf-model stalk with it.
   On kernel classes and tensors, the stalk of our map sends r to r/1 and x_b to
   x_{b/1}. Thus it is the composite of the two localization comparisons.
5. Exactness of module stalks commutes with cohomology. All cohomology maps are
   isomorphisms on stalks, so their kernels and cokernels vanish by
   lem-weil-pbc-module-stalk-exact. This proves quasi-isomorphism. Localization at
   quasi-isomorphisms supplies the displayed derived isomorphism with the specified
   underlying map. If B is zero, its spectrum is empty and stalk detection still applies.
-/
theorem zariski_naive_cotangent_affine_comparison
    (K : SheafPolynomialCotangent.Model (sheafPresentation φ)) :
    Nonempty (Comparison φ K) := by
  sorry

end AlgebraicGeometry.ZariskiNaiveCotangent
