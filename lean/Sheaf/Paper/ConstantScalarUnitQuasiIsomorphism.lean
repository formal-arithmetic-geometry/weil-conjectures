/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.ConstantScalarStrictUnit
public import Sheaf.Paper.DerivedCompleteOnSlices
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-! # The regular coefficient scalar unit is a quasi-isomorphism

Source: Bhatt--Scholze, Propositions 3.1.10, 3.2.3(1), 4.2.8,
Definition 3.5.2 and Lemma 6.8.2(1)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism).

Positive exponent m is indexed by n = m-1. The strict tower, tensor,
normalized unit and mapping cocone are those of the recorded dependencies.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ConstantScalarUnitQuasiIsomorphism
open ConstantScalarStrictUnit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : Scheme.{t})

/-- The actual restricted quotient tower of the regular source complex.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism). -/
abbrev tower := (integralScalarTowerFunctor l E L ι Y).obj (regularComplex l E Y)

/-- Its termwise product B, before localization.
Source: Bhatt--Scholze, Proposition 3.1.10
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism). -/
abbrev product := ∏ᶜ (fun n : ℕ ↦ (tower l E L ι Y).obj (op n))

/-- The first component of the specified normalized unit.
Source: Bhatt--Scholze, Lemma 6.8.2(1), strict coordinate refinement
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism). -/
def inclusion (η : regularComplex l L Y ⟶
    (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) :
    regularComplex l L Y ⟶ product l E L ι Y :=
  η ≫ CochainComplex.mappingCocone.fst (boundary l E Y L ι)

/-- The prescribed quotient leg u_n inverse composed with pi_n.
Its tensor formula is fixed by quotientCoordinates, rather than a choice of isomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism). -/
def leg (η : regularComplex l L Y ⟶
    (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) (n : ℕ) :=
  inclusion l E L ι Y η ≫ Pi.π (fun m : ℕ ↦ (tower l E L ι Y).obj (op m)) n

/-- The normalized unit is a quasi-isomorphism, with its ordinary-limit, derived-product,
Roos-triangle and inverse-projection identifications; the self-extension is complete.
Source: Bhatt--Scholze, Propositions 3.1.10 (p.17), 3.2.3(1) (p.18), 4.2.8 (p.29),
Definition 3.5.2 (p.24), Lemma 6.8.2(1) (pp.58--59)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism).

Proof:
1. lem-weil-l-adic-extension-integers-dvr and lem-weil-valued-dvr-finite-quotients
make every positive target quotient finite and its reductions surjective, also in
ramified extensions.
2. def-weil-pbc-constant-sheaf, lem-pe-ring-sheafification-underlying-sets and
lem-weil-pbc-site-sheafification-sections-local lift quotient sections locally.
The reductions are therefore locally surjective, i.e. epimorphisms of sheaves; the
sheafified sectionwise cokernel is zero, so they are epimorphic in modules
(def-weil-sheaf-of-modules-category).
3. The multiplication isomorphisms of lem-weil-constant-scalar-strict-unit identify
the strict tower with the target quotient tower. By
lem-weil-pbc-module-sheaves-limits-sectionwise its ordinary limit is R_L[0],
with exactly the quotient legs (def-weil-completed-integral-coefficients).
4. lem-weil-proetale-surjective-tower-derived-limit gives that 1-s is degreewise epi
and its kernel inclusion is the ordinary limit inclusion. Outside degree zero all
terms vanish.
5. lem-weil-degreewise-epi-kernel-cocone-qis gives a quasi-isomorphism from this
kernel with unshifted component the inclusion and shifted component zero.
Uniqueness in lem-weil-constant-scalar-strict-unit identifies it with eta.
6. The same surjective-tower theorem identifies the actual termwise product as a
derived product and supplies the distinguished triangle with these very first and
second arrows, hence the Roos triangle of def-weil-derived-limit.
7. def-weil-abstract-derived-category inverts eta. For j_n = fst followed by pr_n,
the strict normalization says eta followed by j_n is the prescribed quotient leg.
Compose its localized equality with the inverse of Q(eta) to obtain the displayed
projection compatibility. The strict cone is precisely the representative used by
def-weil-integral-scalar-extension on the regular K-flat complex.
8. For the identity extension, the strict-unit reductionUnits assertion identifies
the first map with the canonical derived reduction units. The triangle therefore
proves def-weil-derived-complete. All arguments allow arbitrary Y, including the
empty scheme and disconnected schemes, and require no finiteness of Y.
-/
theorem regular_scalar_unit_quasi_isomorphism (D : FiniteFieldDatum.{d}) (_hl : l ≠ D.p)
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y))
    (_hη : quotientCoordinates l E Y L ι η ∧ zeroSecondComponent l E Y L ι η) :
    (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l L (n + 1))) ∧
    (∀ n : ℕ, Sheaf.IsLocallySurjective (integralCoefficientSheafTransition l L Y n)) ∧
    (∃ e : regularComplex l L Y ≅ limit (tower l E L ι Y),
      ∀ n : ℕ, e.hom ≫ limit.π (tower l E L ι Y) (op n) = leg l E L ι Y η n) ∧
    QuasiIso η ∧
    Nonempty (IsLimit (Fan.mk (DerivedCategory.Q.obj (product l E L ι Y))
      (fun n : ℕ ↦ DerivedCategory.Q.map
        (Pi.π (fun m : ℕ ↦ (tower l E L ι Y).obj (op m)) n)))) ∧
    (∃ δ : DerivedCategory.Q.obj (product l E L ι Y) ⟶
        (DerivedCategory.Q.obj (regularComplex l L Y))⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk (DerivedCategory.Q.map (inclusion l E L ι Y η))
        (DerivedCategory.Q.map (boundary l E Y L ι)) δ ∈
          distTriang (DerivedCategory (integralTowerModules l L Y))) ∧
    (∃ e : DerivedCategory.Q.obj
        ((integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) ≅
          DerivedCategory.Q.obj (regularComplex l L Y),
      e.inv = DerivedCategory.Q.map η ∧
      ∀ n : ℕ, e.hom ≫ DerivedCategory.Q.map (leg l E L ι Y η n) =
        DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst (boundary l E Y L ι) ≫
            Pi.π (fun m : ℕ ↦ (tower l E L ι Y).obj (op m)) n)) ∧
    IntegralOnSlice.IsComplete l E Y none
      (DerivedCategory.Q.obj (regularComplex l E Y)) := by
  sorry

end WeilConjectures.ConstantScalarUnitQuasiIsomorphism
