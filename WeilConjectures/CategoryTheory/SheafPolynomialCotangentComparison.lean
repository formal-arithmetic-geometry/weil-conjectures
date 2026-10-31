/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.CategoryTheory.Sites.InverseImageDifferentials
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Sites.SheafifiedDifferentialsCokernel
import WeilConjectures.AlgebraicGeometry.ImagePresheafSheafificationIso
import WeilConjectures.CategoryTheory.LocallyDenseCotangentH1
import WeilConjectures.RingTheory.PresentationsHomotopyEquivalent
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Polynomial presentations of the sheaf naive cotangent complex

Source: Stacks Project, Modules on Sites, Tags 08TY (lemma-NL-up-to-qis) and
08TS (lemma-differential-seq)
(blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison).

The polynomial sheaf is constructed by sheafification. A model records the actual
conormal quotient through its local surjectivity and kernel, and a complex supported
in degrees -1 and 0. Maps and isomorphisms are normalized on conormal classes and
universal differential tensors. Thus the existential statement specifies the canonical
constructions up to their unique compatible isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.SheafPolynomialCotangent

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The underlying set sheaf, without changing its universe.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
abbrev sets (B : Sheaf J CommRingCat.{u}) : Sheaf J (Type u) :=
  (sheafCompose J (forget CommRingCat)).obj B

/-- The polynomial presheaf with coefficient and generator restrictions.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def polynomials (A : Sheaf J CommRingCat.{u}) (E : Sheaf J (Type u)) :
    Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (MvPolynomial (E.obj.obj U) (A.obj.obj U))
  map r := CommRingCat.ofHom (MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (A.obj.map r).hom) (fun e ↦ MvPolynomial.X (E.obj.map r e)))
  map_id U := by
    apply CommRingCat.hom_ext
    ext a e <;> simp
  map_comp r s := by
    apply CommRingCat.hom_ext
    ext a e <;> simp

/-- The sheaf polynomial algebra `A[E]`.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def polynomialSheaf (A : Sheaf J CommRingCat.{u}) (E : Sheaf J (Type u)) :
    Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat.{u}).obj (polynomials A E)

/-- The polynomial coefficient inclusion before sheafification.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def coefficientMap (A : Sheaf J CommRingCat.{u}) (E : Sheaf J (Type u)) :
    A.obj ⟶ polynomials A E where
  app U := CommRingCat.ofHom MvPolynomial.C
  naturality U V r := by ext a; simp [polynomials]

/-- The coefficient map `A → A[E]` from the sheafification adjunction.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def base (A : Sheaf J CommRingCat.{u}) (E : Sheaf J (Type u)) :
    A ⟶ polynomialSheaf A E :=
  ⟨coefficientMap A E ≫ toSheafify J (polynomials A E)⟩

/-- Evaluation of sectionwise polynomials on the given generators.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def evaluationPresheaf {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)
    {E : Sheaf J (Type u)} (α : E ⟶ sets B) : polynomials A E ⟶ B.obj where
  app U := CommRingCat.ofHom (MvPolynomial.eval₂Hom (f.hom.app U).hom (α.hom.app U))
  naturality U V r := by
    apply CommRingCat.hom_ext
    change (MvPolynomial.eval₂Hom (f.hom.app V).hom (α.hom.app V)).comp
      (polynomials A E |>.map r).hom =
        (B.obj.map r).hom.comp
          (MvPolynomial.eval₂Hom (f.hom.app U).hom (α.hom.app U))
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [polynomials]
    · intro e
      simp [polynomials, sets]
      rfl

/-- The canonical evaluation `A[E] → B`.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def evaluation {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)
    {E : Sheaf J (Type u)} (α : E ⟶ sets B) : polynomialSheaf A E ⟶ B :=
  ((sheafificationAdjunction J CommRingCat).homEquiv _ B).symm
    (evaluationPresheaf f α)

/-- A generating sheaf with sheaf-surjective polynomial evaluation. This does not
require sectionwise surjectivity of either the generators or polynomial evaluation.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
structure Presentation {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B) where
  generators : Sheaf J (Type u)
  values : generators ⟶ sets B
  surjective : Presheaf.IsLocallySurjective J (evaluation f values).hom

/-- Identity generators give a sheaf-surjective evaluation: every local `b` is
represented by the polynomial `X b`, and the adjunction preserves its evaluation.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison).
Proof: insert `X b` into the sectionwise polynomial ring and then apply its
sheafification unit. The triangle identity evaluates this section to `b`.
Sectionwise surjectivity implies local surjectivity. -/
theorem canonical_surjective {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B) :
    Presheaf.IsLocallySurjective J (evaluation f (𝟙 (sets B))).hom := by
  sorry

/-- The canonical presentation underlying `NL`.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def canonical {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B) : Presentation f :=
  ⟨sets B, 𝟙 _, canonical_surjective f⟩

/-- Local membership in the square of the evaluation kernel. This allows products
of kernel sections after passing to a cover, as required for an ideal sheaf square.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def LocallyInKernelSquare {A B : Sheaf J CommRingCat.{u}} {f : A ⟶ B}
    (P : Presentation f) (U : Cᵒᵖ)
    (j : (polynomialSheaf A P.generators).obj.obj U) : Prop :=
  ∃ S : Sieve U.unop, S ∈ J U.unop ∧
    ∀ (V : C) (r : V ⟶ U.unop), S r →
      (polynomialSheaf A P.generators).obj.map r.op j ∈
        (RingHom.ker ((evaluation f P.values).hom.app (op V)).hom) ^ 2

/-- The kernel ideals form an ideal sheaf: ring naturality preserves kernels and
zero is detected locally in the target sheaf.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison).
Proof: for restriction apply naturality of evaluation to a kernel section. For local
membership, evaluation of the section restricts to zero on the given covering sieve;
separatedness of the underlying target ring sheaf makes it zero globally. -/
theorem kernel_ideal_axioms {A B : Sheaf J CommRingCat.{u}} {f : A ⟶ B}
    (P : Presentation f) :
    (∀ {U V : C} (r : V ⟶ U)
      (j : (polynomialSheaf A P.generators).obj.obj (op U)),
      j ∈ RingHom.ker ((evaluation f P.values).hom.app (op U)).hom →
      (polynomialSheaf A P.generators).obj.map r.op j ∈
        RingHom.ker ((evaluation f P.values).hom.app (op V)).hom) ∧
    (∀ (U : C) (j : (polynomialSheaf A P.generators).obj.obj (op U)) (S : Sieve U),
      S ∈ J U → (∀ (V : C) (r : V ⟶ U), S r →
        (polynomialSheaf A P.generators).obj.map r.op j ∈
          RingHom.ker ((evaluation f P.values).hom.app (op V)).hom) →
      j ∈ RingHom.ker ((evaluation f P.values).hom.app (op U)).hom) := by
  sorry

/-- The actual ideal subsheaf `ker(A[E] → B)`.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def kernelIdeal {A B : Sheaf J CommRingCat.{u}} {f : A ⟶ B}
    (P : Presentation f) : RingedSiteIdeal (polynomialSheaf A P.generators) where
  sections U := RingHom.ker ((evaluation f P.values).hom.app (op U)).hom
  restriction := (kernel_ideal_axioms P).1
  local_mem := (kernel_ideal_axioms P).2

/-- The actual sheaf differential term `Ω[A[E]/A] ⊗ B`.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def differentialTerm {A B : Sheaf J CommRingCat.{u}} {f : A ⟶ B}
    (P : Presentation f) : ringedSiteModules.{u} (siteModuleRings B) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u, u, u} (evaluation f P.values)
    (SheafDifferentials.omega.{u, u, u} (base A P.generators))

/-- The universal tensor generator `b ⊗ dp`, in the existing sheaf tensor product.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def tensorD {A B : Sheaf J CommRingCat.{u}} {f : A ⟶ B} (P : Presentation f)
    (U : Cᵒᵖ) (b : B.obj.obj U)
    (p : (polynomialSheaf A P.generators).obj.obj U) :
    (differentialTerm P).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings B).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u, u, u} (evaluation f P.values)
      (SheafDifferentials.omega.{u, u, u} (base A P.generators)))).app U)
    (b ⊗ₜ[_, ((evaluation f P.values).hom.app U).hom]
      (SheafDifferentials.derivation.{u, u, u} (base A P.generators)).d p)

/-- A model of exactly `[J/J² → Ω[A[E]/A] ⊗ B]`. The quotient is specified by
local surjectivity and its exact kernel, not by an arbitrary replacement module.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
structure Model {A B : Sheaf J CommRingCat.{u}} {f : A ⟶ B}
    (P : Presentation f) where
  complex : CochainComplex (ringedSiteModules.{u} (siteModuleRings B)) ℤ
  degreeZero : complex.X 0 ≅ differentialTerm P
  supported : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (complex.X i)
  quotient : (kernelIdeal P).module ⟶
    (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (evaluation f P.values))).obj
        (complex.X (-1))
  quotient_surjective : Presheaf.IsLocallySurjective J
    ((PresheafOfModules.toPresheaf _).map quotient.val)
  quotient_kernel : ∀ (U : Cᵒᵖ) (j : (kernelIdeal P).sections U.unop),
    quotient.val.app U j = 0 ↔ LocallyInKernelSquare P U j
  differential_formula : ∀ (U : Cᵒᵖ) (j : (kernelIdeal P).sections U.unop),
    degreeZero.hom.val.app U
      ((complex.d (-1) 0).val.app U (quotient.val.app U j)) = tensorD P U 1 j

/-- Renaming generators, with coefficients fixed, before sheafification.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def polynomialMapPresheaf (A : Sheaf J CommRingCat.{u})
    {E E' : Sheaf J (Type u)} (v : E ⟶ E') : polynomials A E ⟶ polynomials A E' where
  app U := CommRingCat.ofHom (MvPolynomial.rename (R := A.obj.obj U) (v.hom.app U)).toRingHom
  naturality U V r := by
    apply CommRingCat.hom_ext
    change (MvPolynomial.rename (v.hom.app V)).toRingHom.comp
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map r).hom)
        (fun e ↦ MvPolynomial.X (E.obj.map r e))) =
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map r).hom)
        (fun e ↦ MvPolynomial.X (E'.obj.map r e))).comp
          (MvPolynomial.rename (v.hom.app U)).toRingHom
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro e
      simp

/-- The canonical generator map on polynomial sheaves.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def polynomialMap (A : Sheaf J CommRingCat.{u})
    {E E' : Sheaf J (Type u)} (v : E ⟶ E') :
    polynomialSheaf A E ⟶ polynomialSheaf A E' :=
  (presheafToSheaf J CommRingCat.{u}).map (polynomialMapPresheaf A v)

/-- The usual derived category with its standard universe-sized localization.
Source: Stacks 05RU and 08TY
(blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
abbrev derived (B : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (ringedSiteModules.{u} (siteModuleRings B)) _ _
    (HasDerivedCategory.standard _)

/-- Localization of actual complexes; no new derived category is constructed.
Source: Stacks 05RU and 08TY
(blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
def localization (B : Sheaf J CommRingCat.{u}) :
    CochainComplex (ringedSiteModules.{u} (siteModuleRings B)) ℤ ⥤ derived B :=
  @DerivedCategory.Q (ringedSiteModules.{u} (siteModuleRings B)) _ _
    (HasDerivedCategory.standard _)

/-- A chain map induced by a generator map, fixed by the formulas on kernel classes
and universal differential tensors. The quantified kernel representative exists since
polynomial evaluation commutes with a map over `B`.
Source: Stacks 08TY (blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
structure GeneratorMap {A B : Sheaf J CommRingCat.{u}} {f : A ⟶ B}
    {P P' : Presentation f} (K : Model P) (K' : Model P')
    (v : P.generators ⟶ P'.generators) (_hv : v ≫ P'.values = P.values) where
  chainMap : K.complex ⟶ K'.complex
  conormal_formula : ∀ (U : Cᵒᵖ) (j : (kernelIdeal P).sections U.unop)
    (j' : (kernelIdeal P').sections U.unop),
    (j' : (polynomialSheaf A P'.generators).obj.obj U) =
        (polynomialMap A v).hom.app U j →
      (chainMap.f (-1)).val.app U (K.quotient.val.app U j) = K'.quotient.val.app U j'
  differential_formula : ∀ (U : Cᵒᵖ) (b : B.obj.obj U)
    (p : (polynomialSheaf A P.generators).obj.obj U),
    K'.degreeZero.hom.val.app U
      ((chainMap.f 0).val.app U (K.degreeZero.inv.val.app U (tensorD P U b p))) =
        tensorD P' U b ((polynomialMap A v).hom.app U p)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- All comparisons, including their canonical normalization and cokernel map.
`models (canonical f)` is precisely `NL_{B/A}`; `lambda` is the image of the map
induced by the given `E → B`. Thus none of the displayed isomorphisms is arbitrary.
Source: Stacks 08TY and 08TS
(blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison). -/
structure Comparison {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B) where
  models : ∀ P : Presentation f, Model P
  maps : ∀ (P P' : Presentation f) (v : P.generators ⟶ P'.generators)
    (hv : v ≫ P'.values = P.values), GeneratorMap (models P) (models P') v hv
  quasiIso : ∀ (P P' : Presentation f) (v : P.generators ⟶ P'.generators)
    (hv : v ≫ P'.values = P.values), QuasiIso (maps P P' v hv).chainMap
  identity : ∀ P : Presentation f,
    (maps P P (𝟙 _) (Category.id_comp _)).chainMap = 𝟙 (models P).complex
  composition : ∀ (P P' P'' : Presentation f)
    (v : P.generators ⟶ P'.generators) (w : P'.generators ⟶ P''.generators)
    (hv : v ≫ P'.values = P.values) (hw : w ≫ P''.values = P'.values)
    (hvw : (v ≫ w) ≫ P''.values = P.values),
    (maps P P'' (v ≫ w) hvw).chainMap =
      (maps P P' v hv).chainMap ≫ (maps P' P'' w hw).chainMap
  lambda : ∀ P : Presentation f,
    (localization B).obj (models P).complex ≅
      (localization B).obj (models (canonical f)).complex
  lambda_hom : ∀ P : Presentation f,
    (lambda P).hom = (localization B).map
      (maps P (canonical f) P.values (Category.comp_id _)).chainMap
  naturality : ∀ (P P' : Presentation f) (v : P.generators ⟶ P'.generators)
    (hv : v ≫ P'.values = P.values),
    (localization B).map (maps P P' v hv).chainMap ≫ (lambda P').hom = (lambda P).hom
  cokernelIso : ∀ P : Presentation f,
    cokernel ((models P).complex.d (-1) 0) ≅ SheafDifferentials.omega.{u, u, u} f
  cokernel_formula : ∀ (P : Presentation f) (U : Cᵒᵖ) (b : B.obj.obj U)
    (p : (polynomialSheaf A P.generators).obj.obj U),
    ((cokernelIso P).hom.val.app U)
      ((cokernel.π ((models P).complex.d (-1) 0)).val.app U
        ((models P).degreeZero.inv.val.app U (tensorD P U b p))) =
      b • (SheafDifferentials.derivation.{u, u, u} f).d ((evaluation f P.values).hom.app U p)

/-- Every sheaf-surjective polynomial presentation gives the canonical naive
cotangent object, naturally under generator maps, with the canonical differential cokernel.
Source: Stacks Project, Modules on Sites, Tags 08TY and 08TS
(blueprint: lem-sfb-sheaf-polynomial-cotangent-comparison).

Proof, following the five DAG steps:
1. Take the sectionwise image `D` of `A[E] → B` before sheafification. The image
   sheafification lemma identifies `D#` with `B`; no sectionwise surjectivity is used.
2. Sheafify the sectionwise conormal complex over `D`. Exact module sheafification,
   local representation and equality identify its conormal term with the quotient
   specified by `Model.quotient_kernel`. Sheafification of differentials and tensors
   identifies its other term with `differentialTerm`. The generator formulas give
   the differential and every `GeneratorMap`.
3. Ring polynomial-presentation homotopy equivalence identifies its degree minus
   one homology with sheafified first cotangent homology of `D`. Functoriality in
   ring squares and the locally dense cotangent H1 lemma identify this with that
   of `B`, through the map on generators `E → B`.
4. The ring conormal sequence identifies the sectionwise cokernel with differentials
   of `D`. Exact sheafification and the differential-sheafification comparison identify
   this with `omega f`, by the displayed evaluation formula of `cokernel_formula`.
5. Both complexes vanish outside degrees minus one and zero, so the map to the
   identity-generator presentation is a quasi-isomorphism. Localize that actual map
   to obtain `lambda`. Polynomial evaluation and the formulas on conormal classes
   and differential tensors give identity, composition and strict naturality; hence
   every generator map is a quasi-isomorphism as well.
-/
theorem sheaf_polynomial_cotangent_comparison
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (A B : Sheaf J.toGrothendieck CommRingCat.{u}) (f : A ⟶ B) :
    Nonempty (Comparison f) := by
  sorry

end CategoryTheory.SheafPolynomialCotangent
