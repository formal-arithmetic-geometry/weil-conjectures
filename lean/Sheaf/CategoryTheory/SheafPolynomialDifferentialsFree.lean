/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Sheaf.CategoryTheory.SheafPolynomialCotangentComparison
public import Sheaf.CategoryTheory.Sites.FreeModuleUniversalProperty
import Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Polynomial sheaf differentials are free after evaluation

Source: Stacks Project, Deformation Theory, Tag 08UJ, first proof paragraph;
Modules on Sites, Tags 08TP, 0GMW and 04BL
(blueprint: lem-sfb-sheaf-polynomial-differentials-free).

The polynomial sheaf, evaluation, and generator maps are the existing constructions
of `SheafPolynomialCotangent`. Scalar extension uses the existing sheaf tensor, whose
implementation puts the coefficient factor first: `b ⊗ dp` represents `dp ⊗ b`.
No presentation-surjectivity assumption is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace CategoryTheory.SheafPolynomialDifferentials

open SheafPolynomialCotangent

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The actual differential sheaf after scalar extension along arbitrary evaluation.
Unlike `SheafPolynomialCotangent.differentialTerm`, this needs no surjective presentation.
Source: Stacks 08UJ, first proof paragraph
(blueprint: lem-sfb-sheaf-polynomial-differentials-free). -/
def term {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)
    (E : Sheaf J (Type u)) (α : E ⟶ sets B) :
    ringedSiteModules.{u} (SheafFreeModule.ring B) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u, u, u} (SheafPolynomialCotangent.evaluation f α)
    (SheafDifferentials.omega.{u, u, u} (base A E))

/-- Image of the local tensor `dp ⊗ b` in the sheaf tensor product, represented in
its implementation as `b ⊗ dp`. This uses the actual module-sheafification unit.
Source: Stacks 08UJ and 0GMW
(blueprint: lem-sfb-sheaf-polynomial-differentials-free). -/
def tensorD {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)
    (E : Sheaf J (Type u)) (α : E ⟶ sets B) (U : Cᵒᵖ)
    (b : B.obj.obj U) (p : (polynomialSheaf A E).obj.obj U) :
    (term f E α).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (SheafFreeModule.ring B).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u, u, u}
      (SheafPolynomialCotangent.evaluation f α)
      (SheafDifferentials.omega.{u, u, u} (base A E)))).app U)
    (b ⊗ₜ[_, ((SheafPolynomialCotangent.evaluation f α).hom.app U).hom]
      (SheafDifferentials.derivation.{u, u, u} (base A E)).d p)

/-- The polynomial variable section `[e]`, after the ring sheafification unit.
Source: Stacks 08UJ, polynomial generators
(blueprint: lem-sfb-sheaf-polynomial-differentials-free). -/
def variableSection (A : Sheaf J CommRingCat.{u}) (E : Sheaf J (Type u))
    (U : Cᵒᵖ) (e : E.obj.obj U) : (polynomialSheaf A E).obj.obj U :=
  (toSheafify J (polynomials A E)).app U (MvPolynomial.X e)

/-- The generator-normalized free-module isomorphisms and their naturality for every
map of generator sheaves over B. The differential map is characterized on ALL local
`dp ⊗ b`, so it is the induced map on differentials, rather than an arbitrary arrow.
Source: Stacks 08UJ, first proof paragraph and subsequent change of generators;
Modules on Sites 08TP, 0GMW, 03CY and 04BL
(blueprint: lem-sfb-sheaf-polynomial-differentials-free).

Proof:
1. On each U, put Q(U) = A(U)[E(U)]. The arbitrary-variable polynomial differential
   basis (lem-weil-pbc-polynomial-ring-kahler-basis-any-variables) gives the isomorphism
   from the free B(U)-module to Omega[Q(U)/A(U)] tensored with B(U), sending [e] to
   dX_e tensor 1. Its inverse sends a tensor of sum(q_e dX_e) with b to
   sum(eval(q_e) b [e]). Tensor symmetry gives the coefficient-first implementation
   (def-weil-pbc-module-tensor-product).
2. Universal derivations commute with coefficient and generator restrictions
   (def-weil-pbc-kahler-differentials). Both restriction composites take b[e] to
   dX_(e restricted) tensor (b restricted); the basis proves they agree.
3. Sheafifying differentials (lem-trf-sheafified-module-differentials-cokernel) and
   tensors (lem-pc-sites-module-sheafification-tensor) identifies the sheafification
   of these sectionwise tensors with term. This is B-linear on pure tensors and
   hence by the module-sheafification adjunction
   (lem-pc-sites-module-sheafification-interface).
4. Sheafify the sectionwise inverse isomorphisms. The source is the existing free
   module sheaf (lem-trf-free-module-sheaf-universal-property); the composite has
   precisely the displayed generator normalization. That universal property makes
   the normalized isomorphism canonical.
5. For v over B, rename polynomial variables. The universal derivation gives
   dp to d(v(p)); scalar extension and sheafification give the uniquely specified F.
   Both composites in the naturality square send [e'] to d[v(e')] tensor 1.
   Equality follows by the free-module universal property. No step uses surjectivity,
   finiteness, or nonemptiness of E.
-/
theorem sheaf_polynomial_differentials_free
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (A B : Sheaf J.toGrothendieck CommRingCat.{u}) (f : A ⟶ B) :
    ∃ Φ : ∀ (E : Sheaf J.toGrothendieck (Type u)) (α : E ⟶ sets B),
      (SheafFreeModule.free B).obj E ≅ term f E α,
      (∀ (E : Sheaf J.toGrothendieck (Type u)) (α : E ⟶ sets B)
        (U : Cᵒᵖ) (e : E.obj.obj U),
        (Φ E α).hom.val.app U ((SheafFreeModule.generatorRaw B E).hom.app U e) =
          tensorD f E α U 1 (variableSection A E U e)) ∧
      (∀ (E E' : Sheaf J.toGrothendieck (Type u))
        (α : E ⟶ sets B) (α' : E' ⟶ sets B) (v : E' ⟶ E),
        v ≫ α = α' →
        (∃! F : term f E' α' ⟶ term f E α,
          ∀ (U : Cᵒᵖ) (b : B.obj.obj U)
            (p : (polynomialSheaf A E').obj.obj U),
            F.val.app U (tensorD f E' α' U b p) =
              tensorD f E α U b ((polynomialMap A v).hom.app U p)) ∧
        (∀ F : term f E' α' ⟶ term f E α,
          (∀ (U : Cᵒᵖ) (b : B.obj.obj U)
            (p : (polynomialSheaf A E').obj.obj U),
            F.val.app U (tensorD f E' α' U b p) =
              tensorD f E α U b ((polynomialMap A v).hom.app U p)) →
          (Φ E' α').hom ≫ F = (SheafFreeModule.free B).map v ≫ (Φ E α).hom)) := by
  sorry

end CategoryTheory.SheafPolynomialDifferentials
