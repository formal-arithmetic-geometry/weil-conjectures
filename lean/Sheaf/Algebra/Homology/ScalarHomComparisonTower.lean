/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomData
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.ScalarHomTensorCoherence

/-! # Evaluation-defined scalar Hom comparisons in coefficient towers

Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 07A4, and the formal
coefficient-tower argument in the proof of the blueprint node
(blueprint: lem-pur-scalar-hom-comparison-tower).

The comparison is the existing `WeilConjectures.coefficientBaseChangeHom`.
It uses evaluation on Hom tensor P, the symmetry-equivalent convention of the
node's P tensor Hom. The tensor comparisons are normalized on K-flat complexes.
Only tensor-tower and identity equations are assumed; Hom maps need not be invertible.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe c v r w

open CategoryTheory Opposite WeilConjectures SheafOfModules

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- Evaluation-transpose scalar Hom maps are natural and respect coefficient towers
and the identity coefficient map, without flatness or boundedness assumptions.
Source: Stacks Project, sites-cohomology.tex, Tags 08J9 (equation-internal-hom)
and 07A4 (lemma-pullback-tensor-product); the tower argument is formal, rather than
an additional theorem asserted in Stacks
(blueprint: lem-pur-scalar-hom-comparison-tower).

Proof:
1. Use the closed adjunction of lem-sf-ringed-derived-closed-symmetric-monoidal.
Its Hom bijection is injective. Uncurrying h gives evaluation after h tensor 1.
Naturality gives e'(H(f,g) tensor 1) = g e(1 tensor f). Equivalently, use the
node's P tensor Hom convention by symmetry throughout.
2. The existing coefficientBaseChangeHom is the transpose of inverse tensor
comparison followed by scalar-extended evaluation. Thus its uncurry is F(e)t,
where t is the inverse tensor comparison; the same definition applies to each leg.
3. For f : P' → P and g : Q → Q', uncurry both naturality routes.
Naturality of t moves F(f) through it, evaluation naturality replaces g e(1 tensor f)
by e'(H(f,g) tensor 1), and naturality of t moves F(H(f,g)) back through it.
Both uncurried maps agree, so injectivity proves naturality in both variables.
4. Put F = T_a, G = T_b, K = GF, J' = T_(ab), H = H_R(P,Q).
Uncurrying d = G(c_a) followed by c_b gives K(e) G(t_a) t_b:
use the defining equation for c_b, naturality of t_b at c_a, and the defining
equation for c_a. This computation does not invert either Hom comparison.
5. Invert and rearrange the assumed tensor-tower equation from
lem-sfb-scalar-hom-tensor-coherence. It says that G(t_a) t_b followed by
alpha at the tensor equals tensor(alpha_H,alpha_P) followed by t_(ab).
In the node's convention, precomposing with alpha_P inverse tensor 1 gives
alpha_(P tensor H) t_K (alpha_P inverse tensor 1)
= t_(ab) (1 tensor alpha_H).
6. Uncurry after the endpoint Hom transport H(alpha_P inverse,alpha_Q).
The result is alpha_Q K(e) t_K (alpha_P inverse tensor 1).
Naturality of alpha at e and Step 5 identify this with
J'(e) t_(ab) (1 tensor alpha_H), the uncurry of alpha_H followed by c_(ab).
Injectivity proves exactly the displayed tower equality, including both endpoints.
7. For I = T_id and u : I ≅ Id, rearrange the assumed identity tensor equation
to u_(P tensor X) t_id = u_P tensor u_X. Uncurry the transported c_id;
naturality of u at evaluation and this tensor equation give e(1 tensor u_H).
This is the uncurry of u_H, proving the identity assertion under the scalar unitor. -/
theorem scalarHomComparisonTower
    (M : ScalarHomModels.{c, v, r, w} J)
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a)
    (htower : ∀ {R S V : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ V)
      (P Q : DerivedCategory (scalarModules J R)),
      (M.scalar b).derived.map ((μ a).iso.hom.app (P, Q)) ≫
          (μ b).iso.hom.app ((M.scalar a).derived.obj P, (M.scalar a).derived.obj Q) ≫
          (M.closed V).tensor.map (Prod.mkHom
            ((scalarHomExtensionComp M a b).hom.app P)
            ((scalarHomExtensionComp M a b).hom.app Q)) =
        (scalarHomExtensionComp M a b).hom.app ((M.closed R).tensor.obj (P, Q)) ≫
          (μ (a ≫ b)).iso.hom.app (P, Q))
    (hid : ∀ (R : Sheaf J CommRingCat.{max c v r})
      (P Q : DerivedCategory (scalarModules J R)),
      (M.closed R).tensor.map (Prod.mkHom
          ((scalarHomExtensionId M R).inv.app P) ((scalarHomExtensionId M R).inv.app Q)) =
        (scalarHomExtensionId M R).inv.app ((M.closed R).tensor.obj (P, Q)) ≫
          (μ (𝟙 R)).iso.hom.app (P, Q)) :
    (∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
      (P Q P' Q' : DerivedCategory (scalarModules J R)) (f : P' ⟶ P) (g : Q ⟶ Q'),
      (M.scalar a).derived.map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g)) ≫
          coefficientBaseChangeHom (M.closed R) (M.closed S) (M.scalar a).derived
            (μ a).iso P' Q' =
        coefficientBaseChangeHom (M.closed R) (M.closed S) (M.scalar a).derived
            (μ a).iso P Q ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J S).map
            (Prod.mkHom ((M.scalar a).derived.map f).op ((M.scalar a).derived.map g))) ∧
    (∀ {R S V : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ V)
      (P Q : DerivedCategory (scalarModules J R)),
      (M.scalar b).derived.map
          (coefficientBaseChangeHom (M.closed R) (M.closed S) (M.scalar a).derived
            (μ a).iso P Q) ≫
          coefficientBaseChangeHom (M.closed S) (M.closed V) (M.scalar b).derived
            (μ b).iso ((M.scalar a).derived.obj P) ((M.scalar a).derived.obj Q) ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J V).map (Prod.mkHom
            ((scalarHomExtensionComp M a b).inv.app P).op
            ((scalarHomExtensionComp M a b).hom.app Q)) =
        (scalarHomExtensionComp M a b).hom.app
            ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≫
          coefficientBaseChangeHom (M.closed R) (M.closed V) (M.scalar (a ≫ b)).derived
            (μ (a ≫ b)).iso P Q) ∧
    (∀ (R : Sheaf J CommRingCat.{max c v r})
      (P Q : DerivedCategory (scalarModules J R)),
      coefficientBaseChangeHom (M.closed R) (M.closed R) (M.scalar (𝟙 R)).derived
          (μ (𝟙 R)).iso P Q ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom
            ((scalarHomExtensionId M R).inv.app P).op
            ((scalarHomExtensionId M R).hom.app Q)) =
        (scalarHomExtensionId M R).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q))) := by
  sorry

end CategoryTheory
