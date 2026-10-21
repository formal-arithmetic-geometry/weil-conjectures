/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.TraceFormula.SpaceLineModuleProjInput
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward

/-!
# The graded section algebra of a line module and étale base change

Source: Stacks Project, Spaces-Morphisms, Tag 03M9; Properties of Spaces, Tag 03LX;
Descent on Spaces, Tag 0D3C, section-algebra and evaluation paragraphs
(blueprint: lem-trf-space-section-algebra-etale-base-change).

The section-limit characterization uses the existing cartesian scheme-test realization
of the given small-étale line module. It specifies the direct-image homogeneous sheaves,
their multiplication, and their adjunction evaluations, including degree zero. No section
algebra is selected from a bare existence statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}

/-- Restrict the actual tensor section `1 ⊗ s` to an open lying over its domain.
Source: Stacks, Tags 0095, 0096 and 0D3C
(blueprint: lem-trf-space-section-algebra-etale-base-change). -/
def sectionAlgebraPullSection {U V : Scheme.{u}} (g : U ⟶ V) (M : V.Modules)
    (A : V.Opens) (B : U.Opens) (h : B ≤ g ⁻¹ᵁ A) (s : Γ(M, A)) :
    Γ((Scheme.Modules.tensorPullback g).obj M, B) :=
  ((Scheme.Modules.tensorPullback g).obj M).val.map (homOfLE h).op
    (Scheme.Modules.tensorPullbackSection g M A s)

/-- Evaluate a section of a coefficient sheaf on a scheme test of the space.
The arrow is an actual tensor-pullback map; multiplication by a local scalar therefore
gives the usual formula `a ⊗ s ↦ a s|_W`.
Source: Stacks, Tag 0D3C, maps `psi_d`, and Tag 03D7
(blueprint: lem-trf-space-section-algebra-etale-base-change). -/
def sectionAlgebraImage (f : F ⟶ yoneda.obj T) (L : TestLineFamily F)
    (B : ℕ → T.left.Modules)
    (ev : ∀ (W : SchemeTests F) (n : ℕ),
      (Scheme.Modules.tensorPullback (testToBase f W).left).obj (B n) ⟶
        (L.module W).tensorPow n)
    (V : T.left.Opens) (W : SchemeTests F)
    (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V)
    (n : ℕ) (s : Γ(B n, V)) : Γ((L.module W).tensorPow n, ⊤) :=
  (ev W n).app ⊤
    (sectionAlgebraPullSection (testToBase f W).left (B n) V ⊤ h s)

/-- A section algebra with its full section-limit and adjunction normalizations.
`sections` is the limit universal property: a section is exactly a compatible family
on all scheme tests over the open. On étale tests these are the sections of `L^n`;
the existing cartesian realization extends them to arbitrary tests.
`evaluation_cartesian` says that the evaluation of a test is the tensor pullback of the
evaluation of every test it maps to, through the canonical composition, tensor-power and
line-family comparisons. Restricting to the open subtests over each open of the base,
`sections` then fixes every local generator `1 ⊗ s`, so the maps `evaluation` are the
adjunction counits on every test, not only on tests lying over a single open.
`sum` and `sum_mul` make the underlying algebra the sheaf coproduct of its homogeneous
pieces, with the indicated products.
Source: Stacks, Tags 03M8, 03M9 and 0D3C
(blueprint: lem-trf-space-section-algebra-etale-base-change). -/
structure SpaceSectionAlgebra (f : F ⟶ yoneda.obj T) (L : TestLineFamily F) where
  degree : ℕ → T.left.Modules
  degree_quasiCoherent (n : ℕ) : (degree n).IsQuasicoherent
  graded : GradedSheafAlgebra degree
  total : QuasiCoherentAlgebra T.left
  inclusion (n : ℕ) : degree n ⟶ total.obj.toModule
  sum : IsColimit (Cofan.mk total.obj.toModule inclusion)
  sum_mul (m n : ℕ) (V : T.left.Opens) (a : Γ(degree m, V))
      (b : Γ(degree n, V)) :
    (inclusion (m + n)).app V (graded.mul m n V a b) =
      @id (total.obj.right.obj.obj (op V)) ((inclusion m).app V a) *
        @id (total.obj.right.obj.obj (op V)) ((inclusion n).app V b)
  sum_unit (V : T.left.Opens) (r : Γ(T.left, V)) :
    (inclusion 0).app V (graded.unit.val.app (op V) r) = total.obj.hom.hom.app (op V) r
  evaluation (W : SchemeTests F) (n : ℕ) :
    (Scheme.Modules.tensorPullback (testToBase f W).left).obj (degree n) ⟶
      (L.module W).tensorPow n
  naturality (V : T.left.Opens) {W W' : SchemeTests F} (j : W ⟶ W')
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V)
      (h' : (⊤ : W'.left.left.Opens) ≤ (testToBase f W').left ⁻¹ᵁ V)
      (n : ℕ) (s : Γ(degree n, V)) :
    sectionAlgebraImage f L degree evaluation V W h n s =
      L.powerMap j n (sectionAlgebraImage f L degree evaluation V W' h' n s)
  evaluation_cartesian {W W' : SchemeTests F} (j : W ⟶ W') (n : ℕ)
      (w : j.left.left ≫ (testToBase f W').left = (testToBase f W).left) :
    (Scheme.Modules.tensorPullbackCompositionIso j.left.left (testToBase f W').left
        (testToBase f W).left w).hom.app (degree n) ≫
      (Scheme.Modules.tensorPullback j.left.left).map (evaluation W' n) ≫
      (Scheme.Modules.boundaryPullbackPowIso j.left.left (L.module W') n ≪≫
        Scheme.Modules.boundaryTensorPowIso (L.pullbackIso j) n).hom =
    evaluation W n
  sections (V : T.left.Opens) (n : ℕ)
      (s : ∀ (W : SchemeTests F),
        (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V →
          Γ((L.module W).tensorPow n, ⊤))
      (hs : ∀ (W W' : SchemeTests F) (j : W ⟶ W')
        (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V)
        (h' : (⊤ : W'.left.left.Opens) ≤ (testToBase f W').left ⁻¹ᵁ V),
        s W h = L.powerMap j n (s W' h')) :
    ∃! a : Γ(degree n, V), ∀ (W : SchemeTests F)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V),
      sectionAlgebraImage f L degree evaluation V W h n a = s W h
  mul (V : T.left.Opens) (W : SchemeTests F)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V)
      (m n : ℕ) (a : Γ(degree m, V)) (b : Γ(degree n, V)) :
    sectionAlgebraImage f L degree evaluation V W h (m + n) (graded.mul m n V a b) =
      ((L.module W).tensorPowAddIso m n).inv.app ⊤
        (Scheme.Modules.tmulSection (sectionAlgebraImage f L degree evaluation V W h m a)
          (sectionAlgebraImage f L degree evaluation V W h n b))
  unit (V : T.left.Opens) (W : SchemeTests F)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V)
      (r : Γ(T.left, V)) :
    sectionAlgebraImage f L degree evaluation V W h 0 (graded.unit.val.app (op V) r) =
      Scheme.Modules.unitSectionsEquiv ⊤ ((testToBase f W).left.appLE V ⊤ h r)

/-- The adjunction evaluation of a section algebra on one test chart.
Source: Stacks, Tag 0D3C (blueprint: lem-trf-space-section-algebra-etale-base-change). -/
def SpaceSectionAlgebra.image {f : F ⟶ yoneda.obj T} {L : TestLineFamily F}
    (A : SpaceSectionAlgebra f L) (V : T.left.Opens) (W : SchemeTests F)
    (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V)
    (n : ℕ) (s : Γ(A.degree n, V)) : Γ((L.module W).tensorPow n, ⊤) :=
  sectionAlgebraImage f L A.degree A.evaluation V W h n s

/-- A graded base-change isomorphism, fixed on the local tensor generators of every
homogeneous sheaf. The total comparison is the sum of these homogeneous comparisons;
the product and unit equations say that it is a graded algebra comparison. `evaluation`
identifies the pulled-back evaluations on every chart and every local tensor generator.
Source: Stacks, Tags 03LX and 0D3C
(blueprint: lem-trf-space-section-algebra-etale-base-change). -/
structure SpaceSectionAlgebraBaseChange {F' : (Over S)ᵒᵖ ⥤ Type u} {T' : Over S}
    {f : F ⟶ yoneda.obj T} {f' : F' ⟶ yoneda.obj T'} {L : TestLineFamily F}
    (k : F' ⟶ F) (g : T' ⟶ T) (A : SpaceSectionAlgebra f L)
    (A' : SpaceSectionAlgebra f' (L.pullback k)) where
  degree (n : ℕ) : (Scheme.Modules.tensorPullback g.left).obj (A.degree n) ≅ A'.degree n
  total : (Scheme.Modules.tensorPullback g.left).obj A.total.obj.toModule ≅
    A'.total.obj.toModule
  inclusion (n : ℕ) :
    (Scheme.Modules.tensorPullback g.left).map (A.inclusion n) ≫ total.hom =
      (degree n).hom ≫ A'.inclusion n
  mul (V : T.left.Opens) (m n : ℕ) (a : Γ(A.degree m, V)) (b : Γ(A.degree n, V)) :
    (degree (m + n)).hom.app (g.left ⁻¹ᵁ V)
        (Scheme.Modules.tensorPullbackSection g.left (A.degree (m + n)) V
          (A.graded.mul m n V a b)) =
      A'.graded.mul m n (g.left ⁻¹ᵁ V)
        ((degree m).hom.app (g.left ⁻¹ᵁ V)
          (Scheme.Modules.tensorPullbackSection g.left (A.degree m) V a))
        ((degree n).hom.app (g.left ⁻¹ᵁ V)
          (Scheme.Modules.tensorPullbackSection g.left (A.degree n) V b))
  unit (V : T.left.Opens) :
    (degree 0).hom.app (g.left ⁻¹ᵁ V)
        (Scheme.Modules.tensorPullbackSection g.left (A.degree 0) V
          (A.graded.unit.val.app (op V) (1 : Γ(T.left, V)))) =
      A'.graded.unit.val.app (op (g.left ⁻¹ᵁ V)) (1 : Γ(T'.left, g.left ⁻¹ᵁ V))
  evaluation (V : T.left.Opens) (W : SchemeTests F')
      (h' : (⊤ : W.left.left.Opens) ≤ (testToBase f' W).left ⁻¹ᵁ (g.left ⁻¹ᵁ V))
      (h : (⊤ : W.left.left.Opens) ≤
        (testToBase f ((CostructuredArrow.map k).obj W)).left ⁻¹ᵁ V)
      (n : ℕ) (s : Γ(A.degree n, V)) :
    A'.image (g.left ⁻¹ᵁ V) W h' n
        ((degree n).hom.app (g.left ⁻¹ᵁ V)
          (Scheme.Modules.tensorPullbackSection g.left (A.degree n) V s)) =
      A.image V ((CostructuredArrow.map k).obj W) h n s

/-- Agreement with ordinary Zariski direct image and its normalized counit whenever
the source is a scheme. The invertible module is the actual scheme-test pullback of
the given line module, and the counit identity fixes the direct-image comparison.
Source: Stacks, discussion preceding Tag 03M9; Descent, Tags 03DX and 03LC
(blueprint: lem-trf-space-section-algebra-etale-base-change). -/
def SpaceSectionAlgebra.AgreesWithSchemes {f : F ⟶ yoneda.obj T} {L : TestLineFamily F}
    (A : SpaceSectionAlgebra f L) : Prop :=
  ∀ (U : Over S) (k : yoneda.obj U ⟶ F) (_ : IsIso k),
    ∃ e : ∀ n : ℕ, A.degree n ≅
      (Scheme.Modules.pushforward (testToBase f (CostructuredArrow.mk k)).left).obj
        ((L.module (CostructuredArrow.mk k)).tensorPow n),
      ∀ n : ℕ, A.evaluation (CostructuredArrow.mk k) n =
        (Scheme.Modules.tensorPullback (testToBase f (CostructuredArrow.mk k)).left).map
            (e n).hom ≫
          (Scheme.Modules.tensorPullbackSectionAdjunction
            (testToBase f (CostructuredArrow.mk k)).left).counit.app
              ((L.module (CostructuredArrow.mk k)).tensorPow n)

/-- The section algebra is quasi-coherent and formation, multiplication, and evaluation
commute with every étale scheme base change. A Cartesian square is specified by its
universal property, so the result applies to every realization of `X ×_T T'`.

Source: Stacks, Tags 03M9, 03LX and 0D3C
(blueprint: lem-trf-space-section-algebra-etale-base-change).

Proof:
1. Trivialize L on an étale scheme atlas. Each tensor power is locally the structure
module, including its canonical zeroth power, so is quasi-coherent (03G9, 03DL).
2. Quasi-compact separated pushforward preserves quasi-coherence (03M9). The inverse
Zariski/étale equivalence is restriction to opens (03DX, 03LC). Its sections are precisely
the compatible chart sections of each tensor power (03M8). Cartesian scheme-test descent
of the line module gives the identical section-limit property used in `sections`.
3. Multiply compatible sections with the tensor-power product. Restriction commutes with
this product; associativity, commutativity, bilinearity and the unit follow on line
trivializations. Take the coproduct in module sheaves. Coproduct closure of quasi-coherent
modules makes the resulting commutative algebra quasi-coherent. These give `graded`,
`total`, `sum`, `sum_mul` and `sum_unit`.
4. Transpose the chart projections through tensor pullback/direct image adjunction.
The evaluation sends a local tensor a ⊗ s to a times the restricted section. These
counits commute with pullback along every map of tests (03D7, 0097), which is
`evaluation_cartesian`. Summing the counits gives the graded evaluation, because the
left adjoint preserves coproducts.
The tensor formula proves the multiplication and unit equations of the model.
5. For étale g, the base-changed chart diagrams identify their compatible sections
unchanged (03LX). Tensor pullback commutes with tensor powers, starting with the unit
in degree zero (03EL). Under the scheme Zariski/étale comparison the coefficient
pullback is the actual scheme tensor pullback. This gives the degree isomorphisms.
6. Sum these isomorphisms. The same chart section products give the multiplication
and unit equations. On local tensors both evaluation paths send a ⊗ s to a s|_W, so
they agree. This is the equation `evaluation` in the base-change structure, in every
degree; it also gives the equality on the coproduct evaluation.
7. If the source is a scheme, the Zariski/étale comparison identifies the line module
with its ordinary invertible module, its tensor powers and direct images (03LC).
Both counits have the same local tensor formula. Hence the comparison satisfies
`AgreesWithSchemes`, before and after base change. Empty schemes, empty opens, and
the degree-zero structure module are included throughout. -/
theorem space_section_algebra_etale_base_change
    (S : Scheme.{u}) (T : Over S) (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hqc : IsQuasiCompactPresheafMap f) (hsep : IsSeparatedPresheafMap f)
    (L : X.Modules) (hL : X.IsLineModule L) :
    ∃ A : SpaceSectionAlgebra f (lineTestFamily X L hL),
      A.AgreesWithSchemes ∧
      ∀ (T' : Over S) (g : T' ⟶ T) (_ : Etale g.left)
        (F' : (Over S)ᵒᵖ ⥤ Type u) (h : F' ⟶ X.obj.obj) (f' : F' ⟶ yoneda.obj T')
        (_ : IsPullback h f' f (yoneda.map g)),
        ∃ A' : SpaceSectionAlgebra f' ((lineTestFamily X L hL).pullback h),
          Nonempty (SpaceSectionAlgebraBaseChange h g A A') ∧ A'.AgreesWithSchemes := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
