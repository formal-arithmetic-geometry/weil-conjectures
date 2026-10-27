/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Relative Proj of an algebraic-space graded algebra

Source: Stacks Project, spaces-divisors.tex, Tags 084B, 084C and 085C and the
quadruple functor preceding 084B
(blueprint: lem-sfb-space-relative-proj-scheme-tests).

The structures below spell out the data and equations in the conclusion of the theorem.
They impose no additional hypotheses on its input. Tensor pullback and passage to the
Zariski site are the existing functors. Affine section identifications preserve products,
units and restrictions, so the scheme-test algebra cannot be replaced by an unrelated
algebra. The cartesian squares specify the canonical base-change isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The input of relative Proj, bundling precisely its homogeneous pieces, their
commutative unital algebra operations, and degreewise quasi-coherence.
Source: Stacks, Situation 084A (blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
structure SpaceProjInput (X : AlgebraicSpace S) where
  piece : ℕ → X.Modules
  algebra : EtaleGradedModuleAlgebra piece
  quasiCoherent : ∀ n, (piece n).IsQuasicoherent

/-- A graded algebra isomorphism, expressed on homogeneous module sheaves.
Source: Stacks, the diagram following 084C
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
structure SpaceProjGradedIso {X : AlgebraicSpace S} (A B : SpaceProjInput X) where
  degree (n : ℕ) : A.piece n ≅ B.piece n
  mul (m n : ℕ) (V : X.EtaleSite)
      (s : (A.piece m).val.obj (op V)) (t : (A.piece n).val.obj (op V)) :
    (degree (m + n)).hom.val.app (op V) (A.algebra.mul m n V s t) =
      B.algebra.mul m n V ((degree m).hom.val.app (op V) s)
        ((degree n).hom.val.app (op V) t)
  unit : A.algebra.unit ≫ (degree 0).hom = B.algebra.unit

/-- The pulled-back algebra is on the actual tensor-pulled homogeneous modules.
The equations fix its products and unit on local tensors, including their scalars.
Source: Stacks, 084B and 085C; Modules on Sites, 03D7
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
structure SpaceProjPullback {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : SpaceProjInput X) where
  algebra : EtaleGradedModuleAlgebra (fun n ↦ (moduleTensorPullback f).obj (A.piece n))
  quasiCoherent : ∀ n, ((moduleTensorPullback f).obj (A.piece n)).IsQuasicoherent
  mul (m n : ℕ) (V : X.EtaleSite) (q : ModuleChart f V)
      (b c : Y.structureSheaf.obj.obj (op q.left))
      (s : (A.piece m).val.obj (op V)) (t : (A.piece n).val.obj (op V)) :
    algebra.mul m n q.left (moduleTensorSection f (A.piece m) V q b s)
        (moduleTensorSection f (A.piece n) V q c t) =
      moduleTensorSection f (A.piece (m + n)) V q (b * c) (A.algebra.mul m n V s t)
  unit (V : X.EtaleSite) (q : ModuleChart f V)
      (r : X.structureSheaf.obj.obj (op V)) :
    moduleTensorSection f (A.piece 0) V q 1 (A.algebra.unit.val.app (op V) r) =
      algebra.unit.val.app (op q.left) (moduleChartScalar f V q r)

/-- The pulled-back input has the specified tensor modules, with no choice of module data.
Source: Stacks, 085C (blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
def SpaceProjPullback.input {X Y : AlgebraicSpace S} {f : Y ⟶ X}
    {A : SpaceProjInput X} (D : SpaceProjPullback f A) : SpaceProjInput Y :=
  ⟨fun n ↦ (moduleTensorPullback f).obj (A.piece n), D.algebra, D.quasiCoherent⟩

/-- A scheme's open subscheme as a chart of its representable algebraic space.
Source: Stacks, 03DX (blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
def spaceProjOpenChart (W : Over S) (V : W.left.Opens) : (schemeSpace W).EtaleSite :=
  (evaluationSchemeEtale W).obj ((gabberOpenEtale W.left).obj V)

/-- The affine-basis presentation of the Zariski algebra corresponding to tensor pullback.
The linear equivalences identify every homogeneous section, and respect restriction,
products and the structural unit. In particular degree zero need not equal O_W.
Source: Stacks, 084B; Descent, 03DX; Constructions, 01LH
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
structure SpaceProjSchemeAlgebra {X : AlgebraicSpace S} (A : SpaceProjInput X)
    (W : Over S) (g : schemeSpace W ⟶ X) (D : SpaceProjPullback g A) where
  affine : W.left.GradedAlgebraData
  sections (V : W.left.affineOpens) (n : ℕ) :
    affine.grading V n ≃ₗ[Γ(W.left, V.1)]
      Γ((evaluationZariskiRestriction W).obj ((moduleTensorPullback g).obj (A.piece n)), V.1)
  mul (m n : ℕ) (V : W.left.affineOpens)
      (s : affine.grading V m) (t : affine.grading V n) :
    HEq (sections V (m + n) ⟨s * t, SetLike.mul_mem_graded s.property t.property⟩)
      (D.algebra.mul m n (spaceProjOpenChart W V.1) (sections V m s) (sections V n t))
  unit (V : W.left.affineOpens) (r : Γ(W.left, V.1)) :
    HEq (sections V 0 ⟨algebraMap _ _ r,
      SetLike.algebraMap_mem_graded (affine.grading V) r⟩)
      (D.algebra.unit.val.app (op (spaceProjOpenChart W V.1))
        (W.left.restrictFunctorΓ.inv.app (op V.1) r))
  restriction {V U : W.left.affineOpens} (h : U ≤ V) (n : ℕ)
      (s : affine.grading V n) :
    sections U n ⟨affine.res h s, (affine.res h).map_mem s.property⟩ =
      ((evaluationZariskiRestriction W).obj ((moduleTensorPullback g).obj (A.piece n))).val.map
        (homOfLE (X := W.left.Opens) h).op (sections V n s)

/-- A scheme relative Proj, over S, and its projection to its scheme base.
Source: Stacks, 084B; Constructions, 01LH
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
def spaceProjScheme (W : Over S) (A : W.left.GradedAlgebraData) : Over S :=
  Over.mk (A.relProjHom ≫ W.hom)

/-- The structural projection of the ordinary scheme relative Proj.
Source: Stacks, 084B (blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
def spaceProjSchemeProjection (W : Over S) (A : W.left.GradedAlgebraData) :
    spaceProjScheme W A ⟶ W := Over.homMk A.relProjHom

/-- The ordinary scheme-Proj comparison induced by a graded algebra isomorphism.
Source: Stacks, the diagram following 084C
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
def spaceProjSchemeIso (W : Over S) {A B : W.left.GradedAlgebraData} (e : A ≅ B) :
    spaceProjScheme W B ⟶ spaceProjScheme W A :=
  Over.homMk (Scheme.GradedAlgebraData.relProjIsoOfIso e).hom
    (by
      change (Scheme.GradedAlgebraData.relProjIsoOfIso e).hom ≫
        (A.relProjHom ≫ W.hom) = B.relProjHom ≫ W.hom
      rw [← Category.assoc, Scheme.GradedAlgebraData.relProjIsoOfIso_hom_relProjHom])

/-- The ordinary scheme-Proj base-change comparison.
Source: Stacks, 084B; Constructions, 01O0
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
def spaceProjSchemeBaseChange {U W : Over S} (a : U ⟶ W)
    {A : W.left.GradedAlgebraData} {B : U.left.GradedAlgebraData}
    (D : Scheme.GradedAlgebraData.PullbackData a.left A B) :
    spaceProjScheme U B ⟶ spaceProjScheme W A :=
  Over.homMk D.relProjComparison (by
    change D.relProjComparison ≫ (A.relProjHom ≫ W.hom) =
      B.relProjHom ≫ U.hom
    rw [← Category.assoc, D.isPullback.w, Category.assoc, Over.w a])

/-- A coefficient system for the theorem's conclusion: normalized tensor algebras,
Zariski realizations, and their coefficient comparisons. The existence of this system
is asserted by the theorem, not required of its input.
Source: Stacks, 084B, 084C and 085C; Descent, 03DX
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
structure SpaceProjCoefficients (S : Scheme.{u}) where
  pullback {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : SpaceProjInput X) :
    SpaceProjPullback f A
  scheme {X : AlgebraicSpace S} (A : SpaceProjInput X) (W : Over S)
      (g : schemeSpace W ⟶ X) : SpaceProjSchemeAlgebra A W g (pullback g A)
  identity {X : AlgebraicSpace S} (A : SpaceProjInput X) :
    SpaceProjGradedIso (pullback (𝟙 X) A).input A
  identity_degree {X : AlgebraicSpace S} (A : SpaceProjInput X) (n : ℕ) :
    (identity A).degree n = (moduleTensorPullbackId X).app (A.piece n)
  composition {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (g : Z ⟶ Y)
      (A : SpaceProjInput X) :
    SpaceProjGradedIso (pullback g (pullback f A).input).input (pullback (g ≫ f) A).input
  composition_degree {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (g : Z ⟶ Y)
      (A : SpaceProjInput X) (n : ℕ) :
    (composition f g A).degree n = (moduleTensorComposition g f).app (A.piece n)
  isoPullback {X Y : AlgebraicSpace S} (f : Y ⟶ X) {A B : SpaceProjInput X}
      (e : SpaceProjGradedIso A B) :
    SpaceProjGradedIso (pullback f A).input (pullback f B).input
  isoPullback_degree {X Y : AlgebraicSpace S} (f : Y ⟶ X) {A B : SpaceProjInput X}
      (e : SpaceProjGradedIso A B) (n : ℕ) :
    (isoPullback f e).degree n = (moduleTensorPullback f).mapIso (e.degree n)
  schemeIso {X : AlgebraicSpace S} {A B : SpaceProjInput X} (e : SpaceProjGradedIso A B)
      (W : Over S) (g : schemeSpace W ⟶ X) : (scheme A W g).affine ≅ (scheme B W g).affine
  schemeIso_degree {X : AlgebraicSpace S} {A B : SpaceProjInput X}
      (e : SpaceProjGradedIso A B) (W : Over S) (g : schemeSpace W ⟶ X)
      (V : W.left.affineOpens) (n : ℕ) (s : (scheme A W g).affine.grading V n) :
    (scheme B W g).sections V n
        ⟨(schemeIso e W g).hom.app V s, ((schemeIso e W g).hom.app V).map_mem s.property⟩ =
      ((evaluationZariskiRestriction W).map
        ((moduleTensorPullback g).map (e.degree n).hom)).val.app (op V.1)
          ((scheme A W g).sections V n s)
  schemeComposition {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : SpaceProjInput X)
      (W : Over S) (g : schemeSpace W ⟶ Y) :
    (scheme A W (g ≫ f)).affine ≅ (scheme (pullback f A).input W g).affine
  schemeComposition_degree {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : SpaceProjInput X)
      (W : Over S) (g : schemeSpace W ⟶ Y) (V : W.left.affineOpens) (n : ℕ)
      (s : (scheme A W (g ≫ f)).affine.grading V n) :
    (scheme (pullback f A).input W g).sections V n
        ⟨(schemeComposition f A W g).hom.app V s,
          ((schemeComposition f A W g).hom.app V).map_mem s.property⟩ =
      ((evaluationZariskiRestriction W).map
        ((moduleTensorComposition g f).inv.app (A.piece n))).val.app (op V.1)
          ((scheme A W (g ≫ f)).sections V n s)
  schemeBaseChange {X : AlgebraicSpace S} (A : SpaceProjInput X)
      {U W : Over S} (a : U ⟶ W) (g : schemeSpace W ⟶ X) :
    Scheme.GradedAlgebraData.PullbackData a.left (scheme A W g).affine
      (scheme A U (evaluationSchemeMap a ≫ g)).affine
  schemeBaseChange_normalized {X : AlgebraicSpace S} (A : SpaceProjInput X)
      {U W : Over S} (a : U ⟶ W) (g : schemeSpace W ⟶ X)
      (V : W.left.affineOpens) (V' : U.left.affineOpens)
      (h : V'.1 ≤ a.left ⁻¹ᵁ V.1) (n : ℕ) (s : (scheme A W g).affine.grading V n)
      (q : ModuleChart (evaluationSchemeMap a) (spaceProjOpenChart W V.1))
      (hq : q.left = spaceProjOpenChart U V'.1)
      (ha : HEq q.hom.left.left (a.left.resLE V.1 V'.1 h)) :
    HEq ((scheme A U (evaluationSchemeMap a ≫ g)).sections V' n
      ⟨(schemeBaseChange A a g).map h s,
        ((schemeBaseChange A a g).map h).map_mem s.property⟩)
      (((moduleTensorComposition (evaluationSchemeMap a) g).hom.app (A.piece n)).val.app
        (op q.left) (moduleTensorSection (evaluationSchemeMap a)
          ((moduleTensorPullback g).obj (A.piece n)) (spaceProjOpenChart W V.1) q 1
            ((scheme A W g).sections V n s)))

/-- A realization of the scheme tests with their structural projections and naturality.
An IsPullback square is the comparison W times_X P = Proj_W(g-star A), with both
projections specified; its isoPullback is precisely the comparison isomorphism.
Source: Stacks, 084B (blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
structure SpaceProjRealization (C : SpaceProjCoefficients S) {X : AlgebraicSpace S}
    (A : SpaceProjInput X) where
  space : AlgebraicSpace S
  projection : space ⟶ X
  representable : IsRepresentable projection.hom.hom
  compare (W : Over S) (g : schemeSpace W ⟶ X) :
    yoneda.obj (spaceProjScheme W (C.scheme A W g).affine) ⟶ space.obj.obj
  cartesian (W : Over S) (g : schemeSpace W ⟶ X) :
    IsPullback (compare W g)
      (yoneda.map (spaceProjSchemeProjection W (C.scheme A W g).affine))
      projection.hom.hom g.hom.hom
  naturality {U W : Over S} (a : U ⟶ W) (g : schemeSpace W ⟶ X) :
    yoneda.map (spaceProjSchemeBaseChange a (C.schemeBaseChange A a g)) ≫ compare W g =
      compare U (evaluationSchemeMap a ≫ g)

/-- All comparisons required in the conclusion, simultaneously for every algebra.
Uniqueness preserves the scheme tests. Base-change arrows are cartesian, normalized
on those tests, and obey identity, composition and graded-isomorphism compatibility.
Source: Stacks, 084B, 084C and 085C
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
structure SpaceProjSystem (C : SpaceProjCoefficients S) where
  realization {X : AlgebraicSpace S} (A : SpaceProjInput X) : SpaceProjRealization C A
  unique {X : AlgebraicSpace S} (A : SpaceProjInput X) (Q : SpaceProjRealization C A) :
    ∃! e : (realization A).space ≅ Q.space,
      e.hom ≫ Q.projection = (realization A).projection ∧
        ∀ (W : Over S) (g : schemeSpace W ⟶ X),
          (realization A).compare W g ≫ e.hom.hom.hom = Q.compare W g
  iso {X : AlgebraicSpace S} {A B : SpaceProjInput X} (e : SpaceProjGradedIso A B) :
    (realization B).space ≅ (realization A).space
  iso_over {X : AlgebraicSpace S} {A B : SpaceProjInput X} (e : SpaceProjGradedIso A B) :
    (iso e).hom ≫ (realization A).projection = (realization B).projection
  iso_test {X : AlgebraicSpace S} {A B : SpaceProjInput X} (e : SpaceProjGradedIso A B)
      (W : Over S) (g : schemeSpace W ⟶ X) :
    (realization B).compare W g ≫ (iso e).hom.hom.hom =
      yoneda.map (spaceProjSchemeIso W (C.schemeIso e W g)) ≫ (realization A).compare W g
  baseChange {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : SpaceProjInput X) :
    (realization (C.pullback f A).input).space ⟶ (realization A).space
  baseChange_cartesian {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : SpaceProjInput X) :
    IsPullback (baseChange f A).hom (realization (C.pullback f A).input).projection.hom
      (realization A).projection.hom f.hom
  baseChange_test {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : SpaceProjInput X)
      (W : Over S) (g : schemeSpace W ⟶ Y) :
    (realization (C.pullback f A).input).compare W g ≫ (baseChange f A).hom.hom =
      yoneda.map (spaceProjSchemeIso W (C.schemeComposition f A W g)) ≫
        (realization A).compare W (g ≫ f)
  baseChange_id {X : AlgebraicSpace S} (A : SpaceProjInput X) :
    baseChange (𝟙 X) A = (iso (C.identity A)).inv
  baseChange_comp {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (g : Z ⟶ Y)
      (A : SpaceProjInput X) :
    baseChange g (C.pullback f A).input ≫ baseChange f A =
      (iso (C.composition f g A)).inv ≫ baseChange (g ≫ f) A
  baseChange_iso {X Y : AlgebraicSpace S} (f : Y ⟶ X) {A B : SpaceProjInput X}
      (e : SpaceProjGradedIso A B) :
    (iso (C.isoPullback f e)).hom ≫ baseChange f A = baseChange f B ≫ (iso e).hom

/-- The actual algebraic-space fibre product in the base-change conclusion.
Source: Stacks, 085C and 02X2
(blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
def SpaceProjSystem.baseChangeTarget {C : SpaceProjCoefficients S} (R : SpaceProjSystem C)
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : SpaceProjInput X) : AlgebraicSpace S :=
  ⟨Limits.pullback f.hom (R.realization A).projection.hom,
    (fibreProduct_isAlgebraicSpace Y (R.realization A).space X f
      (R.realization A).projection).1⟩

/-- The canonical base-change isomorphism, extracted from the specified cartesian square.
It goes from P_Y(f-star A) to Y times_X P_X(A), with the scheme-test normalization
and the identity, composition and graded-isomorphism equations in SpaceProjSystem.
Source: Stacks, 085C (blueprint: lem-sfb-space-relative-proj-scheme-tests). -/
def SpaceProjSystem.baseChangeIso {C : SpaceProjCoefficients S} (R : SpaceProjSystem C)
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : SpaceProjInput X) :
    (R.realization (C.pullback f A).input).space ≅ R.baseChangeTarget f A :=
  ObjectProperty.isoMk _ (R.baseChange_cartesian f A).flip.isoPullback

/-- Relative Proj over an algebraic space is representable by schemes, has its natural
ordinary scheme-test identifications, is uniquely characterized by them, and commutes
with arbitrary space base change and graded algebra isomorphisms. The input is exactly
SpaceProjInput: no finiteness, flatness, separation or Noetherian condition is used.

Source: Stacks Project, spaces-divisors.tex, Tags 084B, 084C and 085C, including the
quadruple functor preceding 084B
(blueprint: lem-sfb-space-relative-proj-scheme-tests).

Proof:
1. Tensor pullback preserves quasi-coherence by lem-sfb-space-module-pullback-quasicoherent.
   The ringed tensor comparison lem-weil-pbc-ringed-topoi-module-pullback-tensor gives
   products (b tensor s)(c tensor t) = bc tensor st and the unit. The scheme Zariski/etale
   equivalence lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identifies these
   operations on opens. Normalized moduleTensorComposition gives the associativity
   comparisons. These facts supply the coefficient system, including its affine sections
   and normalized base-change maps; no infinite direct-sum assertion on sections is used.
2. On a quasi-compact test T use quadruples (d,f,L,psi), d positive, L invertible, and
   psi from the d-th Veronese of f-star A to the tensor-power algebra of L, surjective
   in degree one. Identify two with the same f when, for m=ad=a'd' positive, an isomorphism
   L^a = (L')^a' intertwines psi in every degree an and a'n. Identity, inverse, and a
   common multiple of two witnesses give an equivalence relation. Invertible pullback
   and powers are lem-weil-pbc-invertible-pullback-tensor.
3. On any T take compatible families over all quasi-compact opens. To pull back along u,
   each quasi-compact open of its source has image contained in a quasi-compact open of T
   (take a finite affine cover of the image). Pull the quadruple back there. Choices
   agree on the quasi-compact union. Tensor pullback is a left adjoint, so preserves the
   degree-one surjection. The compatible remembered maps f glue because X is a sheaf.
   This defines a presheaf F and F to X, without quasi-compact intersection hypotheses.
4. For g:W to X, a section of h_W times_X F is a:T to W and a quadruple with f=g a.
   Replace f by a, keeping d,L,psi and all equivalence witnesses. Tensor composition
   identifies the sources of psi. This is inverse to composition with g, and extends
   over quasi-compact opens. The scheme Veronese-quotient theorem
   lem-sfb-scheme-proj-veronese-quotient-functor identifies it with the ordinary relative
   Proj. The formula preserves projection to W and commutes with every further test.
5. The scheme-test products are schemes, hence algebraic spaces. Apply
   lem-sfb-presheaf-space-target-bootstrap to F to X; F is an algebraic space and its
   projection is representable by schemes. For any second realization, evaluate its
   comparison at W=T on (id_T,q). This gives the unique comparison-preserving map on
   every section q. Reversing the construction proves it is an isomorphism and unique.
6. For f:Y to X send [d,b:T to Y,L,psi] to (b,[d,fb,L,psi]). The inverse replaces fb
   by b. Both retain all equivalence witnesses and commute with restriction, hence
   give the base-change cartesian square. The fibre product is an algebraic space by
   lem-trf-space-fibre-products-etale-covers. Identity retains the quadruple; successive
   changes along g and f and the direct change along gf retain the same data, giving
   the identity and composition equations after the normalized coefficient comparisons.
7. For e:A to B send a B-quadruple to the A-quadruple by precomposing psi with f-star e
   in degrees dn. Degree-one surjectivity is retained since e is invertible. Common-power
   witnesses are unchanged. The inverse uses e inverse. This is the ordinary induced
   scheme-Proj isomorphism on every test, and commutes with base change because the two
   homogeneous maps are the same psi composed with f-star e. -/
theorem exists_space_relativeProj_scheme_tests (S : Scheme.{u}) :
    ∃ C : SpaceProjCoefficients S, Nonempty (SpaceProjSystem C) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
