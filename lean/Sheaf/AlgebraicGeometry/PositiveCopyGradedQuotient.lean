/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
import Sheaf.AlgebraicGeometry.GradedSheafAlgebraTotal
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # The positive-copy graded algebra and its symmetric quotient

Source: Stacks Project, Morphisms, Tag 0B3I (lemma-finite-projective), the canonical
projective-bundle embedding; Modules, Tag 01CF (section-symmetric-exterior)
(blueprint: lem-trf-positive-copy-graded-quotient).

The total algebra is specified by its categorical coproduct cocone and its products on
homogeneous sections. Bijectivity of the canonical affine section-sum map is the graded
algebra identification: its multiplication and scalar map are fixed by the homogeneous
product and degree-zero equations. All cocone arrows are sheaf-module morphisms, so these
identifications commute with restriction, including arbitrary inclusions of affine opens.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace AlgebraicGeometry

/-- The degree-zero structure module and the positive copies of the given algebra module.
Source: Stacks Project, Morphisms, Tag 0B3I, explicit graded-quotient construction
(blueprint: lem-trf-positive-copy-graded-quotient). -/
noncomputable def positiveCopyPiece {X : Scheme.{u}} (E : X.CommAlgebraSheaf) :
    ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | _ + 1 => E.toModule

/-- The canonical linear map from the direct sum of homogeneous sections to total sections.
It is defined on every open, but is asserted to be bijective only on affine opens.
Source: Stacks Project, Schemes, Tag 01ID (lemma-colimit-quasi-coherent)
(blueprint: lem-trf-positive-copy-graded-quotient). -/
noncomputable def positiveCopySectionSum {X : Scheme.{u}} (E B : X.CommAlgebraSheaf)
    (i : ∀ n : ℕ, positiveCopyPiece E n ⟶ B.toModule) (U : X.Opens) :
    (⨁ n : ℕ, (positiveCopyPiece E n).val.obj (op U)) →ₗ[Γ(X, U)]
      B.toModule.val.obj (op U) :=
  DirectSum.toModule Γ(X, U) ℕ (B.toModule.val.obj (op U))
    (fun n ↦ ((i n).val.app (op U)).hom)

private noncomputable def positiveCopyMul {X : Scheme.{u}} (E : X.CommAlgebraSheaf)
    (m n : ℕ) (U : X.Opens) :
    (positiveCopyPiece E m).val.obj (op U) →ₗ[Γ(X, U)]
      (positiveCopyPiece E n).val.obj (op U) →ₗ[Γ(X, U)]
        (positiveCopyPiece E (m + n)).val.obj (op U) := by
  let : Algebra Γ(X, U) (E.right.obj.obj (op U)) := (E.hom.hom.app (op U)).hom.toAlgebra
  cases m with
  | zero =>
    cases n with
    | zero => exact LinearMap.mul Γ(X, U) Γ(X, U)
    | succ n =>
      exact (LinearMap.mul Γ(X, U) (E.right.obj.obj (op U))).comp
        (Algebra.linearMap Γ(X, U) (E.right.obj.obj (op U)))
  | succ m =>
    cases n with
    | zero =>
      exact ((LinearMap.mul Γ(X, U) (E.right.obj.obj (op U))).flip.comp
        (Algebra.linearMap Γ(X, U) (E.right.obj.obj (op U)))).flip
    | succ n => exact LinearMap.mul Γ(X, U) (E.right.obj.obj (op U))

private theorem positiveCopyMul_zero_zero {X : Scheme.{u}} (E : X.CommAlgebraSheaf)
    (U : X.Opens) (r s : Γ(X, U)) : positiveCopyMul E 0 0 U r s = r * s := rfl
private theorem positiveCopyMul_zero_succ {X : Scheme.{u}} (E : X.CommAlgebraSheaf)
    (U : X.Opens) (n : ℕ) (r : Γ(X, U)) (a : E.right.obj.obj (op U)) :
    positiveCopyMul E 0 (n+1) U r a = E.hom.hom.app (op U) r * a := rfl
private theorem positiveCopyMul_succ_zero {X : Scheme.{u}} (E : X.CommAlgebraSheaf)
    (U : X.Opens) (n : ℕ) (a : E.right.obj.obj (op U)) (r : Γ(X, U)) :
    positiveCopyMul E (n+1) 0 U a r = a * E.hom.hom.app (op U) r := rfl
private theorem positiveCopyMul_succ_succ {X : Scheme.{u}} (E : X.CommAlgebraSheaf)
    (U : X.Opens) (m n : ℕ) (a b : E.right.obj.obj (op U)) :
    positiveCopyMul E (m+1) (n+1) U a b = a * b := rfl

private noncomputable def positiveCopyGraded {X : Scheme.{u}} (E : X.CommAlgebraSheaf) :
    GradedSheafAlgebra (positiveCopyPiece E) where
  mul := positiveCopyMul E
  unit := 𝟙 _
  naturality := by
    intro m n U V h a b
    cases m with
    | zero =>
      cases n with
      | zero =>
        change Γ(X, U) at a b
        exact map_mul (X.presheaf.map (homOfLE h).op).hom a b
      | succ n =>
        change Γ(X, U) at a
        change E.right.obj.obj (op U) at b
        change E.right.obj.map (homOfLE h).op (E.hom.hom.app (op U) a * b) = _
        rw [map_mul]
        have he := NatTrans.naturality_apply E.hom.hom (homOfLE h).op a
        exact congrArg (fun r ↦ r * E.right.obj.map (homOfLE h).op b) he.symm
    | succ m =>
      cases n with
      | zero =>
        change E.right.obj.obj (op U) at a
        change Γ(X, U) at b
        change E.right.obj.map (homOfLE h).op (a * E.hom.hom.app (op U) b) = _
        rw [map_mul]
        have he := NatTrans.naturality_apply E.hom.hom (homOfLE h).op b
        exact congrArg (fun r ↦ E.right.obj.map (homOfLE h).op a * r) he.symm
      | succ n =>
        change E.right.obj.obj (op U) at a b
        exact map_mul (E.right.obj.map (homOfLE h).op).hom a b
  assoc := by
    intro l m n U a b c
    cases l <;> cases m <;> cases n
    case zero.zero.zero =>
      change Γ(X, U) at a b c
      apply heq_of_eq
      exact mul_assoc a b c
    case zero.zero.succ n =>
      change Γ(X, U) at a b
      change E.right.obj.obj (op U) at c
      apply heq_of_eq
      change E.hom.hom.app (op U) (a * b) * c =
        E.hom.hom.app (op U) a * (E.hom.hom.app (op U) b * c)
      rw [map_mul, mul_assoc]
    case zero.succ.zero m =>
      change Γ(X, U) at a c
      change E.right.obj.obj (op U) at b
      apply heq_of_eq
      change E.hom.hom.app (op U) a * b * E.hom.hom.app (op U) c =
        E.hom.hom.app (op U) a * (b * E.hom.hom.app (op U) c)
      exact mul_assoc _ _ _
    case zero.succ.succ m n =>
      change Γ(X, U) at a
      change E.right.obj.obj (op U) at b c
      apply heq_of_eq
      change (E.hom.hom.app (op U) a) * (b) * (c) = (E.hom.hom.app (op U) a) * ((b) * (c))
      exact mul_assoc _ _ _
    case succ.zero.zero l =>
      change Γ(X, U) at b c
      change E.right.obj.obj (op U) at a
      apply heq_of_eq
      change a * E.hom.hom.app (op U) b * E.hom.hom.app (op U) c =
        a * E.hom.hom.app (op U) (b * c)
      rw [map_mul, mul_assoc]
    case succ.zero.succ l n =>
      change Γ(X, U) at b
      change E.right.obj.obj (op U) at a c
      apply heq_of_eq
      change (a) * (E.hom.hom.app (op U) b) * (c) = (a) * ((E.hom.hom.app (op U) b) * (c))
      exact mul_assoc _ _ _
    case succ.succ.zero l m =>
      change Γ(X, U) at c
      change E.right.obj.obj (op U) at a b
      apply heq_of_eq
      change (a) * (b) * (E.hom.hom.app (op U) c) = (a) * ((b) * (E.hom.hom.app (op U) c))
      exact mul_assoc _ _ _
    case succ.succ.succ l m n =>
      change E.right.obj.obj (op U) at a b c
      apply heq_of_eq
      change (a) * (b) * (c) = (a) * ((b) * (c))
      exact mul_assoc _ _ _
  comm := by
    intro m n U a b
    cases m <;> cases n
    case zero.zero =>
      change Γ(X, U) at a b
      exact heq_of_eq (mul_comm a b)
    case zero.succ n =>
      change Γ(X, U) at a
      change E.right.obj.obj (op U) at b
      exact heq_of_eq (mul_comm (E.hom.hom.app (op U) a) b)
    case succ.zero m =>
      change E.right.obj.obj (op U) at a
      change Γ(X, U) at b
      exact heq_of_eq (mul_comm a (E.hom.hom.app (op U) b))
    case succ.succ m n =>
      change E.right.obj.obj (op U) at a b
      exact heq_of_eq (mul_comm a b)
  one_mul := by
    intro n U a
    cases n with
    | zero =>
      change Γ(X, U) at a
      exact heq_of_eq (one_mul a)
    | succ n =>
      change E.right.obj.obj (op U) at a
      apply heq_of_eq
      change E.hom.hom.app (op U) 1 * a = a
      rw [map_one, one_mul]
  mul_one := by
    intro n U a
    cases n with
    | zero =>
      change Γ(X, U) at a
      exact heq_of_eq (mul_one a)
    | succ n =>
      change E.right.obj.obj (op U) at a
      apply heq_of_eq
      change a * E.hom.hom.app (op U) 1 = a
      rw [map_one, mul_one]

private theorem isQuasicoherent_coproduct {X : Scheme.{u}} (P : ℕ → X.Modules)
    (B : X.Modules) (i : ∀ n, P n ⟶ B) (h : IsColimit (Cofan.mk B i))
    [∀ n, (P n).IsQuasicoherent] : B.IsQuasicoherent := by
  let Q : ULift.{u} ℕ → X.Modules := fun n ↦ P n.down
  have : ∀ n, (Q n).IsQuasicoherent := fun n ↦ inferInstance
  have hq := Scheme.Modules.isQuasicoherent_sigma Q
  let hc := (Cofan.isColimitEquivOfEquiv (Equiv.ulift : ULift.{u} ℕ ≃ ℕ)
    (Cofan.mk B i)) h
  let e := (coproductIsCoproduct Q).coconePointUniqueUpToIso hc
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq

private theorem bijective_coproductSectionSum {X : Scheme.{u}} (P : ℕ → X.Modules)
    (B : X.Modules) (i : ∀ n, P n ⟶ B) (h : IsColimit (Cofan.mk B i))
    [∀ n, (P n).IsQuasicoherent] [B.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (DirectSum.toModule Γ(X, U) ℕ (B.val.obj (op U))
      (fun n ↦ ((i n).val.app (op U)).hom)) := by
  let Q : ULift.{u} ℕ → X.Modules := fun n ↦ P n.down
  let hc := (Cofan.isColimitEquivOfEquiv (Equiv.ulift : ULift.{u} ℕ ≃ ℕ)
    (Cofan.mk B i)) h
  obtain ⟨he⟩ := Scheme.Modules.quasiCoherentModuleColimitEvaluation X
    (Discrete (ULift.{u} ℕ)) (Discrete.functor Q) _ hc
    (fun n ↦ (inferInstance : (P n.as.down).IsQuasicoherent))
    (inferInstance : B.IsQuasicoherent) U hU
  let Z : ℕ → ModuleCat Γ(X, U) := fun n ↦ (P n).val.obj (op U)
  let c : Cofan Z := Cofan.mk (B.val.obj (op U)) (fun n ↦ (i n).val.app (op U))
  have he' : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (Equiv.ulift : ULift.{u} ℕ ≃ ℕ) c).symm (by
      exact Cofan.isColimitMapCoconeEquiv
        (SheafOfModules.evaluation X.ringCatSheaf (op U)) Q _ he)
  let e := (ModuleCat.coproductCoconeIsColimit Z).coconePointUniqueUpToIso he'
  have heq : e.hom = ModuleCat.ofHom (DirectSum.toModule Γ(X, U) ℕ
      (B.val.obj (op U)) (fun n ↦ ((i n).val.app (op U)).hom)) := by
    apply (ModuleCat.coproductCoconeIsColimit Z).hom_ext
    intro j
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    ext x
    change (i j.as).val.app (op U) x =
      DirectSum.toModule Γ(X, U) ℕ (B.val.obj (op U))
        (fun n ↦ ((i n).val.app (op U)).hom) (DirectSum.lof Γ(X, U) ℕ
          (fun n ↦ (P n).val.obj (op U)) j.as x)
    exact (DirectSum.toModule_lof Γ(X, U)
      (M := fun n ↦ (P n).val.obj (op U)) (N := B.val.obj (op U))
      (φ := fun n ↦ ((i n).val.app (op U)).hom) j.as x).symm
  rw [← ModuleCat.hom_ofHom (DirectSum.toModule Γ(X, U) ℕ
      (B.val.obj (op U)) (fun n ↦ ((i n).val.app (op U)).hom)), ← heq]
  exact (ConcreteCategory.bijective_of_isIso e.hom)

private theorem exists_symmetricQuotient {X : Scheme.{u}} (E B : X.CommAlgebraSheaf)
    (i : ∀ n, positiveCopyPiece E n ⟶ B.toModule)
    (G : GradedSheafAlgebra (positiveCopyPiece E))
    (hmul : ∀ U m n a b,
      (i (m + n)).val.app (op U) (G.mul m n U a b) =
        (show B.right.obj.obj (op U) from (i m).val.app (op U) a) *
          (show B.right.obj.obj (op U) from (i n).val.app (op U) b))
    (hzero : ∀ U r, (i 0).val.app (op U) r = B.hom.hom.app (op U) r)
    (hpos : ∀ U m n (a b : E.right.obj.obj (op U)),
      HEq (G.mul (m + 1) (n + 1) U a b) (a * b)) :
    ∃! q : SymmetricAlgebraSheaf.algebra E.toModule ⟶ B,
      (∀ (U : X.Opens) (a : E.right.obj.obj (op U)),
        q.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion E.toModule).val.app
          (op U) a) = (i 1).val.app (op U) a) ∧
      (∀ (U : X.Opens) (n : ℕ)
        (s : SymmetricAlgebra Γ(X, U) (E.toModule.val.obj (op U))),
        s ∈ (SymmetricAlgebra.ι Γ(X, U) (E.toModule.val.obj (op U))).range ^ n →
        ∃ a : (positiveCopyPiece E n).val.obj (op U),
          q.right.hom.app (op U) (SymmetricAlgebraSheaf.sectionMap E.toModule
            (op U) s) = (i n).val.app (op U) a) ∧
      (∀ (U : X.Opens) (r : Γ(X, U)),
        q.right.hom.app (op U) ((SymmetricAlgebraSheaf.algebra E.toModule).hom.hom.app
          (op U) r) = (i 0).val.app (op U) r) ∧
      (∀ (U : X.Opens) (n : ℕ) (a : (positiveCopyPiece E n).val.obj (op U)),
        ∃ s : SymmetricAlgebra Γ(X, U) (E.toModule.val.obj (op U)),
          s ∈ (SymmetricAlgebra.ι Γ(X, U) (E.toModule.val.obj (op U))).range ^ n ∧
          q.right.hom.app (op U) (SymmetricAlgebraSheaf.sectionMap E.toModule
            (op U) s) = (i n).val.app (op U) a) := by
  obtain ⟨q, hq, huniq⟩ := exists_quasiCoherentSymmetricAlgebra_core X E.toModule B (i 1)
  have hscalar (U : X.Opens) (r : Γ(X, U)) :
      q.right.hom.app (op U) ((SymmetricAlgebraSheaf.algebra E.toModule).hom.hom.app
        (op U) r) = (i 0).val.app (op U) r := by
    rw [hzero]
    exact congrArg (fun f ↦ f.hom.app (op U) r) (Under.w q)
  refine ⟨q, ⟨hq, ?_, hscalar, ?_⟩, fun t ht ↦ huniq t ht.1⟩
  · intro U n s hs
    induction hs using Submodule.pow_induction_on_right' with
    | algebraMap r => exact ⟨r, hscalar U r⟩
    | add x y n hx hy hix hiy =>
      obtain ⟨a, ha⟩ := hix
      obtain ⟨b, hb⟩ := hiy
      exact ⟨a + b, by simp only [map_add, ha, hb]⟩
    | mul_mem n x hx hix m hm =>
      obtain ⟨a, ha⟩ := hix
      obtain ⟨b, rfl⟩ := hm
      refine ⟨G.mul n 1 U a b, ?_⟩
      rw [map_mul, map_mul, ha]
      change (show B.right.obj.obj (op U) from (i n).val.app (op U) a) *
        q.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion E.toModule).val.app
          (op U) b) = _
      rw [hq]
      exact (hmul U n 1 a b).symm
  · intro U n
    cases n with
    | zero =>
      intro a
      change Γ(X, U) at a
      exact ⟨algebraMap _ _ a, Submodule.algebraMap_mem a, hscalar U a⟩
    | succ n =>
      induction n with
      | zero =>
        intro a
        exact ⟨SymmetricAlgebra.ι _ _ a, by
          rw [pow_one]
          exact LinearMap.mem_range_self _ a, hq U a⟩
      | succ n ih =>
        intro a
        obtain ⟨s, hs, he⟩ := ih a
        refine ⟨s * SymmetricAlgebra.ι Γ(X, U) (E.toModule.val.obj (op U))
          (show E.toModule.val.obj (op U) from (1 : E.right.obj.obj (op U))), ?_, ?_⟩
        · rw [pow_succ]
          exact Submodule.mul_mem_mul hs (LinearMap.mem_range_self _ _)
        · rw [map_mul, map_mul, he]
          change (show B.right.obj.obj (op U) from (i (n + 1)).val.app (op U) a) *
            q.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion E.toModule).val.app
              (op U) (1 : E.right.obj.obj (op U))) = _
          rw [hq]
          refine (hmul U (n + 1) 1 a
            (1 : E.right.obj.obj (op U))).symm.trans ?_
          have hg := eq_of_heq (hpos U n 0 a (1 : E.right.obj.obj (op U)))
          simpa only [mul_one] using congrArg ((i (n + 1 + 1)).val.app (op U)) hg


/-- The positive-copy graded algebra is quasi-coherent and receives the unique graded
symmetric quotient, which is the identity in degree zero and surjective in every degree.
The membership clauses use the degree-n submodule spanned by products of n generators;
sheafifying these pieces gives the symmetric-degree subsheaves. Their images lie in the
specified target piece on every open. The reverse containment is witnessed on sections,
so it implies in particular surjectivity of each homogeneous sheaf map.
Source: Stacks Project, Morphisms, Tag 0B3I (lemma-finite-projective); Modules, Tag 01CF
(section-symmetric-exterior) (blueprint: lem-trf-positive-copy-graded-quotient).

Proof: (1) Define positive-positive products by multiplication in E, mixed products by
its structure map, and degree-zero products in O_X. Restriction compatibility and
bilinearity follow from those of E. Associativity is checked with zero, one, two, or
three degree-zero factors; commutativity and the unit laws follow in the same cases.
This uses def-weil-pbc-quasi-coherent-algebra and def-weil-pbc-graded-sheaf-structures.
(2) Restrict to an affine open and use
lem-weil-pbc-module-restriction-open-immersion-colimits,
lem-weil-pbc-affine-tilde-gamma-adjunction and lem-weil-pbc-spec-tilde-free-module.
The tilde of the module direct sum is the sheaf coproduct. Its affine sections are the
original direct sum, proving the canonical section-sum bijection and quasi-coherence
(pqf-def-coherent). No claim about sectionwise coproducts on general opens is needed.
(3) The comparison respects products on homogeneous elements, hence on finite sums;
naturality of the cocone arrows proves compatibility for every affine restriction.
(4) Apply lem-weil-pbc-quasi-coherent-symmetric-algebra to the degree-one inclusion.
The symmetric universal property gives the unique algebra-sheaf extension.
(5) By lem-weil-pbc-symmetric-algebra-graded, pure products span each symmetric degree.
Their images are products in the corresponding positive copy. This proves homogeneity
sectionwise, and hence for the sheafified homogeneous pieces by local representation.
(6) Algebra-linearity makes degree zero the identity. In degree n+1, lift a to
j(a) j(1_E)^n. This is homogeneous and maps to a in the degree-(n+1) copy. The formula
also covers n=0, the zero algebra, and a noninjective structure homomorphism. -/
theorem exists_positiveCopyGradedQuotient (X : Scheme.{u}) (E : X.CommAlgebraSheaf)
    [E.toModule.IsQuasicoherent] :
    ∃ (B : X.CommAlgebraSheaf)
      (i : ∀ n : ℕ, positiveCopyPiece E n ⟶ B.toModule)
      (G : GradedSheafAlgebra (positiveCopyPiece E)),
      Nonempty (IsColimit (Cofan.mk B.toModule i)) ∧
      B.toModule.IsQuasicoherent ∧
      G.unit = 𝟙 (SheafOfModules.unit X.ringCatSheaf) ∧
      (∀ (U : X.Opens) (r s : Γ(X, U)), HEq (G.mul 0 0 U r s) (r * s)) ∧
      (∀ (U : X.Opens) (n : ℕ) (r : Γ(X, U))
        (a : E.right.obj.obj (op U)),
        HEq (G.mul 0 (n + 1) U r a) (E.hom.hom.app (op U) r * a)) ∧
      (∀ (U : X.Opens) (n : ℕ) (a : E.right.obj.obj (op U)) (r : Γ(X, U)),
        HEq (G.mul (n + 1) 0 U a r) (a * E.hom.hom.app (op U) r)) ∧
      (∀ (U : X.Opens) (m n : ℕ) (a b : E.right.obj.obj (op U)),
        HEq (G.mul (m + 1) (n + 1) U a b) (a * b)) ∧
      (∀ (U : X.Opens) (m n : ℕ)
        (a : (positiveCopyPiece E m).val.obj (op U))
        (b : (positiveCopyPiece E n).val.obj (op U)),
        (i (m + n)).val.app (op U) (G.mul m n U a b) =
          (@id (B.right.obj.obj (op U)) ((i m).val.app (op U) a)) *
            (@id (B.right.obj.obj (op U)) ((i n).val.app (op U) b))) ∧
      (∀ (U : X.Opens) (r : Γ(X, U)),
        (i 0).val.app (op U) r = B.hom.hom.app (op U) r) ∧
      (∀ U : X.affineOpens, Function.Bijective (positiveCopySectionSum E B i U.1)) ∧
      ∃! q : SymmetricAlgebraSheaf.algebra E.toModule ⟶ B,
        (∀ (U : X.Opens) (a : E.right.obj.obj (op U)),
          q.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion E.toModule).val.app
            (op U) a) = (i 1).val.app (op U) a) ∧
        (∀ (U : X.Opens) (n : ℕ)
          (s : SymmetricAlgebra Γ(X, U) (E.toModule.val.obj (op U))),
          s ∈ (SymmetricAlgebra.ι Γ(X, U) (E.toModule.val.obj (op U))).range ^ n →
          ∃ a : (positiveCopyPiece E n).val.obj (op U),
            q.right.hom.app (op U) (SymmetricAlgebraSheaf.sectionMap E.toModule
              (op U) s) = (i n).val.app (op U) a) ∧
        (∀ (U : X.Opens) (r : Γ(X, U)),
          q.right.hom.app (op U) ((SymmetricAlgebraSheaf.algebra E.toModule).hom.hom.app
            (op U) r) = (i 0).val.app (op U) r) ∧
        (∀ (U : X.Opens) (n : ℕ) (a : (positiveCopyPiece E n).val.obj (op U)),
          ∃ s : SymmetricAlgebra Γ(X, U) (E.toModule.val.obj (op U)),
            s ∈ (SymmetricAlgebra.ι Γ(X, U) (E.toModule.val.obj (op U))).range ^ n ∧
            q.right.hom.app (op U) (SymmetricAlgebraSheaf.sectionMap E.toModule
              (op U) s) = (i n).val.app (op U) a) := by
  have hpieces : ∀ n, (positiveCopyPiece E n).IsQuasicoherent := by
    intro n
    cases n with
    | zero =>
      exact SheafOfModules.isQuasicoherent_unit.{u, u, u} (R := X.ringCatSheaf)
    | succ n => exact (inferInstance : E.toModule.IsQuasicoherent)
  obtain ⟨B, i, hcol, hmul, hunit⟩ :=
    GradedSheafAlgebra.exists_total (positiveCopyPiece E) (positiveCopyGraded E)
  have hB : B.toModule.IsQuasicoherent :=
    isQuasicoherent_coproduct (positiveCopyPiece E) B.toModule i hcol.some
  refine ⟨B, i, positiveCopyGraded E, hcol, hB, rfl, ?_, ?_, ?_, ?_, hmul, hunit, ?_, ?_⟩
  · intro U r s
    exact heq_of_eq (positiveCopyMul_zero_zero E U r s)
  · intro U n r a
    exact heq_of_eq (positiveCopyMul_zero_succ E U n r a)
  · intro U n a r
    exact heq_of_eq (positiveCopyMul_succ_zero E U n a r)
  · intro U m n a b
    exact heq_of_eq (positiveCopyMul_succ_succ E U m n a b)
  · intro U
    exact bijective_coproductSectionSum (positiveCopyPiece E) B.toModule i hcol.some U.1 U.2
  · exact exists_symmetricQuotient E B i (positiveCopyGraded E) hmul hunit
      (fun U m n a b ↦ heq_of_eq (positiveCopyMul_succ_succ E U m n a b))

end AlgebraicGeometry
