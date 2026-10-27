/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Linearized PGL actions and their invariant section algebras

Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 1, §1 and
Theorem 1.10; Morrison, arXiv:0810.2340, §2 and §3.3
(blueprint: def-sfb-pgl-linearized-polarization).

A PGL action is encoded by a natural GL action on scheme-valued points on which
scalar matrices act trivially. The same condition is imposed on the line module.
Since GL → PGL is an fppf quotient, this is precisely descent of a PGL action,
including its values over schemes whose PGL points do not lift globally to GL.
All tests include nonreduced schemes. Invariance of a section is tested after
arbitrary such pullbacks, not just on geometric fibres.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry
namespace PGLLinearization

variable (k : Type u) [Field k]

/-- Scheme-valued points of GL, including nonaffine test schemes. Source: MFK,
Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
abbrev Matrices (r : ℕ) (T : Over (Spec (.of k))) :=
  Matrix.GeneralLinearGroup (Fin r) Γ(T.left, ⊤)

/-- The affine test scheme of a field extension. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def fieldTest (Ω : Type u) [Field Ω] [Algebra k Ω] :
    Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- A linearized PGL action, written on GL-valued test points with trivial scalar
kernel. Naturality makes the action algebraic; the line isomorphisms are O-linear,
and satisfy the unit, multiplication and pullback cocycles. Source: MFK, Chapter 1,
§1 (blueprint: def-sfb-pgl-linearized-polarization). -/
structure Action (r : ℕ) (Z : Over (Spec (.of k))) (L : Z.left.Modules) where
  act : ∀ (T : Over (Spec (.of k))), Matrices k r T → (T ⟶ Z) → (T ⟶ Z)
  one_act : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Z), act T 1 x = x
  mul_act : ∀ (T : Over (Spec (.of k))) (g h : Matrices k r T) (x : T ⟶ Z),
    act T (g * h) x = act T g (act T h x)
  scalar_act : ∀ (T : Over (Spec (.of k))) (a : Γ(T.left, ⊤)ˣ) (x : T ⟶ Z),
    act T (Matrix.GeneralLinearGroup.scalar (Fin r) a) x = x
  naturality : ∀ (T U : Over (Spec (.of k))) (f : U ⟶ T)
    (g : Matrices k r T) (x : T ⟶ Z),
    act U (Matrix.GeneralLinearGroup.map f.left.appTop.hom g) (f ≫ x) = f ≫ act T g x
  lift : ∀ (T : Over (Spec (.of k))) (g : Matrices k r T) (x : T ⟶ Z),
    (Scheme.Modules.pullback x.left).obj L ≅
      (Scheme.Modules.pullback (act T g x).left).obj L
  one_lift : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Z),
    HEq (lift T 1 x) (Iso.refl ((Scheme.Modules.pullback x.left).obj L))
  mul_lift : ∀ (T : Over (Spec (.of k))) (g h : Matrices k r T) (x : T ⟶ Z),
    HEq (lift T (g * h) x) (lift T h x ≪≫ lift T g (act T h x))
  scalar_lift : ∀ (T : Over (Spec (.of k))) (a : Γ(T.left, ⊤)ˣ) (x : T ⟶ Z),
    HEq (lift T (Matrix.GeneralLinearGroup.scalar (Fin r) a) x)
      (Iso.refl ((Scheme.Modules.pullback x.left).obj L))
  lift_naturality : ∀ (T U : Over (Spec (.of k))) (f : U ⟶ T)
    (g : Matrices k r T) (x : T ⟶ Z),
    HEq (lift U (Matrix.GeneralLinearGroup.map f.left.appTop.hom g) (f ≫ x))
      ((Scheme.Modules.pullbackComp f.left x.left).symm.app L ≪≫
        (Scheme.Modules.pullback f.left).mapIso (lift T g x) ≪≫
        (Scheme.Modules.pullbackComp f.left (act T g x).left).app L)

variable {k}

/-- The canonical tensor power of a module isomorphism, with no choice of
trivialization. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def powerIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    ∀ n : ℕ, M.tensorPow n ≅ N.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => e ⊗ᵢ powerIso e n

/-- The canonical monoidal pullback comparison for tensor powers. Source: MFK,
Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def pullbackPowerIso {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.pullback f).obj (L.tensorPow n) ≅
      ((Scheme.Modules.pullback f).obj L).tensorPow n
  | 0 => Scheme.Modules.pullbackObjUnitIso f
  | n + 1 => (Functor.Monoidal.μIso (Scheme.Modules.pullback f) L (L.tensorPow n)).symm ≪≫
      (Iso.refl _ ⊗ᵢ pullbackPowerIso f L n)

variable {r : ℕ} {Z : Over (Spec (.of k))} {L : Z.left.Modules}

/-- The induced linearization on the nth power, using the canonical monoidal
comparisons. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def Action.powerLift (D : Action k r Z L)
    (T : Over (Spec (.of k))) (g : Matrices k r T) (x : T ⟶ Z) (n : ℕ) :
    (Scheme.Modules.pullback x.left).obj (L.tensorPow n) ≅
      (Scheme.Modules.pullback (D.act T g x).left).obj (L.tensorPow n) :=
  pullbackPowerIso x.left L n ≪≫ powerIso (D.lift T g x) n ≪≫
    (pullbackPowerIso (D.act T g x).left L n).symm

/-- Invariance as equality of sections after every scheme-valued test point.
This detects nilpotents. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
def Action.IsInvariant (D : Action k r Z L) (n : ℕ)
    (s : Scheme.Modules.SectionRingComponent L n) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : Matrices k r T) (x : T ⟶ Z),
    (D.powerLift T g x n).hom.app ⊤ (AlgebraicGeometry.pullbackΓ x.left (L.tensorPow n) s) =
      AlgebraicGeometry.pullbackΓ (D.act T g x).left (L.tensorPow n) s

/-- Geometric semistability: a positive-degree invariant section does not vanish
at the point. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
def Action.IsSemistable (D : Action k r Z L) (Ω : Type u) [Field Ω] [Algebra k Ω]
    (x : fieldTest k Ω ⟶ Z) : Prop :=
  ∃ (n : ℕ) (_ : 0 < n) (s : Scheme.Modules.SectionRingComponent L n),
    D.IsInvariant n s ∧ AlgebraicGeometry.pullbackΓ x.left (L.tensorPow n) s ≠ 0

/-- Matrices over Ω regarded as GL-valued points over Spec Ω. Source: MFK,
Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def fieldMatrix (Ω : Type u) [Field Ω] [Algebra k Ω]
    (g : Matrix.GeneralLinearGroup (Fin r) Ω) : Matrices k r (fieldTest k Ω) :=
  Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (.of Ω)).inv.hom g

/-- The point of the Ω-base change underlying an Ω-valued point. Source: MFK,
Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def geometricImage (Ω : Type u) [Field Ω] [Algebra k Ω]
    (x : fieldTest k Ω ⟶ Z) :
    pullback (C := Scheme.{u}) Z.hom (fieldTest k Ω).hom :=
  (pullback.lift x.left (𝟙 _) (by simp)).base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)

/-- Stability on geometric points. A closed set in the base change cuts out the
orbit among semistable geometric points. The finite set of PGL classes in the
stabilizer expresses dimension zero, including nonreduced finite stabilizers.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
def Action.IsStable (D : Action k r Z L) (Ω : Type u) [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω]
    (x : fieldTest k Ω ⟶ Z) : Prop :=
  D.IsSemistable Ω x ∧
    (∃ C : Set (pullback (C := Scheme.{u}) Z.hom (fieldTest k Ω).hom), IsClosed C ∧
      ∀ y : fieldTest k Ω ⟶ Z, D.IsSemistable Ω y →
        ((∃ g : Matrix.GeneralLinearGroup (Fin r) Ω,
          D.act _ (fieldMatrix Ω g) x = y) ↔ geometricImage Ω y ∈ C)) ∧
    Set.Finite (Matrix.ProjGenLinGroup.mk ''
      {g : Matrix.GeneralLinearGroup (Fin r) Ω | D.act _ (fieldMatrix Ω g) x = x})

/-- The invariant subring, generated by its homogeneous invariant sections.
Since the action preserves degrees, this is exactly the fixed section subring.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def Action.invariantRing [L.IsInvertible] (D : Action k r Z L) :
    Subring (Scheme.Modules.InvertibleSectionRing L) :=
  Subring.closure {a | ∃ (n : ℕ) (s : Scheme.Modules.SectionRingComponent L n),
    D.IsInvariant n s ∧ DirectSum.of (Scheme.Modules.SectionRingComponent L) n s = a}

/-- The actual degree-n subgroup of the invariant section algebra, inherited
from the existing section-ring grading. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def Action.invariantGrade [L.IsInvertible] (D : Action k r Z L) (n : ℕ) :
    AddSubgroup D.invariantRing :=
  (Scheme.Modules.sectionRingGrade L n).comap D.invariantRing.subtype.toAddMonoidHom

set_option linter.unusedVariables false in
/-- The inherited grading is uniquely determined. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization).
Proof: tensor multiplication and addition preserve invariance by naturality and
linearity of the linearization. Thus the ring generated by homogeneous invariant
sections is their direct sum. The section-ring decomposition restricts to this
subring, giving the grading. Uniqueness follows by comparing each homogeneous
component in the ambient section ring; all remaining grading fields are proofs. -/
theorem Action.invariantGrading_existsUnique [L.IsInvertible] (D : Action k r Z L) :
    ∃! h : GradedRing D.invariantGrade, True := by
  classical
  let hmul : SetLike.GradedMonoid D.invariantGrade :=
    { one_mem := SetLike.one_mem_graded (Scheme.Modules.sectionRingGrade L)
      mul_mem := by
        intro i j a b ha hb
        exact SetLike.mul_mem_graded (A := Scheme.Modules.sectionRingGrade L) ha hb }
  let f : ∀ n, D.invariantGrade n →+ Scheme.Modules.sectionRingGrade L n := fun n ↦
    { toFun := fun a ↦ ⟨a.1.1, a.2⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hf : Function.Injective (DirectSum.map f) := by
    apply (DirectSum.map_injective _).2
    intro n a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : Scheme.Modules.sectionRingGrade L n ↦ q.1) h
  have hcomp :
      (DirectSum.coeAddMonoidHom (Scheme.Modules.sectionRingGrade L)).comp
          (DirectSum.map f) =
        D.invariantRing.subtype.toAddMonoidHom.comp
          (DirectSum.coeAddMonoidHom D.invariantGrade) := by
    ext n a
    simp [f, DirectSum.coeAddMonoidHom]
  have hinj : Function.Injective (DirectSum.coeAddMonoidHom D.invariantGrade) := by
    intro a b h
    apply hf
    apply (Scheme.Modules.sectionRing_isInternal L).1
    have hc := congrArg (fun q ↦ q a) hcomp
    have hd := congrArg (fun q ↦ q b) hcomp
    exact hc.trans ((congrArg Subtype.val h).trans hd.symm)
  let F := D.invariantRing.subtype.comp (DirectSum.coeRingHom D.invariantGrade)
  have hgen : D.invariantRing ≤ F.range := by
    apply Subring.closure_le.mpr
    rintro a ⟨n, s, hs, rfl⟩
    let a : D.invariantRing :=
      ⟨DirectSum.of (Scheme.Modules.SectionRingComponent L) n s,
        Subring.subset_closure ⟨n, s, hs, rfl⟩⟩
    have ha : a ∈ D.invariantGrade n := ⟨s, rfl⟩
    refine ⟨DirectSum.of (fun n ↦ D.invariantGrade n) n ⟨a, ha⟩, ?_⟩
    simp [F, a]
  have hsurj : Function.Surjective (DirectSum.coeAddMonoidHom D.invariantGrade) := by
    intro a
    obtain ⟨b, hb⟩ := hgen a.2
    exact ⟨b, Subtype.ext hb⟩
  let h : GradedRing D.invariantGrade :=
    { hmul, (show DirectSum.IsInternal D.invariantGrade from ⟨hinj, hsurj⟩).chooseDecomposition
      with }
  refine ⟨h, trivial, ?_⟩
  intro h' _
  cases h
  cases h'
  congr 1
  exact Subsingleton.elim _ _

/-- The unique grading on the invariant subring. Only the uniquely determined
grading laws and decomposition have been postponed. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable instance Action.invariantGrading [L.IsInvertible] (D : Action k r Z L) :
    GradedRing D.invariantGrade :=
  Classical.choose D.invariantGrading_existsUnique

/-- Constants embedded in degree zero using the existing tensor-unit section
identification and structure map. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def constantSection (c : k) : Scheme.Modules.InvertibleSectionRing L :=
  DirectSum.of (Scheme.Modules.SectionRingComponent L) 0
    (Scheme.Modules.unitSectionsEquiv ⊤ (Z.hom.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)))

/-- Finite generation over k, expressed inside the ambient section ring. The
constant map is fixed, so no arbitrary coefficient-algebra structure is assumed.
Source: MFK, Chapter 1, Theorem 1.10
(blueprint: def-sfb-pgl-linearized-polarization). -/
def Action.IsFinitelyGenerated [L.IsInvertible] (D : Action k r Z L) : Prop :=
  ∃ s : Finset (Scheme.Modules.InvertibleSectionRing L),
    (↑s : Set (Scheme.Modules.InvertibleSectionRing L)) ⊆
      (D.invariantRing : Set (Scheme.Modules.InvertibleSectionRing L)) ∧
      Subring.closure (Set.range (constantSection (Z := Z) (L := L)) ∪ ↑s) = D.invariantRing

/-- A Veronese is generated in degree one over degree zero. Source: MFK,
Chapter 1, Theorem 1.10 (blueprint: def-sfb-pgl-linearized-polarization). -/
def Action.VeroneseGenerated [L.IsInvertible] (D : Action k r Z L) (d : ℕ) : Prop :=
  ∀ (n : ℕ) (a : D.invariantRing), a ∈ D.invariantGrade (n * d) →
    a ∈ Subring.closure ((D.invariantGrade 0 : Set D.invariantRing) ∪
      (D.invariantGrade d : Set D.invariantRing))

/-- The degree-zero coefficient ring, with a named carrier to keep typeclass
search from unfolding the scheme-theoretic closure. Source: MFK, Chapter 1, §1
(blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def Action.CoefficientRing [L.IsInvertible] (D : Action k r Z L) : Type u :=
  D.invariantGrade 0

/-- The inherited commutative ring on the degree-zero component. Source: MFK,
Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable instance Action.coefficientCommRing [L.IsInvertible] (D : Action k r Z L) :
    CommRing D.CoefficientRing :=
  inferInstanceAs (CommRing ↥(D.invariantGrade 0))

/-- The inclusion of degree zero in the ambient section ring. Source: MFK,
Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def Action.coefficientVal [L.IsInvertible] (D : Action k r Z L)
    (a : D.CoefficientRing) : Scheme.Modules.InvertibleSectionRing L :=
  a.1.1

/-- Proj of the invariant ring over k, with its coefficient map supplied in
degree zero. Source: MFK, Chapter 1, Theorem 1.10
(blueprint: def-sfb-pgl-linearized-polarization). -/
noncomputable def Action.projOver [L.IsInvertible] (D : Action k r Z L)
    (φ : k →+* D.CoefficientRing) : Over (Spec (.of k)) :=
  Over.mk (Proj.toSpecZero D.invariantGrade ≫ Spec.map (CommRingCat.ofHom φ))

/-- Compatibility of a linearized action on a closed subscheme with the given
one, including the line isomorphisms and not merely the action on points.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
def Action.IsRestriction (D : Action k r Z L) {X : Over (Spec (.of k))} (i : X ⟶ Z)
    (E : Action k r X ((Scheme.Modules.pullback i.left).obj L)) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : Matrices k r T) (x : T ⟶ X),
    E.act T g x ≫ i = D.act T g (x ≫ i) ∧
      HEq ((Scheme.Modules.pullbackComp x.left i.left).symm.app L ≪≫
        E.lift T g x ≪≫ (Scheme.Modules.pullbackComp (E.act T g x).left i.left).app L)
        (D.lift T g (x ≫ i))

/-- Scheme-theoretic invariance of a subscheme, tested by all schemes. Source:
MFK, Chapter 1, §1 (blueprint: def-sfb-pgl-linearized-polarization). -/
def Action.IsInvariantSubscheme (D : Action k r Z L) {J : Over (Spec (.of k))}
    (j : J ⟶ Z) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : Matrices k r T) (x : T ⟶ J),
    ∃ y : T ⟶ J, y ≫ j = D.act T g (x ≫ j)

/-- Invariance of a morphism to an algebraic space. Source: MFK, Chapter 1,
Theorem 1.10 (blueprint: def-sfb-pgl-linearized-polarization). -/
def Action.IsInvariantMap (D : Action k r Z L) {J : Over (Spec (.of k))} (j : J ⟶ Z)
    (B : AlgebraicSpace (Spec (.of k))) (f : yoneda.obj J ⟶ B.obj.obj) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : Matrices k r T) (x y : T ⟶ J),
    y ≫ j = D.act T g (x ≫ j) → f.app (op T) y = f.app (op T) x

end PGLLinearization
end AlgebraicGeometry
