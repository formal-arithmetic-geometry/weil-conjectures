/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.CategoryTheory.CondensedBarHomCoordinates
import Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Exact injective rows of the internal condensed bar

Source: main-20261015, six-functors direct-image stability, paragraph (3),
agent expansion of the internal condensed bar input
(blueprint: lem-sfb-condensed-injective-bar-rows).

The existing inhomogeneous bar sheaves represent the homogeneous equivariant Hom
presheaves by the normalized coordinate formula below. Thus the Hom presheaves are
sheaves, and their exactness is asserted both internally and on every profinite section.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction Profinite.CondensedAction.InternalBar

namespace CategoryTheory.CondensedBar

variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The generator [s] of A[S] over a profinite test object T, from the recorded free
adjunction. Source: internal bar, proof step 2
(blueprint: lem-sfb-condensed-injective-bar-rows). -/
def parameterGenerator (A : Ring.{u}) (S T : Profinite.{u}) (s : T ⟶ S) :
    sections A (freeParameter A S) T :=
  (((freeAdjunction A.toMon).unit.app
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj S)).hom.app
      (op T)) (ULift.up s)

/-- The section restriction in the homogeneous Hom presheaf is precomposition in
its free parameter. The tensor order P tensor A[S] uses the canonical symmetry of
A[S] tensor P. Source: internal bar, proof steps 2-3
(blueprint: lem-sfb-condensed-injective-bar-rows). -/
def parameterPullback (E : Resolution A.toMon G) (n : ℕ)
    {S T : Profinite.{u}} (k : T ⟶ S) (I : Equivariant A G)
    (f : E.tensorObjects (freeParameter A S) n ⟶ I) :
    (E.tensorObjects (freeParameter A T) n).module ⟶ I.module :=
  (E.tensorIso (freeParameter A T) n).hom ≫
    (E.objects n).module ◁ (free A.toMon).map
      (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).map k) ≫
    (E.tensorIso (freeParameter A S) n).inv ≫ f.val

/-- The complete row assertion on the recorded diagrams. The Hom identification is
additive, respects all restrictions and equivariant postcompositions, and is fixed by
its values on the actual free generators. Faces and degeneracies are those of B,
whose defining fields give all three inhomogeneous cofaces and insertion of 1.
Source: all clauses of the injective-row statement, internal bar expansion
(blueprint: lem-sfb-condensed-injective-bar-rows). -/
structure InjectiveRows (F : InternalFunctions A) (B : BarDiagram (G := G) F)
    (V : Invariants A G) (a : Augmentation V B) (E : Resolution A.toMon G) where
  /-- These sheaf sections are exactly the parametrized equivariant Hom groups. -/
  homEquiv : ∀ (I : Equivariant A G) [Injective I] (n : ℕ) (S : Profinite.{u}),
    sections A ((cochains B).obj I |>.X n) S ≃+
      (E.tensorObjects (freeParameter A S) n ⟶ I)
  /-- The displayed homogeneous-to-inhomogeneous formula, at every generalized point. -/
  coordinates : ∀ (I : Equivariant A G) [Injective I] (n : ℕ) (S T : Profinite.{u})
      (x : sections A (((cochains B).obj I).X n) S) (s : T ⟶ S)
      (g : Fin (n + 1) → C(T, G)),
    onSections A.toMon ((homEquiv I n S x).val) T
      (onSections A.toMon (E.tensorIso (freeParameter A S) n).inv T
        (pureTensor A.toMon _ _ T
          (basis A.toMon G (n + 1) (E.objects n) (E.freeIso n) T g)
          (parameterGenerator A S T s))) =
      I.act T (g 0)
        ((F.evaluate (power G n) S I.module
          (onSections A.toMon (B.term I n).hom S x)).val T s
            (tupleMap (fun j ↦ (g j.castSucc)⁻¹ * g j.succ)))
  /-- Every profinite base change commutes with the Hom identification. -/
  restriction : ∀ (I : Equivariant A G) [Injective I] (n : ℕ)
      (S T : Profinite.{u}) (k : T ⟶ S)
      (x : sections A (((cochains B).obj I).X n) S),
    (homEquiv I n T ((((cochains B).obj I).X n).X.obj.map k.op x)).val =
      parameterPullback E n k I (homEquiv I n S x)
  /-- Every equivariant map of injectives commutes with the Hom identification. -/
  naturality : ∀ (I J : Equivariant A G) [Injective I] [Injective J]
      (h : I ⟶ J) (n : ℕ) (S : Profinite.{u})
      (x : sections A (((cochains B).obj I).X n) S),
    homEquiv J n S (onSections A.toMon (((cochains B).map h).f n) S x) =
      homEquiv I n S x ≫ h
  /-- The cochain differential is precisely precomposition by the homogeneous boundary. -/
  differential : ∀ (I : Equivariant A G) [Injective I] (n : ℕ) (S : Profinite.{u})
      (x : sections A (((cochains B).obj I).X n) S),
    homEquiv I (n + 1) S
      (onSections A.toMon (((cochains B).obj I).d n (n + 1)) S x) =
        E.tensorBoundary (freeParameter A S) n ≫ homEquiv I n S x
  /-- The augmentation is the invariant inclusion, constant on homogeneous generators. -/
  augmentation : ∀ (I : Equivariant A G) [Injective I] (S T : Profinite.{u})
      (x : sections A (V.functor.obj I) S) (s : T ⟶ S) (g : Fin 1 → C(T, G)),
    onSections A.toMon
      (homEquiv I 0 S (onSections A.toMon ((a.map.app I).f 0) S x)).val T
      (onSections A.toMon (E.tensorIso (freeParameter A S) 0).inv T
        (pureTensor A.toMon _ _ T
          (basis A.toMon G 1 (E.objects 0) (E.freeIso 0) T g)
          (parameterGenerator A S T s))) =
      I.module.X.obj.map s.op (onSections A.toMon (V.inclusion.app I) S x)
  /-- The degree-zero differential evaluates to g*m-m on every generalized section. -/
  degreeZero : ∀ (I : Equivariant A G) [Injective I] (S T : Profinite.{u})
      (x : sections A (((cochains B).obj I).X 0) S) (s : T ⟶ S) (g : C(T, G)),
    (F.evaluate (power G 1) S I.module
      (onSections A.toMon
        ((((cochains B).obj I).d 0 1) ≫ (B.term I 1).hom) S x)).val T s
          (tupleMap (fun _ ↦ g)) =
      @id (sections A I.module T) (I.act T g ((F.evaluate (power G 0) S I.module
        (onSections A.toMon (B.term I 0).hom S x)).val T s
          (tupleMap (fun i ↦ Fin.elim0 i)))) -
      (F.evaluate (power G 0) S I.module
        (onSections A.toMon (B.term I 0).hom S x)).val T s
          (tupleMap (fun i ↦ Fin.elim0 i))
  /-- Internal exactness at the augmented term. -/
  mono : ∀ (I : Equivariant A G) [Injective I], Mono ((a.map.app I).f 0)
  /-- Exactness at the augmented term on every S, hence an invariant inclusion. -/
  mono_sections : ∀ (I : Equivariant A G) [Injective I] (S : Profinite.{u}),
    Function.Injective (onSections A.toMon ((a.map.app I).f 0) S)
  /-- Exactness on every S at bar degree zero. -/
  exact_sections_zero : ∀ (I : Equivariant A G) [Injective I] (S : Profinite.{u}),
    Function.Exact (onSections A.toMon ((a.map.app I).f 0) S)
      (onSections A.toMon (((cochains B).obj I).d 0 1) S)
  /-- Exactness on every S at every strictly positive bar degree. -/
  exact_sections_succ : ∀ (I : Equivariant A G) [Injective I]
      (n : ℕ) (S : Profinite.{u}),
    Function.Exact (onSections A.toMon (((cochains B).obj I).d n (n + 1)) S)
      (onSections A.toMon (((cochains B).obj I).d (n + 1) (n + 2)) S)
  /-- Internal exactness at degree zero, including the given invariant augmentation. -/
  exact_zero : ∀ (I : Equivariant A G) [Injective I],
    ∃ w : (a.map.app I).f 0 ≫ ((cochains B).obj I).d 0 1 = 0,
      (ShortComplex.mk ((a.map.app I).f 0) (((cochains B).obj I).d 0 1) w).Exact
  /-- Internal exactness at every strictly positive degree. -/
  exact_succ : ∀ (I : Equivariant A G) [Injective I] (n : ℕ),
    ((cochains B).obj I).ExactAt (n + 1)

private def functionValue (F : InternalFunctions A) (P S : Profinite.{u})
    (M : Modules A) (T : Profinite.{u}) (s : T ⟶ S) (g : C(T, P)) :
    sections A ((F.functor P).obj M) S →+ sections A M T where
  toFun x := (F.evaluate P S M x).val T s g
  map_zero' := by
    have h := F.add P S M 0 0 T s g
    exact (add_left_cancel (by simpa only [zero_add, add_zero] using h.symm :
      (F.evaluate P S M 0).val T s g + (F.evaluate P S M 0).val T s g =
        (F.evaluate P S M 0).val T s g + 0))
  map_add' x y := F.add P S M x y T s g

private theorem bar_degreeZero (F : InternalFunctions A) (B : BarDiagram (G := G) F)
    (I : Equivariant A G) (S T : Profinite.{u})
    (x : sections A (((cochains B).obj I).X 0) S) (s : T ⟶ S) (g : C(T, G)) :
    (F.evaluate (power G 1) S I.module
      (onSections A.toMon
        ((((cochains B).obj I).d 0 1) ≫ (B.term I 1).hom) S x)).val T s
          (tupleMap (fun _ ↦ g)) =
      @id (sections A I.module T)
        (I.act T g ((F.evaluate (power G 0) S I.module
          (onSections A.toMon (B.term I 0).hom S x)).val T s
            (tupleMap (fun i ↦ Fin.elim0 i)))) -
      (F.evaluate (power G 0) S I.module
        (onSections A.toMon (B.term I 0).hom S x)).val T s
          (tupleMap (fun i ↦ Fin.elim0 i)) := by
  have hd : ((cochains B).obj I).d 0 1 =
      (B.diagram.obj I).δ 0 - (B.diagram.obj I).δ 1 := by
    have h := CochainComplex.of_d
      (fun n : ℕ ↦ (B.diagram.obj I).obj (SimplexCategory.mk n))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD (B.diagram.obj I)) 0
    exact h.trans (by
      simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two,
        sub_eq_add_neg])
  let y := onSections A.toMon (B.term I 0).hom S x
  have h0 := B.face I 0 0 S y T s (fun _ ↦ g)
  have h1 := B.face I 0 1 S y T s (fun _ ↦ g)
  have hempty (f : Fin 0 → C(T, G)) : f = (fun i ↦ Fin.elim0 i) :=
    funext (fun i ↦ Fin.elim0 i)
  simp only [Fin.val_zero] at h0
  simp only [Fin.val_one, Nat.zero_add] at h1
  simp only [hempty] at h0 h1
  change functionValue F (power G 1) S I.module T s (tupleMap (fun _ ↦ g)) _ = _
  rw [hd, Preadditive.sub_comp]
  change functionValue F (power G 1) S I.module T s (tupleMap (fun _ ↦ g))
    (onSections A.toMon ((B.diagram.obj I).δ 0 ≫ (B.term I 1).hom) S x -
      onSections A.toMon ((B.diagram.obj I).δ 1 ≫ (B.term I 1).hom) S x) = _
  rw [map_sub]
  have hy : onSections A.toMon (B.term I 0).inv S y = x := by
    change onSections A.toMon ((B.term I 0).hom ≫ (B.term I 0).inv) S x = x
    rw [Iso.hom_inv_id]
    rfl
  change (F.evaluate (power G 1) S I.module
    (onSections A.toMon ((B.diagram.obj I).δ 0 ≫ (B.term I 1).hom) S
      (onSections A.toMon (B.term I 0).inv S y))).val T s
        (tupleMap (fun _ ↦ g)) = _ at h0
  change (F.evaluate (power G 1) S I.module
    (onSections A.toMon ((B.diagram.obj I).δ 1 ≫ (B.term I 1).hom) S
      (onSections A.toMon (B.term I 0).inv S y))).val T s
        (tupleMap (fun _ ↦ g)) = _ at h1
  rw [hy] at h0 h1
  simpa [functionValue, y] using
    congrArg₂ (· - ·) h0 h1

private theorem mono_of_sections {M N : Modules A} (f : M ⟶ N)
    (hf : ∀ S : Profinite.{u}, Function.Injective (onSections A.toMon f S)) : Mono f := by
  constructor
  intro Z g h he
  ext S x
  apply hf S.unop
  exact ConcreteCategory.congr_hom (congr_app (congrArg (fun t ↦ t.hom.hom) he) S) x

private theorem exact_of_sections (S : ShortComplex (Modules A))
    (hS : ∀ T : Profinite.{u}, Function.Exact (onSections A.toMon S.f T)
      (onSections A.toMon S.g T)) : S.Exact := by
  let U := Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) A.X
  let J := coherentTopology Profinite.{u}
  let i := sheafToPresheaf J AddCommGrpCat.{u + 1}
  have hEval : JointlyReflectIsomorphisms
      (fun T : Profiniteᵒᵖ ↦ (evaluation Profiniteᵒᵖ AddCommGrpCat.{u + 1}).obj T) := by
    constructor
    intro P Q f hf
    let : ∀ T, IsIso (f.app T) := hf
    exact NatIso.isIso_of_isIso_app f
  have hP : ((S.map U).map i).Exact := (hEval.exact_iff _).2 (fun T ↦
    (ShortComplex.ab_exact_iff_function_exact _).2 (hS T.unop))
  have hSheaf : (S.map U).Exact := by
    have h := hP.map (presheafToSheaf J AddCommGrpCat.{u + 1})
    exact (ShortComplex.exact_iff_of_iso
      ((S.map U).mapNatIso (sheafificationNatIso J AddCommGrpCat.{u + 1}))).2 h
  exact (S.exact_map_iff_of_faithful U).1 hSheaf

private theorem exact_hom {C : Type*} [Category* C] [Abelian C]
    (S : ShortComplex C) (hS : S.Exact) (I : C) [Injective I] :
    Function.Exact (fun f : S.X₃ ⟶ I ↦ S.g ≫ f) (fun f : S.X₂ ⟶ I ↦ S.f ≫ f) := by
  intro f
  constructor
  · intro hf
    exact ⟨hS.descToInjective f hf, hS.comp_descToInjective f hf⟩
  · rintro ⟨g, rfl⟩
    change S.f ≫ (S.g ≫ g) = 0
    rw [← Category.assoc, S.zero, zero_comp]

private theorem fixed_actionAbelian : ActionAbelian A G := by
  obtain ⟨ab, _⟩ := GroupAlgebra.exists_abelian A.toMon G
  have hz : @Preadditive.preadditiveHasZeroMorphisms _ _ ab.toPreadditive =
      @Preadditive.preadditiveHasZeroMorphisms _ _
        (Profinite.CondensedAction.actionPreadditive (R := A.toMon) (P := G)) :=
    Subsingleton.elim _ _
  exact
    { normalMono := hz ▸ ab.toIsNormalMonoCategory
      normalEpi := hz ▸ ab.toIsNormalEpiCategory
      products := ab.has_finite_products
      kernels := hz ▸ ab.has_kernels
      cokernels := hz ▸ ab.has_cokernels }

/-- The normalized internal equivariant Hom sheaves of the bar into an injective
form exact augmented rows, with the inhomogeneous faces, degeneracies, alternating
signs and invariant augmentation supplied by the recorded bar data.
Source: main-20261015 direct-image proof paragraph (3), internal-bar expansion
(blueprint: lem-sfb-condensed-injective-bar-rows).

Proof:
1. Tensor the exact augmented homogeneous bar with A[S], using
lem-sfb-condensed-internal-bar-resolution. The equivariant category is abelian by
lem-sfb-condensed-group-algebra-exact-forgetful. No projectivity or flatness is used.
2. By lem-sfb-condensed-free-linearization-tensor, maps are specified on parametrized
free generators. Send f to c(s;b_1,...,b_p)=f(s;1,b_1,b_1*b_2,...,b_1*...*b_p).
The inverse sends c to g_0*c(s;g_0^(-1)*g_1,...,g_(p-1)^(-1)*g_p).
Equivariance and cancellation show that these formulas are inverse and linear.
3. The evaluation of InternalFunctions identifies these natural families with sections
of the specified internal Hom. The formulas commute with restriction and equivariant
postcomposition, so this represents the Hom presheaf by the existing bar sheaves.
4. Deleting the first homogeneous coordinate gives the first action face; deleting an
interior coordinate multiplies the adjacent ratios in their stated order; deleting the
last drops the last ratio. These are exactly B.face on every generalized generator.
5. Repeating a homogeneous coordinate inserts 1 in the ratios, giving B.degeneracy.
Alternating deletion gives the alternating cochain differential, with no extra sign.
For p=0 the two faces give g*m and m, hence g*m-m.
6. A cocycle Q_p -> I kills the kernel of Q_p -> Q_(p-1), and factors through its image
by the image/coimage identity in the abelian equivariant category. Injectivity of I
extends this factorization across the image inclusion into Q_(p-1). The extension
is the required coboundary. Conversely every coboundary is a cocycle.
7. In degree zero the epimorphic augmentation gives unique factorization through A[S].
Equivariance is exactly FixedAll, including every base change, so this factorization
is the invariant inclusion and is injective, as specified by V and a.
8. S was arbitrary: this proves sectionwise exactness, which implies equality of the
image and kernel subsheaves internally. The coordinate formulas already prove all
naturality assertions; no natural choice of the injective extension is claimed.
-/
theorem nonempty_injectiveRows (F : InternalFunctions A) (B : BarDiagram (G := G) F)
    (V : Invariants A G) (a : Augmentation V B) (E : Resolution A.toMon G) :
    Nonempty (InjectiveRows F B V a E) := by
  classical
  obtain ⟨c⟩ := nonempty_homCoordinates F B V a E
  let : ActionAbelian A G := fixed_actionAbelian
  have monoS (I : Equivariant A G) (S : Profinite.{u}) :
      Function.Injective (onSections A.toMon ((a.map.app I).f 0) S) := by
    intro x y hxy
    apply (c.invariantsEquiv I S).injective
    let := E.tensor_augmentation_epi (freeParameter A S)
    apply (cancel_epi (E.tensorAugmentation (freeParameter A S))).1
    simpa only [← c.augmentation_hom] using congrArg (c.homEquiv I 0 S) hxy
  have exactS (I : Equivariant A G) [Injective I] (n : ℕ) (S : Profinite.{u}) :
      Function.Exact (onSections A.toMon (((cochains B).obj I).d n (n + 1)) S)
        (onSections A.toMon (((cochains B).obj I).d (n + 1) (n + 2)) S) := by
    intro x
    constructor
    · intro hx
      have hf : E.tensorBoundary (freeParameter A S) (n + 1) ≫
          c.homEquiv I (n + 1) S x = 0 := by
        rw [← c.differential, hx, map_zero]
      obtain ⟨h, hh⟩ := (exact_hom
        (ShortComplex.mk (E.tensorBoundary (freeParameter A S) (n + 1))
          (E.tensorBoundary (freeParameter A S) n)
          (by exact E.tensor_boundary_boundary (freeParameter A S) n))
        (E.tensor_exact_succ (freeParameter A S) n) I
          (c.homEquiv I (n + 1) S x)).mp hf
      refine ⟨(c.homEquiv I n S).symm h, ?_⟩
      apply (c.homEquiv I (n + 1) S).injective
      rw [c.differential, AddEquiv.apply_symm_apply]
      exact hh
    · rintro ⟨y, rfl⟩
      apply (c.homEquiv I (n + 2) S).injective
      rw [map_zero, c.differential, c.differential, ← Category.assoc,
        E.tensor_boundary_boundary, zero_comp]
  have exact0S (I : Equivariant A G) [Injective I] (S : Profinite.{u}) :
      Function.Exact (onSections A.toMon ((a.map.app I).f 0) S)
        (onSections A.toMon (((cochains B).obj I).d 0 1) S) := by
    intro x
    constructor
    · intro hx
      have hf : E.tensorBoundary (freeParameter A S) 0 ≫ c.homEquiv I 0 S x = 0 := by
        rw [← c.differential, hx, map_zero]
      obtain ⟨h, hh⟩ := (exact_hom
        (ShortComplex.mk (E.tensorBoundary (freeParameter A S) 0)
          (E.tensorAugmentation (freeParameter A S))
          (by exact E.tensor_boundary_augmentation (freeParameter A S)))
        (E.tensor_exact_zero (freeParameter A S)) I (c.homEquiv I 0 S x)).mp hf
      refine ⟨(c.invariantsEquiv I S).symm h, ?_⟩
      apply (c.homEquiv I 0 S).injective
      rw [c.augmentation_hom, AddEquiv.apply_symm_apply]
      exact hh
    · rintro ⟨y, rfl⟩
      apply (c.homEquiv I 1 S).injective
      rw [map_zero, c.differential, c.augmentation_hom, ← Category.assoc,
        E.tensor_boundary_augmentation, zero_comp]
  refine ⟨{
    homEquiv := fun I _ n S ↦ c.homEquiv I n S
    coordinates := fun I _ ↦ c.coordinates I
    restriction := fun I _ ↦ c.restriction I
    naturality := fun I J _ _ ↦ c.naturality I J
    differential := fun I _ ↦ c.differential I
    augmentation := fun I _ ↦ c.augmentation I
    degreeZero := fun I _ ↦ bar_degreeZero F B I
    mono := fun I _ ↦ mono_of_sections _ (monoS I)
    mono_sections := fun I _ ↦ monoS I
    exact_sections_zero := fun I _ ↦ exact0S I
    exact_sections_succ := fun I _ ↦ exactS I
    exact_zero := ?_
    exact_succ := ?_ }⟩
  · intro I _
    have w : (a.map.app I).f 0 ≫ ((cochains B).obj I).d 0 1 = 0 := by
      simp
    exact ⟨w, exact_of_sections _ (exact0S I)⟩
  · intro I _ n
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
    exact exact_of_sections _ (exactS I n)

end CategoryTheory.CondensedBar
