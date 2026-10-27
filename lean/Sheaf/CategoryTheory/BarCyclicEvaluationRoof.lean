/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.CategoryTheory.RelativeTrivialCyclicMap
public import Sheaf.CategoryTheory.CyclicRowDerivedComparison
public import Sheaf.CategoryTheory.InternalBarRoofAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus

/-! # Evaluation from the compatible bar total to the cyclic total

Source: latest blueprint, six-functors direct-image stability proof, paragraph (3),
agent-extracted cyclic calculation, steps 15--18; the combined external reference is wanted.
(blueprint: lem-sfb-bar-cyclic-evaluation-roof).

The scalar cyclic total below is the existing relative total with trivial residual group.
Its two coordinates, differential and functorial maps are those of `TotalModel`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar CategoryTheory.RelativeCyclic
open Profinite.CondensedAction (inflate)
namespace CategoryTheory.BarCyclicEvaluation

variable {A : CondensedBar.Ring.{u}} {H : Type u}
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction along the chosen cyclic homomorphism, with trivial residual action.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def input (v : Z.{u} →ₜ* H) :
    Equivariant A H ⥤ Equivariant A (PUnit.{u + 1} × Z.{u}) :=
  inflate (R := A.toMon) v ⋙ addTrivialResidual A

/-- Restriction and trivial inflation keep the original addition on maps.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
instance inputAdditive (v : Z.{u} →ₜ* H) : (input (A := A) v).Additive :=
  inferInstanceAs ((inflate (R := A.toMon) v ⋙ addTrivialResidual A).Additive)

/-- The scalar cyclic total on a complex, using the existing two-column total.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def total (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H)
    (N : CochainComplex (Equivariant A H) ℤ) : CochainComplex (Modules A) ℤ :=
  ((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
    (.up ℤ)).obj (K.functor.obj (((input v).mapHomologicalComplex (.up ℤ)).obj N))

/-- Projection onto the resolution-degree-n coordinate of the scalar cyclic total.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def first (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H)
    (N : CochainComplex (Equivariant A H) ℤ) (n : ℤ) :
    (total K v N).X n ⟶ (N.X n).module :=
  CondensedBar.forgetAction.map
    ((K.coordinates (((input v).mapHomologicalComplex (.up ℤ)).obj N) n).hom ≫ biprod.fst)

/-- Projection onto the resolution-degree-(n-1) coordinate of the scalar cyclic total.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def second (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H)
    (N : CochainComplex (Equivariant A H) ℤ) (n : ℤ) :
    (total K v N).X n ⟶ (N.X (n - 1)).module :=
  CondensedBar.forgetAction.map
    ((K.coordinates (((input v).mapHomologicalComplex (.up ℤ)).obj N) n).hom ≫ biprod.snd)

/-- The identity-underlying comparison of the two presentations of restricted trivial R.
Source: paragraph (3), step 17 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def regularIso (v : Z.{u} →ₜ* H) :
    trivialInput (A := A) v ≅
      (input v).obj (CondensedDerivedRestriction.regularTrivial A H) where
  hom := ⟨𝟙 _, fun _ _ _ ↦ rfl⟩
  inv := ⟨𝟙 _, fun _ _ _ ↦ rfl⟩

/-- Apply K(V-) to the specified resolution augmentation, with its single-complex
and trivial-coefficient identifications. This is k, not an arbitrary denominator.
Source: paragraph (3), step 17 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def resolutionMap (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) :
    extend (trivialCyclic A) ⟶ total K v I.cochainComplex :=
  (trivialTotalIso K v).inv ≫
    ((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
      (.up ℤ)).map
      (K.functor.map
        ((HomologicalComplex.single _ (.up ℤ) 0).map (regularIso v).hom ≫
          ((HomologicalComplex.singleMapHomologicalComplex (input v) (.up ℤ) 0).inv.app
            (CondensedDerivedRestriction.regularTrivial A H)) ≫
          ((input v).mapHomologicalComplex (.up ℤ)).map I.ι'))

variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The (p,q)-summand included into the integer-indexed compatible finite total.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def summand (M : BarModel A H)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) (p q : ℕ) :
    ((cochains (barDiagram M)).obj (I.cocomplex.X q)).X p ⟶
      (extend ((totalCochains (barDiagram M)).obj I.cocomplex)).X (p + q : ℕ) :=
  (doubleComplex (barDiagram M) I.cocomplex).ιTotal (.up ℕ) p q (p + q) rfl ≫
    (((totalCochains (barDiagram M)).obj I.cocomplex).extendXIso
      ComplexShape.embeddingUpNat (i := p + q) (i' := (p + q : ℕ)) rfl).inv

/-- The first cyclic coordinate identified with its nonnegative resolution term.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def firstNat (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) (q : ℕ) :
    (total K v I.cochainComplex).X q ⟶ (I.cocomplex.X q).module :=
  first K v I.cochainComplex q ≫ CondensedBar.forgetAction.map
    (I.cocomplex.extendXIso ComplexShape.embeddingUpNat (i := q) (i' := q) rfl).hom

/-- The second cyclic coordinate identified with its nonnegative resolution term.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def secondNat (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) (q : ℕ) :
    (total K v I.cochainComplex).X (1 + q : ℕ) ⟶ (I.cocomplex.X q).module :=
  second K v I.cochainComplex (1 + q : ℕ) ≫ CondensedBar.forgetAction.map
    (I.cocomplex.extendXIso ComplexShape.embeddingUpNat
      (i := q) (i' := ((1 + q : ℕ) : ℤ) - 1) (by simp [ComplexShape.embeddingUpNat])).hom

/-- Evaluate an existing bar term on a continuous tuple, after every profinite base change.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def value (M : BarModel A H) (N : Equivariant A H) (p : ℕ) (S : Profinite.{u})
    (x : sections A (((cochains (barDiagram M)).obj N).X p) S)
    (g : C(S, power H p)) : sections A N.module S :=
  ((barFunctions M).evaluate (power H p) S N.module
    (((barDiagram M).term N p).hom.hom.hom.app (op S) x)).val S (𝟙 S) g

/-- The exact two-coordinate specification of E: identity in bar degree zero,
evaluation at tau in degree one, and zero on all other input columns.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def Coordinates (M : BarModel A H) (K : TotalModel A PUnit.{u + 1})
    (v : Z.{u} →ₜ* H)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H))
    (E : extend ((totalCochains (barDiagram M)).obj I.cocomplex) ⟶
      total K v I.cochainComplex) : Prop :=
  (∀ (q : ℕ) (S : Profinite.{u})
    (x : sections A (((cochains (barDiagram M)).obj (I.cocomplex.X q)).X 0) S),
    ((summand M I 0 q ≫ eqToHom (by congr 1; omega) ≫
      E.f q ≫ firstNat K v I q).hom.hom.app (op S)) x =
      value M (I.cocomplex.X q) 0 S x (ContinuousMap.const S (fun _ ↦ 1))) ∧
  (∀ (p q : ℕ), 0 < p →
    summand M I p q ≫ E.f (p + q : ℕ) ≫ first K v I.cochainComplex (p + q : ℕ) = 0) ∧
  (∀ (q : ℕ) (S : Profinite.{u})
    (x : sections A (((cochains (barDiagram M)).obj (I.cocomplex.X q)).X 1) S),
    ((summand M I 1 q ≫ E.f (1 + q : ℕ) ≫ secondNat K v I q).hom.hom.app (op S)) x =
      value M (I.cocomplex.X q) 1 S x (ContinuousMap.const S (fun _ ↦ v generator))) ∧
  (∀ (p q : ℕ), p ≠ 1 →
    summand M I p q ≫ E.f (p + q : ℕ) ≫ second K v I.cochainComplex (p + q : ℕ) = 0)

/-- The degree-zero horizontal differential evaluated at tau is tau times m minus m.
All sections are quantified, so this is the internal formula, including every base change.
Source: paragraph (3), step 16 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def Horizontal (M : BarModel A H) (v : Z.{u} →ₜ* H)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) : Prop :=
  ∀ (q : ℕ) (S : Profinite.{u})
    (x : sections A (((cochains (barDiagram M)).obj (I.cocomplex.X q)).X 0) S),
    value M (I.cocomplex.X q) 1 S
        ((((cochains (barDiagram M)).obj (I.cocomplex.X q)).d 0 1).hom.hom.app (op S) x)
        (ContinuousMap.const S (fun _ ↦ v generator)) =
      @id (sections A (I.cocomplex.X q).module S)
        ((I.cocomplex.X q).act S (ContinuousMap.const S (v generator))
          (value M (I.cocomplex.X q) 0 S x (ContinuousMap.const S (fun _ ↦ 1)))) -
        value M (I.cocomplex.X q) 0 S x (ContinuousMap.const S (fun _ ↦ 1))

/-- The invariant-to-bar chain map b_H, extended by zero to integer degrees.
Source: paragraph (3), step 15 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def invariantMap (M : BarModel A H)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) :=
  HomologicalComplex.extendMap ((barTotalAugmentation M).map.app I.cocomplex)
    ComplexShape.embeddingUpNat

/-- The canonical source-resolution identification sigma. The definition of barEta
makes this precisely the inverse resolution computation followed by invariant normalization.
Source: paragraph (3), step 17 (blueprint: lem-sfb-bar-cyclic-evaluation-roof). -/
def sourceIso (M : BarModel A H) (b : BarNormalization M)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) :=
  (DerivedCategory.Q.mapIso ((ComplexShape.embeddingUpNat.extendFunctor (Modules A)).mapIso
    ((NatIso.mapHomologicalComplex b.invariants (.up ℕ)).app I.cocomplex))).symm ≪≫
    (scalarResolutionIso (CondensedDerivedRestriction.regularTrivial A H) I).symm

/-- K(Va) is a quasi-isomorphism; restriction of I need not be injective.
Source: paragraph (3), extracted step 17 (blueprint: lem-sfb-bar-cyclic-evaluation-roof).
Proof: restriction is exact by lem-sfb-condensed-derived-restriction-calculus, so Va is
an augmented bounded-below quasi-isomorphism. The two-column total preserves such maps
by lem-sfb-cyclic-total-triangulated (trivial residual group), or directly by its two
column filtration. The coordinate identification of its source with [R -> 0 R] is an
isomorphism. Thus the displayed resolutionMap is a quasi-isomorphism. -/
@[instance] theorem resolutionMap_quasiIso (K : TotalModel A PUnit.{u + 1})
    (v : Z.{u} →ₜ* H)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) :
    QuasiIso (resolutionMap K v I) := by
  sorry

/-- The full cyclic evaluation roof, on every specified compatible injective resolution.
Source: paragraph (3), extracted steps 15--18
(blueprint: lem-sfb-bar-cyclic-evaluation-roof).

Proof, following the six DAG steps:
1. Internal evaluation precomposes with R -> R[H], 1 maps to [tau], on every base.
   The face rules of def-sfb-condensed-equivariant-bar-data give (d_h m)(tau)=tau m-m.
   Evaluation commutes with restriction and every coefficient map, including d_I.
2. On the finite-diagonal total put E(z)=(z_0,ev_tau z_1). The vertical differential
   has sign minus in column one. Hence E d(z)=(d_I z_0,(T-1)z_0-d_I ev_tau z_1)=d E(z).
   Higher columns contribute to neither output coordinate. On b_H only the first
   coordinate survives, and it is the actual invariant inclusion.
3. For trivial coefficients this is the existing epsilon. The augmentation j_rep
   postcomposes by a^0. Evaluation commutes with that map, so j_rep E=epsilon k in
   categorical order, including all zero higher components.
4. Exact cyclic restriction and lem-sfb-cyclic-total-triangulated make k=K(Va) a
   quasi-isomorphism, as resolutionMap_quasiIso states. No injectivity of VI is used.
5. Put A=RGamma_H(Qa), B=RGamma_Z(QVa), C=Qk. The normalized source identification
   is sigma=A inverse alpha_H,I: both factors are invertible by injective computation.
   lem-sfb-relative-restriction-mate-forgetting gives beta_I alpha_H,I=alpha_Z,VI Q(iota).
   lem-sfb-cyclic-row-derived-comparison gives theta_VI alpha_Z,VI=Qb_VI even for VI.
   Naturality gives beta_I A=B beta_R and theta_VI B=C theta_R. Therefore c sigma is
   Q(E b_H) followed by C inverse. The coordinate equality in step 2 identifies b_VI iota.
6. lem-sfb-internal-bar-roof-adjunction fixes eta sigma=Qb_H with Qb_H invertible.
   Cancel Qb_H in c eta inverse j, apply step 3, and cancel Qk to obtain Qepsilon.
   Neither beta nor j is inverted, and the underived bar is not asserted acyclic.
-/
theorem bar_cyclic_evaluation_roof (K : TotalModel A PUnit.{u + 1})
    (C : HasComparison A PUnit.{u + 1} K) (v : Z.{u} →ₜ* H)
    (M : BarModel A H) (b : BarNormalization M)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) :
    Horizontal M v I ∧
    ∃ E : extend ((totalCochains (barDiagram M)).obj I.cocomplex) ⟶
        total K v I.cochainComplex,
      Coordinates M K v I E ∧
      (∀ n : ℕ,
        ((invariantMap M I) ≫ E).f n ≫ firstNat K v I n =
          ((((barInvariants M).functor.mapHomologicalComplex (.up ℕ)).obj
            I.cocomplex).extendXIso ComplexShape.embeddingUpNat
            (i := n) (i' := n) rfl).hom ≫
              (barInvariants M).inclusion.app (I.cocomplex.X n)) ∧
      (∀ n : ℤ, ((invariantMap M I) ≫ E).f n ≫ second K v I.cochainComplex n = 0) ∧
      (HomologicalComplex.extendMap
          (barAugmentation (barFunctions M) (barDiagram M)
            (CondensedDerivedRestriction.regularTrivial A H) I) ComplexShape.embeddingUpNat ≫
        E = HomologicalComplex.extendMap
          (RelativeCyclic.evaluation (barFunctions M) (barDiagram M) v)
          ComplexShape.embeddingUpNat ≫
            resolutionMap K v I) ∧
      ((sourceIso M b I).hom ≫ trivialCyclicMap C v =
        DerivedCategory.Q.map (invariantMap M I ≫ E) ≫
          inv (DerivedCategory.Q.map (resolutionMap K v I))) ∧
      (DerivedCategory.Q.map (HomologicalComplex.extendMap
          (barAugmentation (barFunctions M) (barDiagram M)
            (CondensedDerivedRestriction.regularTrivial A H) I) ComplexShape.embeddingUpNat) ≫
        (barEta M b (CondensedDerivedRestriction.regularTrivial A H) I).inv ≫
          trivialCyclicMap C v =
        DerivedCategory.Q.map (HomologicalComplex.extendMap
          (RelativeCyclic.evaluation (barFunctions M) (barDiagram M) v)
          ComplexShape.embeddingUpNat)) := by
  sorry

end CategoryTheory.BarCyclicEvaluation
