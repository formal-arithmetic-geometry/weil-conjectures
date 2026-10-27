/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.EtaleCoefficientSystemAdjoint
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.CategoryTheory.SystemLevelLeftExtension

/-!
# Free insertion and compact-support quotient mates

Source: blueprint `prop-coef-integral-exceptional-adjoint.proof.md`, second and final
paragraphs; Zheng, Construction 4.1 and Lemmas 5.16 and 5.22
(blueprint: lem-coef-free-insertion-compact-support-coherence).

All categories are ordinary unbounded derived categories of strict systems or of
coefficient-level module sheaves. Index `n` means the positive exponent `n + 1`.
The helpers construct actual natural transformations by the recorded adjunctions.
The reference exceptional-adjoint package supplies the canonical quotient projection;
the right adjoints in the theorem are arbitrary choices, independent of that package.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open SheafOfModules
namespace AlgebraicGeometry

section Maps
variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport O ell c)

/-- The transpose-defined free-insertion map `a_n`. The inverse mate of the canonical
compact-support evaluation square transposes the identity after the free-insertion unit.
Source: blueprint exceptional-adjoint proof, second paragraph; Zheng, Construction 4.1
(blueprint: lem-coef-free-insertion-compact-support-coherence). -/
def strictEtaleFreeInsertion (n : ℕ) :
    S.levelFunctor n ⋙ S.PY.derivedExtension n ⟶ S.PX.derivedExtension n ⋙ S.functor :=
  ((mateEquiv (S.PX.derivedAdj n) (S.PY.derivedAdj n)).symm
    (.mk _ _ _ _ (S.evaluation n).inv)).natTrans

variable {S}
/-- The canonical counit-compatible evaluated-right-adjoint map. Its invertibility is
asserted below; no family of evaluated objects is used to manufacture a system map.
Source: blueprint exceptional-adjoint proof, second and final paragraphs
(blueprint: lem-coef-free-insertion-compact-support-coherence). -/
def strictEtaleRightEvaluationMate
    {G : DerivedCategory (strictEtaleCoefficientSystem Y O ell) ⥤
      DerivedCategory (strictEtaleCoefficientSystem X O ell)}
    (adj : S.functor ⊣ G)
    {Gn : ∀ n : ℕ, DerivedCategory (strictEtaleLevel Y O ell n) ⥤
      DerivedCategory (strictEtaleLevel X O ell n)}
    (adjN : ∀ n : ℕ, S.levelFunctor n ⊣ Gn n) (n : ℕ) :
    G ⋙ S.PX.evaluation n ⟶ S.PY.evaluation n ⋙ Gn n :=
  (mateEquiv adj (adjN n) (.mk _ _ _ _ (S.evaluation n).inv)).natTrans

/-- The quotient mate `b`, using `q⁻¹`, the canonical compact-support projection.
Source: blueprint exceptional-adjoint proof, final paragraph; Zheng, Lemma 5.22
(blueprint: lem-coef-free-insertion-compact-support-coherence). -/
def strictEtaleQuotientMate
    (H : StrictEtaleExceptionalAdjoint O ell c S)
    {Gn : ∀ n : ℕ, DerivedCategory (strictEtaleLevel Y O ell n) ⥤
      DerivedCategory (strictEtaleLevel X O ell n)}
    (adjN : ∀ n : ℕ, S.levelFunctor n ⊣ Gn n) {m n : ℕ} (h : n ≤ m) :
    Gn m ⋙ (S.PX.scalar h).derived ⟶ (S.PY.scalar h).derived ⋙ Gn n :=
  (mateEquiv (adjN m) (adjN n)
    (.mk _ _ _ _ (H.val.quotientProjection h).hom)).natTrans

/-- Scalar-extension adjunct of the actual transition of a derived strict system.
Source: Zheng, Construction 4.1; blueprint exceptional-adjoint proof, final paragraph
(blueprint: lem-coef-free-insertion-compact-support-coherence). -/
def strictEtaleAdjointTransition
    {T : Scheme.{u}} (P : StrictEtaleEvaluation T O ell)
    {m n : ℕ} (h : n ≤ m)
    (M : DerivedCategory (strictEtaleCoefficientSystem T O ell)) :
    (P.scalar h).derived.obj ((P.evaluation m).obj M) ⟶ (P.evaluation n).obj M :=
  ((P.scalar h).derivedAdj.homEquiv _ _).symm ((P.transition h).app M)
end Maps

/-- Free insertion commutes with compact support, coherently with truncation; its
representing bijections identify the evaluated exceptional adjoint, unit, counit and
actual quotient transitions. All assertions hold for unbounded inputs and arbitrary
chosen right adjoints. The two final equations give invariance under their unique
counit-compatible changes.

Source: blueprint `prop-coef-integral-exceptional-adjoint.proof.md`, second and final
paragraphs; Zheng, Construction 4.1 and Lemmas 5.16 and 5.22
(blueprint: lem-coef-free-insertion-compact-support-coherence).

Proof plan:
1. Apply lem-pur-etale-system-brown-construction to O=R and ell=varpi. Its left
extension and that of lem-pur-coefficient-evaluation-derived-left-adjoint are the total
left derived functor of the same strict insertion (lem-pur-system-level-left-extension).
Identify them by the unique unit-compatible isomorphism. Brown supplies an actual
isomorphism whose r-component below n is q(n,r). At n the coefficient-projection identity
clause (lem-pur-etale-system-coefficient-projection) and x -> x tensor 1 identify its
transpose with the identity. Injectivity of the insertion Hom bijection identifies it
with strictEtaleFreeInsertion. This proves invertibility and its evaluated formula.
2. Transpose both sides of the sigma equation under L_n/e_n. The explicit sigma
formula gives the identity on evaluation n. On the other side the evaluated insertion
map is q(m,n) and cancels q(m,n) inverse. Injectivity of this single Hom bijection proves
the equation on actual derived-system maps, naturally in the level-m input.
3. Apply lem-pur-etale-system-evaluation-bound to the given adjunctions and the
canonical evaluation/insertion comparisons. Its representing Hom bijection is exactly
the composite displayed below, by step 1. Yoneda identifies the evaluated right adjoint
with G_n e_n; its counit and unit are exactly the finite-level ones. No amplitude
hypothesis is needed for these clauses of that lemma.
4. The transition clause of the same evaluation-bound theorem identifies the actual
transition of G N with G_n(t_N) after the quotient mate. Expand this transpose using
(def-weil-pbc-adjunction-mate) to obtain the displayed unit, inverse projection and
counit composite. The argument applies to arbitrary unbounded systems and derived maps.
5. For any other right adjoints use det-sp-unique-right-adjoint. Their unique comparison
isomorphisms intertwine counits. Under step 3 the Hom bijections therefore agree, which
gives the evaluation comparison equation below. Substitution in the counit composite
characterizing b gives the quotient-mate equation. The transition formula is preserved;
the unit is preserved as the transpose of the identity. -/
theorem freeInsertionCompactSupportCoherence
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) c)
    (H : StrictEtaleExceptionalAdjoint _ _ c S)
    (G : DerivedCategory (strictEtaleCoefficientSystem Y
        (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E)) ⥤
      DerivedCategory (strictEtaleCoefficientSystem X
        (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E)))
    (adj : S.functor ⊣ G)
    (Gn : ∀ n : ℕ, DerivedCategory (strictEtaleLevel Y
        (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E) n) ⥤
      DerivedCategory (strictEtaleLevel X
        (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E) n))
    (adjN : ∀ n : ℕ, S.levelFunctor n ⊣ Gn n) :
    (∀ n : ℕ, IsIso (strictEtaleFreeInsertion S n)) ∧
    (∀ (n r : ℕ) (h : r ≤ n) K,
      (S.PY.evaluation r).map ((strictEtaleFreeInsertion S n).app K) ≫
        (S.evaluation r).hom.app ((S.PX.derivedExtension n).obj K) ≫
        (S.levelFunctor r).map ((S.PX.derivedBelow h).hom.app K) =
      (S.PY.derivedBelow h).hom.app ((S.levelFunctor n).obj K) ≫
        (H.val.quotientProjection h).inv.app K) ∧
    (∀ (m n : ℕ) (h : n ≤ m) K,
      (strictEtaleFreeInsertion S n).app ((S.PX.scalar h).derived.obj K) ≫
        S.functor.map ((S.PX.sigma h).app K) =
      (S.PY.derivedExtension n).map ((H.val.quotientProjection h).hom.app K) ≫
        (S.PY.sigma h).app ((S.levelFunctor m).obj K) ≫
        (strictEtaleFreeInsertion S m).app K) ∧
    (∀ n : ℕ, IsIso (strictEtaleRightEvaluationMate adj adjN n)) ∧
    (∀ (n : ℕ) K N (h : K ⟶ (S.PX.evaluation n).obj (G.obj N)),
      (S.PY.derivedAdj n).homEquiv _ _
        ((strictEtaleFreeInsertion S n).app K ≫
          (adj.homEquiv _ _).symm (((S.PX.derivedAdj n).homEquiv _ _).symm h)) =
      ((adjN n).homEquiv _ _).symm
        (h ≫ (strictEtaleRightEvaluationMate adj adjN n).app N)) ∧
    (∀ (n : ℕ) M,
      (S.PX.evaluation n).map (adj.unit.app M) ≫
        (strictEtaleRightEvaluationMate adj adjN n).app (S.functor.obj M) ≫
        (Gn n).map ((S.evaluation n).hom.app M) =
      (adjN n).unit.app ((S.PX.evaluation n).obj M)) ∧
    (∀ (n : ℕ) N,
      (S.levelFunctor n).map ((strictEtaleRightEvaluationMate adj adjN n).app N) ≫
        (adjN n).counit.app ((S.PY.evaluation n).obj N) =
      (S.evaluation n).inv.app (G.obj N) ≫ (S.PY.evaluation n).map (adj.counit.app N)) ∧
    (∀ (m n : ℕ) (h : n ≤ m) M,
      (strictEtaleQuotientMate H adjN h).app M =
      (adjN n).unit.app ((S.PX.scalar h).derived.obj ((Gn m).obj M)) ≫
        (Gn n).map ((H.val.quotientProjection h).hom.app ((Gn m).obj M)) ≫
        (Gn n).map ((S.PY.scalar h).derived.map ((adjN m).counit.app M))) ∧
    (∀ (m n : ℕ) (h : n ≤ m) N,
      strictEtaleAdjointTransition S.PX h (G.obj N) ≫
        (strictEtaleRightEvaluationMate adj adjN n).app N =
      (S.PX.scalar h).derived.map ((strictEtaleRightEvaluationMate adj adjN m).app N) ≫
        (strictEtaleQuotientMate H adjN h).app ((S.PY.evaluation m).obj N) ≫
        (Gn n).map (strictEtaleAdjointTransition S.PY h N)) ∧
    (∀ (G' : DerivedCategory (strictEtaleCoefficientSystem Y
          (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E)) ⥤
        DerivedCategory (strictEtaleCoefficientSystem X
          (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E)))
      (adj' : S.functor ⊣ G')
      (Gn' : ∀ n : ℕ, DerivedCategory (strictEtaleLevel Y
          (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E) n) ⥤
        DerivedCategory (strictEtaleLevel X
          (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E) n))
      (adjN' : ∀ n : ℕ, S.levelFunctor n ⊣ Gn' n),
      (∀ (n : ℕ) N,
        (S.PX.evaluation n).map ((adj.rightAdjointUniq adj').hom.app N) ≫
          (strictEtaleRightEvaluationMate adj' adjN' n).app N =
        (strictEtaleRightEvaluationMate adj adjN n).app N ≫
          ((adjN n).rightAdjointUniq (adjN' n)).hom.app ((S.PY.evaluation n).obj N)) ∧
      (∀ (m n : ℕ) (h : n ≤ m) M,
        (S.PX.scalar h).derived.map (((adjN m).rightAdjointUniq (adjN' m)).hom.app M) ≫
          (strictEtaleQuotientMate H adjN' h).app M =
        (strictEtaleQuotientMate H adjN h).app M ≫
          ((adjN n).rightAdjointUniq (adjN' n)).hom.app ((S.PY.scalar h).derived.obj M))) := by
  sorry

end AlgebraicGeometry
