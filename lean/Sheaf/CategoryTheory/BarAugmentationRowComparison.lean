module

public import Sheaf.CategoryTheory.RelativeBarData
public import Sheaf.CategoryTheory.CondensedBarTotalNaturality
public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
public import WeilConjectures.CategoryTheory.DoubleComplexTotal

/-! # The actual bar augmentation from positive-row collapse

Source: Stacks Project, homology.tex Tags 0130, 0132, 0133 and derived.tex Tags 013P,
013S; agent positive-E2-row refinement of the internal-bar input in the latest blueprint,
six-functors direct-images proof, paragraph (3)
(blueprint: lem-sfb-bar-augmentation-row-comparison).

The augmentation is the existing `RelativeCyclic.barAugmentation`, whose components are
postcomposition with the resolution augmentation followed by the (n,0) coprojection.
After extension by zero, all localization takes place in the ordinary derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar

variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The horizontal complex of internal vertical cohomology objects, without evaluating
sections. Source: Stacks 0130 (blueprint: lem-sfb-bar-augmentation-row-comparison). -/
def verticalCohomologyRow {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (I : CochainComplex (Equivariant A G) ℕ) (q : ℕ) :
    CochainComplex (Modules A) ℕ :=
  ((HomologicalComplex.homologyFunctor (Modules A) (.up ℕ) q).mapHomologicalComplex
    (.up ℕ)).obj (doubleComplex B I)

/-- A compatible change of bar diagram induces the actual finite-total isomorphism.
Source: normalized bar-model comparison, paragraph (3)
(blueprint: lem-sfb-bar-augmentation-row-comparison). -/
def barDiagramTotalIso {F F' : InternalFunctions A}
    {B : BarDiagram (G := G) F} {B' : BarDiagram (G := G) F'}
    (e : cochains B ≅ cochains B') (I : CochainComplex (Equivariant A G) ℕ) :
    (totalCochains B).obj I ≅ (totalCochains B').obj I :=
  (HomologicalComplex₂.flipFunctor (Modules A) (.up ℕ) (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor (Modules A) (.up ℕ) (.up ℕ) (.up ℕ)).mapIso
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app I)

variable [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- Column-wise quasi-isomorphisms are a sufficient special case of the row hypothesis.
Source: Stacks 0133 (blueprint: lem-sfb-bar-augmentation-row-comparison).
Proof: step 7 of the node. A column augmentation from a single object which is a
quasi-isomorphism forces all strictly positive vertical cohomology objects to vanish.
Thus each positive vertical-cohomology row is the zero complex and has zero cohomology.
This implication does not assume the row hypothesis.
-/
theorem bar_augmentation_columns_imply_rows (M : Model A G) (N : Modules A)
    (hcolumns : ∀ (I : InjectiveResolution
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)) (p : ℕ),
      QuasiIso (((cochains M.bar ⋙
        HomologicalComplex.eval (Modules A) (.up ℕ) p).mapHomologicalComplex
          (.up ℕ)).map I.ι)) :
    ∀ (I : InjectiveResolution
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)) (p q : ℕ),
      0 < q → IsZero ((verticalCohomologyRow M.bar I.cocomplex q).homology p) := by
  intro I p q hq
  let F := cochains M.bar ⋙ HomologicalComplex.eval (Modules A) (.up ℕ) p
  let f := (F.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso f := hcolumns I p
  have hsource : ((F.mapHomologicalComplex (.up ℕ)).obj
      ((CochainComplex.single₀ (Equivariant A G)).obj
        ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N))).ExactAt q := by
    apply HomologicalComplex.ExactAt.of_isZero
    exact F.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 _ q
      (Nat.ne_of_gt hq))
  have hcolumn := ((exactAt_iff_of_quasiIsoAt f q).mp hsource).isZero_homology
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  exact hcolumn

/-- Positive internal vertical-cohomology rows suffice for the specified augmentation.
Every resolution and every compatible model retains its actual augmentation morphism.
Source: Stacks 0130, 0132, 0133, 013P and 013S; latest blueprint direct-images proof,
paragraph (3), formal internal-bar refinement
(blueprint: lem-sfb-bar-augmentation-row-comparison).

Proof (the eight steps of the node).
1. Equivariance makes postcomposition by s^0 commute with every bar face, including
   the action face. The equation d_I s^0 = 0 kills the vertical contribution. The
   existing unique augmentation therefore has exactly the displayed components.
2. The computation datum makes forgetting exact. Internal Hom is a right adjoint,
   so it preserves the kernel of UI^0 -> UI^1. Naturality with every face identifies
   the zero vertical-cohomology row with the underived bar as a complex.
3. Compare the functorial first-quadrant spectral sequences with the single-row
   double complex. The positive E2 rows vanish by hypothesis and the bottom-row map
   is the kernel isomorphism from step 2. Finite-diagonal convergence and the
   row-collapse edge square make H^n of this very augmentation invertible. Extension
   by zero handles negative degrees, so its ordinary localization is invertible.
4. Postcomposition by any augmentation-preserving lift gives strict equality of
   augmented total maps. Two-out-of-three makes its total map a quasi-isomorphism.
5. Injective-resolution lifting gives identity lifts in both directions. Uniqueness
   up to equivariant homotopy and the signed total homotopy (-1)^p h in bar degree p
   give equal localized maps and inverse changes of resolution.
6. The inverse derived-unit comparison on UI identifies each column with the actual
   second-variable derived internal Hom. Its unit equation identifies the column
   augmentation with Q(Hom(s)), including every action face. Thus Q of the specified
   augmentation is the resolution augmentation into the compatible derived total.
   Internal-Hom and evaluation normalizations determine changes of bar model on
   every term. Naturality of totalization gives the displayed model-change square.
7. Column-wise quasi-isomorphisms kill every positive vertical-cohomology object,
   hence imply the weaker horizontal cohomology vanishing assumed here.
8. Evaluation on G^0 identifies C^0 with N. The two faces are gn and n; triviality
   makes their difference zero. The invariant inclusion is an isomorphism to N.
   The invariant-resolution and bar augmentations have the same (0,0) component,
   so their chain square commutes. Taking kernels in degree zero gives the normalized
   cohomology identifications and the identity H^0(a) = 1_N under them.
-/
theorem bar_augmentation_row_comparison (M : Model A G) (N : Modules A)
    (hrows : ∀ (I : InjectiveResolution
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N))
      (p q : ℕ), 0 < q → IsZero ((verticalCohomologyRow M.bar I.cocomplex q).homology p)) :
    (∀ (I : InjectiveResolution
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)),
      (∀ n : ℕ,
        (RelativeCyclic.barAugmentation M.functions M.bar _ I).f n =
          ((cochains M.bar).map (I.ι.f 0)).f n ≫
            (doubleComplex M.bar I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)) ∧
      QuasiIso (RelativeCyclic.barAugmentation M.functions M.bar _ I) ∧
      IsIso (DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap
        (RelativeCyclic.barAugmentation M.functions M.bar _ I) ComplexShape.embeddingUpNat))) ∧
    (∀ (I J : InjectiveResolution
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N))
      (f : I.cocomplex ⟶ J.cocomplex), I.ι ≫ f = J.ι →
      RelativeCyclic.barAugmentation M.functions M.bar _ I ≫ (totalCochains M.bar).map f =
        RelativeCyclic.barAugmentation M.functions M.bar _ J ∧
      QuasiIso ((totalCochains M.bar).map f) ∧
      (M.computation.iso I).hom ≫ (totalLocalization M.bar).map f =
        (M.computation.iso J).hom) ∧
    (∀ (I J : InjectiveResolution
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)),
      (∃ f : I.cocomplex ⟶ J.cocomplex, I.ι ≫ f = J.ι) ∧
      (∀ (f g : I.cocomplex ⟶ J.cocomplex), I.ι ≫ f = J.ι → I.ι ≫ g = J.ι →
        (totalLocalization M.bar).map f = (totalLocalization M.bar).map g) ∧
      (∀ (f : I.cocomplex ⟶ J.cocomplex) (g : J.cocomplex ⟶ I.cocomplex),
        I.ι ≫ f = J.ι → J.ι ≫ g = I.ι →
        (totalLocalization M.bar).map f ≫ (totalLocalization M.bar).map g = 𝟙 _ ∧
        (totalLocalization M.bar).map g ≫ (totalLocalization M.bar).map f = 𝟙 _)) ∧
    (∀ (I J : InjectiveResolution
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N))
      (f g : I.cocomplex ⟶ J.cocomplex) (h : Homotopy f g),
      I.ι ≫ f = J.ι → I.ι ≫ g = J.ι →
      ∃ H : Homotopy ((totalCochains M.bar).map f) ((totalCochains M.bar).map g),
        ∀ (p q n m : ℕ) (hpq : p + q = n),
          (doubleComplex M.bar I.cocomplex).ιTotal (.up ℕ) p q n hpq ≫ H.hom n m =
            (-1 : ℤ) ^ p • (((cochains M.bar).map (h.hom q (m - p))).f p ≫
              (doubleComplex M.bar J.cocomplex).ιTotalOrZero (.up ℕ) p (m - p) m)) ∧
    (∀ (I : InjectiveResolution
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)) (p : ℕ),
      ∃ c : (M.functions.functor (power G p)).rightDerivedFunctor.{u + 2, u + 2}.obj
          (DerivedCategory.Q.{u + 2}.obj
            ((forgetAction.mapHomologicalComplex (.up ℤ)).obj
              ((HomologicalComplex.single _ (.up ℤ) 0).obj
                ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)))) ≅
        DerivedCategory.Q.{u + 2}.obj
          (((M.functions.functor (power G p)).mapHomologicalComplex (.up ℤ)).obj
            ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)),
        c.hom ≫ (M.functions.functor (power G p)).rightDerivedFunctorUnitQ.{u + 2, u + 2}
            ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) =
          (M.functions.functor (power G p)).rightDerivedFunctor.{u + 2, u + 2}.map
            (DerivedCategory.Q.{u + 2}.map
              ((forgetAction.mapHomologicalComplex (.up ℤ)).map I.ι')) ∧
        (M.functions.functor (power G p)).rightDerivedFunctorUnitQ.{u + 2, u + 2}
            ((forgetAction.mapHomologicalComplex (.up ℤ)).obj
              ((HomologicalComplex.single _ (.up ℤ) 0).obj
                ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N))) ≫
            c.hom =
          DerivedCategory.Q.{u + 2}.map
            (((M.functions.functor (power G p)).mapHomologicalComplex (.up ℤ)).map
              ((forgetAction.mapHomologicalComplex (.up ℤ)).map I.ι'))) ∧
    (∀ M' : Model A G, ∃ e : cochains M.bar ≅ cochains M'.bar,
      (∀ (L : Equivariant A G) (p : ℕ) (S : Profinite.{u})
        (x : sections A (((cochains M.bar).obj L).X p) S),
        M'.functions.evaluate (power G p) S L.module
            ((M'.bar.term L p).hom.hom.hom.app (op S)
              (((e.hom.app L).f p).hom.hom.app (op S) x)) =
          M.functions.evaluate (power G p) S L.module
            ((M.bar.term L p).hom.hom.hom.app (op S) x)) ∧
      (∀ I : InjectiveResolution
        ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N),
        DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap
            (RelativeCyclic.barAugmentation M.functions M.bar _ I)
              ComplexShape.embeddingUpNat) ≫
          (DerivedCategory.Q.{u + 2}.mapIso
            ((ComplexShape.embeddingUpNat.extendFunctor (Modules A)).mapIso
              (barDiagramTotalIso e I.cocomplex))).hom =
        (DerivedCategory.Q.{u + 2}.mapIso
            ((ComplexShape.embeddingUpNat.extendFunctor (Modules A)).mapIso
              (e.app ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)))).hom ≫
          DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap
            (RelativeCyclic.barAugmentation M'.functions M'.bar _ I)
              ComplexShape.embeddingUpNat))) ∧
    (∃ e : ((cochains M.bar).obj
        ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)).X 0 ≅ N,
      (∀ (S : Profinite.{u}) (x : sections A
        (((cochains M.bar).obj
          ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)).X 0) S),
        e.hom.hom.hom.app (op S) x =
          (M.functions.evaluate (power G 0) S N
            ((M.bar.term
              ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N) 0).hom.hom.hom.app
                (op S) x)).val S (𝟙 S) (ContinuousMap.const S (fun i ↦ Fin.elim0 i))) ∧
      ((cochains M.bar).obj
        ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)).d 0 1 = 0 ∧
      (∃ v : M.invariants.functor.obj
          ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N) ≅ N,
        v.hom = M.invariants.inclusion.app
          ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N) ∧
        (M.augmentation.map.app
            ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)).f 0 ≫
            e.hom = v.hom ∧
        (∀ I : InjectiveResolution
          ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N),
          (CochainComplex.single₀ (Modules A)).map v.inv ≫
              M.augmentation.map.app
                ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N) ≫
              RelativeCyclic.barAugmentation M.functions M.bar _ I =
            (CochainComplex.single₀ (Modules A)).map v.inv ≫
              (HomologicalComplex.singleMapHomologicalComplex
                M.invariants.functor (.up ℕ) 0).inv.app
                ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N) ≫
              (M.invariants.functor.mapHomologicalComplex (.up ℕ)).map I.ι ≫
              M.totalAugmentation.map.app I.cocomplex) ∧
        (∃ hC : ((cochains M.bar).obj
            ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)).homology 0 ≅ N,
          ((cochains M.bar).obj
              ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)).homologyπ 0 ≫
              hC.hom =
            ((cochains M.bar).obj
              ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)).iCycles 0 ≫
              e.hom ∧
          (∀ I : InjectiveResolution
            ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N),
            ∃ (hT : ((totalCochains M.bar).obj I.cocomplex).homology 0 ≅ N)
              (hV : ((M.invariants.functor.mapHomologicalComplex (.up ℕ)).obj
                I.cocomplex).homology 0 ≅ M.invariants.functor.obj
                  ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N)),
              HomologicalComplex.homologyMap
                  (RelativeCyclic.barAugmentation M.functions M.bar _ I) 0 ≫ hT.hom = hC.hom ∧
              HomologicalComplex.homologyMap
                  (M.totalAugmentation.map.app I.cocomplex) 0 ≫ hT.hom = hV.hom ≫ v.hom ∧
              (∃ hS : ((CochainComplex.single₀ (Modules A)).obj
                  (M.invariants.functor.obj
                    ((Profinite.CondensedAction.trivial
                      (R := A.toMon) (P := G)).obj N))).homology 0 ≅
                    M.invariants.functor.obj
                        ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N),
                ((CochainComplex.single₀ (Modules A)).obj
                    (M.invariants.functor.obj
                      ((Profinite.CondensedAction.trivial
                      (R := A.toMon) (P := G)).obj N))).homologyπ 0 ≫
                    hS.hom =
                  ((CochainComplex.single₀ (Modules A)).obj
                    (M.invariants.functor.obj
                      ((Profinite.CondensedAction.trivial
                      (R := A.toMon) (P := G)).obj N))).iCycles 0 ∧
                HomologicalComplex.homologyMap
                    ((HomologicalComplex.singleMapHomologicalComplex
                        M.invariants.functor (.up ℕ) 0).inv.app
                      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj N) ≫
                      (M.invariants.functor.mapHomologicalComplex (.up ℕ)).map I.ι) 0 ≫ hV.hom =
                  hS.hom))))) := by
  sorry

end CategoryTheory.CondensedBar
