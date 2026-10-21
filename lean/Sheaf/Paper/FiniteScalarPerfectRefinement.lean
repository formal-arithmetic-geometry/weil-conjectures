/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.FiniteAffineProEtaleRefinement
import Sheaf.Paper.ScalarPerfectFiniteFree
import Sheaf.Paper.ScalarPerfectChartRestriction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Data.Finset.Max

/-! # Finite uniform scalar-perfect models on a pro-etale refinement

Source: Stacks Project, proetale.tex, Tags 0989, 098A and 098C; sites-modules.tex,
Tags 03DH, 04IX and 0GMW; the internal-Hom stability proof, paragraphs 2--3
(blueprint: lem-sfb-finite-scalar-perfect-refinement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t r w w' i
open CategoryTheory CategoryTheory.Limits
open SheafOfModules
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace AlgebraicGeometry.Scheme
variable [UnivLE.{t + 1, r}]

/-- The original small pro-etale site remains small in any containing coefficient universe.
Source: the size convention (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
instance scalarPerfectProEtSmall (S : Scheme.{t}) :
    EssentiallySmall.{r} S.ProEt :=
  letI : UnivLE.{t, r} := UnivLE.trans.{t, t + 1, r}
  inferInstance

/-- Localizing does not require changing the chosen coefficient universe.
Source: the size convention (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
instance scalarPerfectProEtSliceSmall (S : Scheme.{t}) (U : S.ProEt) :
    EssentiallySmall.{r} (Over U) :=
  letI : UnivLE.{t, r} := UnivLE.trans.{t, t + 1, r}
  inferInstance

/-- Coefficient-sized ring sheafification on the small pro-etale site.
Source: Stacks 03CY (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
instance scalarPerfectProEtCommSheafify (S : Scheme.{t}) :
    HasSheafify (ProEt.topology S) CommRingCat.{r} :=
  letI : EssentiallySmall.{r} S.ProEt := scalarPerfectProEtSmall S
  hasSheafifyEssentiallySmallSite _ _

/-- Coefficient-sized abelian sheafification on the same site.
Source: Stacks 03CY (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
instance scalarPerfectProEtAbSheafify (S : Scheme.{t}) :
    HasSheafify (ProEt.topology S) AddCommGrpCat.{r} :=
  letI : EssentiallySmall.{r} S.ProEt := scalarPerfectProEtSmall S
  letI : HasSheafify
      ((equivSmallModel _).inverse.inducedTopology (ProEt.topology S))
      AddCommGrpCat.{r} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective criterion for the chosen coefficient size.
Source: Stacks 03CY (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
instance scalarPerfectProEtLocallyBijective (S : Scheme.{t}) :
    (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{r} :=
  letI : EssentiallySmall.{r} S.ProEt := scalarPerfectProEtSmall S
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Commutative-ring sheafification on each localized site in the coefficient universe.
Source: Stacks 03DH (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
instance scalarPerfectProEtSliceCommSheafify (S : Scheme.{t}) (U : S.ProEt) :
    HasSheafify ((ProEt.topology S).over U) CommRingCat.{r} :=
  letI : EssentiallySmall.{r} (Over U) := scalarPerfectProEtSliceSmall S U
  hasSheafifyEssentiallySmallSite _ _

/-- Abelian sheafification on every localized site, without changing either site universe.
Source: Stacks 03DH (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
instance scalarPerfectProEtSliceSheafify (S : Scheme.{t}) (U : S.ProEt) :
    HasSheafify ((ProEt.topology S).over U) AddCommGrpCat.{r} :=
  letI : EssentiallySmall.{r} (Over U) := scalarPerfectProEtSliceSmall S U
  letI : HasSheafify
      ((equivSmallModel _).inverse.inducedTopology ((ProEt.topology S).over U))
      AddCommGrpCat.{r} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective criterion on the localized site in the same coefficient size.
Source: Stacks 03DH (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
instance scalarPerfectProEtSliceLocallyBijective (S : Scheme.{t}) (U : S.ProEt) :
    ((ProEt.topology S).over U).WEqualsLocallyBijective
      AddCommGrpCat.{r} :=
  letI : EssentiallySmall.{r} (Over U) := scalarPerfectProEtSliceSmall S U
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- An open chart in a weakly etale object, viewed as an object of the same small site.
Source: Stacks 0989 (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
def scalarPerfectOpenChart {S : Scheme.{t}} (U : S.ProEt) (V : U.left.Opens) : S.ProEt :=
  ProEt.mk (V.ι ≫ U.hom)

/-- The underlying coefficient ring sheaf, in the declared independent coefficient size.
Source: Stacks 03DA (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
abbrev scalarPerfectProEtRing (S : Scheme.{t})
    (B : Sheaf (ProEt.topology S) CommRingCat.{r}) :=
  scalarPerfectRingUnderlying.{t + 1, t, r} (ProEt.topology S) B

variable (S : Scheme.{t}) (R : Type (r)) [CommRing R]
  (B : Sheaf (ProEt.topology S) CommRingCat.{r})
  (φ : scalarPerfectRing.{t + 1, t, r} (ProEt.topology S) R ⟶ B)

/-- The local termwise B|U tensor underline F model; constants are restricted before tensoring.
Source: Stacks 03DH, 03EK (blueprint: lem-sfb-finite-scalar-perfect-refinement). -/
abbrev scalarPerfectLocalModel (S : Scheme.{t}) (R : Type (r)) [CommRing R]
    (B : Sheaf (ProEt.topology S) CommRingCat.{r})
    (φ : scalarPerfectRing.{t + 1, t, r} (ProEt.topology S) R ⟶ B)
    (U : S.ProEt) (F : CochainComplex (ModuleCat.{r} R) ℤ) :=
  scalarPerfectChartComplex.{t + 1, t, r} (ProEt.topology S) R φ U F

/-- Finite affine refinement, common extremal bounds, and the specified extended splittings.
Source: Stacks proetale.tex, Tags 0989, 098A and 098C; sites-modules.tex, Tag 0GMW
(blueprint: lem-sfb-finite-scalar-perfect-refinement).

Proof plan:
1. Cover the quasi-compact S by finitely many affine opens. On each, use the finite
   affine-refinement clause of the original fpqc cover (0989), not just joint surjectivity.
2. Compose these covers using fpqc transitivity and stability of weak etaleness (098C).
   The finite union of finite sets is finite and is nonempty because S is nonempty.
   No quasi-separatedness or quasi-compactness of the original charts is used.
3. Replace the supplied endpoints by their minimum and maximum, giving ordered bounds.
   The finite nonempty set of lower and upper endpoints has an attained minimum and maximum.
4. Localize to slice sites. The constant-presheaf restriction is literally constant, and
   the continuous cocontinuous slice functor commutes with module sheafification.
   The natural tensor-restriction comparison commutes with all differentials.
5. Exact module restriction computes derived restriction termwise. Restrict the given
   representing isomorphisms and use relocalization and the comparisons in step 4.
   Terms outside the chosen intervals are B tensor zero, hence zero.
6. The map b tensor (r_k) to (b r_k) identifies scalar extension of a finite free module
   with the finite tuple sheaf; its inverse is the finite sum of b_k tensor e_k.
   The same formulas cover rank zero and require no flatness.
7. Apply constant sheafification and ordinary scalar extension to each chosen inclusion
   and projection. Functoriality carries p i = 1 to the same split identity. The resulting
   package has precisely these maps under the normalized finite-free identification.
   All choices precede any test module, and no exactness of scalar extension is used. -/
theorem finite_scalar_perfect_refinement [Nonempty S] [CompactSpace S]
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      (scalarPerfectProEtRing S B))]
    [∀ U : S.ProEt, HasDerivedCategory.{w'} (SheafOfModules.{r}
      ((scalarPerfectProEtRing S B).over U))]
    (P : DerivedCategory (SheafOfModules.{r}
      (scalarPerfectProEtRing S B)))
    (I : Type i) (U : I → S.ProEt)
    (_hcover : Presieve.ofArrows (fun k ↦ (U k).left) (fun k ↦ (U k).hom) ∈
      proetalePrecoverage.coverings S)
    (F : I → CochainComplex (ModuleCat.{r} R) ℤ)
    (_hbounded : ∀ k, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero ((F k).X q))
    (spl : ∀ k, ModuleCat.StrictPerfectCoefficientPackage (F k))
    (_hrep : ∀ k, Nonempty
      (ringedSiteDerivedRestrictionOfUniverses.{t + 1, t,
        r, r, w, w'}
        (scalarPerfectProEtRing S B) (U k) P ≅
          DerivedCategory.Q.obj (scalarPerfectLocalModel S R B φ (U k) (F k)))) :
    ∃ (n : ℕ) (_hn : 0 < n) (α : Fin n → I) (V : ∀ j, (U (α j)).left.Opens)
      (lo hi : Fin n → ℤ) (a b : ℤ),
      (∀ j, IsAffineOpen (V j)) ∧
      Presieve.ofArrows (fun j ↦ (V j).toScheme)
        (fun j ↦ (V j).ι ≫ (U (α j)).hom) ∈ proetalePrecoverage.coverings S ∧
      (∀ j, lo j ≤ hi j) ∧
      (∀ j q, q < lo j ∨ hi j < q → IsZero ((F (α j)).X q)) ∧
      (∀ j, a ≤ lo j) ∧ (∃ j, a = lo j) ∧
      (∀ j, hi j ≤ b) ∧ (∃ j, b = hi j) ∧ a ≤ b ∧
      ∀ j, Nonempty
        (ringedSiteDerivedRestrictionOfUniverses.{t + 1, t,
        r, r, w, w'}
          (scalarPerfectProEtRing S B)
          (scalarPerfectOpenChart (U (α j)) (V j)) P ≅
            DerivedCategory.Q.obj (scalarPerfectLocalModel S R B φ
              (scalarPerfectOpenChart (U (α j)) (V j)) (F (α j)))) ∧
        (∀ q, q < lo j ∨ hi j < q → IsZero
          ((scalarPerfectLocalModel S R B φ
            (scalarPerfectOpenChart (U (α j)) (V j)) (F (α j))).X q)) ∧
        ∃ pkg : StrictPerfectCoefficientPackageOnSite
          ((scalarPerfectProEtRing S B).over
            (scalarPerfectOpenChart (U (α j)) (V j)))
          (scalarPerfectLocalModel S R B φ
            (scalarPerfectOpenChart (U (α j)) (V j)) (F (α j))),
          ∃ hN : pkg.N = (spl (α j)).N,
          ∃ e : ∀ q : ℤ,
            (scalarPerfectChartFunctor.{t + 1, t, r} (ProEt.topology S) R φ
              (scalarPerfectOpenChart (U (α j)) (V j))).obj
                (ModuleCat.of R (Fin ((spl (α j)).N q) → R)) ≅
              ∏ᶜ fun _ : Fin (pkg.N q) ↦ SheafOfModules.unit
                ((scalarPerfectProEtRing S B).over
                  (scalarPerfectOpenChart (U (α j)) (V j))),
            (∀ q, pkg.i q =
              (scalarPerfectChartFunctor.{t + 1, t, r} (ProEt.topology S) R φ
                (scalarPerfectOpenChart (U (α j)) (V j))).map ((spl (α j)).i q) ≫
                  (e q).hom) ∧
            (∀ q, pkg.p q = (e q).inv ≫
              (scalarPerfectChartFunctor.{t + 1, t, r} (ProEt.topology S) R φ
                (scalarPerfectOpenChart (U (α j)) (V j))).map ((spl (α j)).p q)) ∧
            ∀ (q : ℤ) (W : (Over (scalarPerfectOpenChart (U (α j)) (V j)))ᵒᵖ)
              (s : B.obj.obj (Opposite.op W.unop.left))
              (x : Fin ((spl (α j)).N q) → R) (k : Fin (pkg.N q)),
              ((e q).hom ≫ Pi.π _ k).val.app W
                (scalarPerfectChartSection.{t + 1, t, r} (ProEt.topology S) R φ
                  (scalarPerfectOpenChart (U (α j)) (V j)) _ W s x) =
                s * φ.hom.app (Opposite.op W.unop.left)
                  ((scalarPerfectRingUnit.{t + 1, t, r} (ProEt.topology S) R).app
                    (Opposite.op W.unop.left) (x (Fin.cast (congrFun hN q) k))) := by
  classical
  obtain ⟨n, hn, α, V, hV, hcov⟩ := finite_affine_proetale_refinement S I U _hcover
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  choose l h hl using _hbounded
  let lo : Fin n → ℤ := fun j ↦ min (l (α j)) (h (α j))
  let hi : Fin n → ℤ := fun j ↦ max (l (α j)) (h (α j))
  have hlohi (j) : lo j ≤ hi j := min_le_max
  have hF (j) (q : ℤ) (hq : q < lo j ∨ hi j < q) : IsZero ((F (α j)).X q) := by
    apply hl (α j) q
    rcases hq with hq | hq
    · exact Or.inl (hq.trans_le (min_le_left _ _))
    · exact Or.inr ((le_max_right _ _).trans_lt hq)
  obtain ⟨ja, _, hja⟩ := Finset.exists_min_image Finset.univ lo Finset.univ_nonempty
  obtain ⟨jb, _, hjb⟩ := Finset.exists_max_image Finset.univ hi Finset.univ_nonempty
  refine ⟨n, hn, α, V, lo, hi, lo ja, hi jb, hV, hcov, hlohi, hF,
    (fun j ↦ hja j (Finset.mem_univ _)), ⟨ja, rfl⟩,
    (fun j ↦ hjb j (Finset.mem_univ _)), ⟨jb, rfl⟩,
    (hlohi ja).trans (hjb ja (Finset.mem_univ _)), ?_⟩
  intro j
  let W := scalarPerfectOpenChart (U (α j)) (V j)
  let G := scalarPerfectChartFunctor.{t + 1, t, r} (ProEt.topology S) R φ W
  have hC := scalarPerfectConstantFunctor_additive (ProEt.topology S) R
  have hE := scalarPerfectExtensionFunctor_additive ((ProEt.topology S).over W)
    (((ProEt.topology S).overPullback CommRingCat.{r} W).map φ)
  have hO : (overFunctor.{r}
      (scalarPerfectRingUnderlying (ProEt.topology S)
        (scalarPerfectRing (ProEt.topology S) R)) W).Additive :=
    ⟨fun {_ _} f g ↦ by ext T x; rfl⟩
  have hG : G.Additive := inferInstanceAs
    ((scalarPerfectConstantFunctor (ProEt.topology S) R ⋙
      overFunctor (scalarPerfectRingUnderlying (ProEt.topology S)
        (scalarPerfectRing (ProEt.topology S) R)) W ⋙
      scalarPerfectExtensionFunctor.{t + 1, t, r} ((ProEt.topology S).over W)
        (((ProEt.topology S).overPullback CommRingCat.{r} W).map φ)).Additive)
  have hzero (q) (hq : q < lo j ∨ hi j < q) :
      IsZero ((scalarPerfectLocalModel S R B φ W (F (α j))).X q) :=
    G.map_isZero (hF j q hq)
  have he (q : ℤ) := exists_scalarPerfectChartFiniteFreeIso
    (ProEt.topology S) R φ W ((spl (α j)).N q)
  choose e he using he
  let pkg : StrictPerfectCoefficientPackageOnSite ((scalarPerfectProEtRing S B).over W)
      (scalarPerfectLocalModel S R B φ W (F (α j))) :=
    { N := (spl (α j)).N
      i q := G.map ((spl (α j)).i q) ≫ (e q).hom
      p q := (e q).inv ≫ G.map ((spl (α j)).p q)
      splitting q := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp,
          (spl (α j)).splitting, G.map_id]
        rfl }
  refine ⟨?_, hzero, pkg, rfl, e, (fun _ ↦ rfl), (fun _ ↦ rfl), ?_⟩
  · let O := scalarPerfectProEtRing S B
    let f : W ⟶ U (α j) := MorphismProperty.Over.homMk (V j).ι rfl trivial
    let H := overMap.{r} O f
    have : H.Additive := ⟨fun {_ _} g h ↦ by ext T x; rfl⟩
    have : PreservesFiniteColimits H := inferInstance
    let T := SheafOfModules.forget.{r} (O.over W) ⋙ PresheafOfModules.toPresheaf (O.over W).obj
    have : PreservesFiniteLimits (H ⋙ T) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{r} (O.over (U (α j))) ⋙
          PresheafOfModules.toPresheaf (O.over (U (α j))).obj) ⋙
            (Functor.whiskeringLeft _ _ _).obj (Over.map f).op)
      infer_instance
    have : PreservesFiniteLimits H := preservesFiniteLimits_of_reflects_of_preserves H T
    have : (overFunctor.{r} O (U (α j))).Additive :=
      ⟨fun {_ _} g h ↦ by ext T x; rfl⟩
    have : (overFunctor.{r} O W).Additive :=
      ⟨fun {_ _} g h ↦ by ext T x; rfl⟩
    let K := DerivedCategory.Q.objPreimage P
    let ec := (Functor.mapHomologicalComplexCompIso (overFunctorMap O f) (.up ℤ)).app K
    let e₀ := (DerivedCategory.Q.mapIso ec).symm ≪≫
      (H.mapDerivedCategoryFactors.app
        (((overFunctor.{r} O (U (α j))).mapHomologicalComplex (.up ℤ)).obj K)).symm ≪≫
      H.mapDerivedCategory.mapIso (Classical.choice (_hrep (α j))) ≪≫
      H.mapDerivedCategoryFactors.app (scalarPerfectLocalModel S R B φ (U (α j)) (F (α j)))
    let G₀ := scalarPerfectChartFunctor.{t + 1, t, r} (ProEt.topology S) R φ (U (α j))
    have hO₀ : (overFunctor.{r}
        (scalarPerfectRingUnderlying (ProEt.topology S)
          (scalarPerfectRing (ProEt.topology S) R)) (U (α j))).Additive :=
      ⟨fun {_ _} g h ↦ by ext T x; rfl⟩
    have hE₀ := scalarPerfectExtensionFunctor_additive ((ProEt.topology S).over (U (α j)))
      (((ProEt.topology S).overPullback CommRingCat.{r} (U (α j))).map φ)
    have : G₀.Additive := inferInstanceAs
      ((scalarPerfectConstantFunctor (ProEt.topology S) R ⋙
        overFunctor (scalarPerfectRingUnderlying (ProEt.topology S)
          (scalarPerfectRing (ProEt.topology S) R)) (U (α j)) ⋙
        scalarPerfectExtensionFunctor.{t + 1, t, r} ((ProEt.topology S).over (U (α j)))
          (((ProEt.topology S).overPullback CommRingCat.{r} (U (α j))).map φ)).Additive)
    let e₁ := (Functor.mapHomologicalComplexCompIso
      (Classical.choice (scalarPerfectChartRestrictionIso f R φ)).symm (.up ℤ)).app (F (α j))
    exact ⟨e₀ ≪≫ DerivedCategory.Q.mapIso e₁⟩
  · intro q T b x k
    exact he q T b x k


end AlgebraicGeometry.Scheme
