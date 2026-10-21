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
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.Algebra.Homology.SliceModuleSheafification
import Sheaf.Algebra.Homology.SliceTensorNatural
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor

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
3. Choose ordered bounds for the selected complexes, choosing [0,0] for the zero complex.
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
  sorry

end AlgebraicGeometry.Scheme
