/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits

/-!
# Naturality of the locally free Ext comparison

Source: Weil conjectures blueprint, `thm-sc-p1-duality`, proof, Step 1
(blueprint: lem-sc-p1-ext-locally-free-naturality).
-/

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of extensions corresponds to the map induced by the dual tensor morphism.
Source: blueprint `thm-sc-p1-duality`, proof, Step 1.
Proof: first-variable evaluation naturality identifies precomposition with dual tensor
(lem-sc-ext-evaluation-first-naturality). Compute Ext using an injective resolution of G
(lem-weil-pbc-ext-via-injective-resolution); precomposition acts on each cochain. Evaluation
identifies this with Gamma of dual tensor, and the derived-composite naturality square
(lem-sc-ext-derived-composite-natural) identifies the resulting map with H of dual tensor.
Compose these squares with the canonical comparison of lem-sc-ext-locally-free.
(blueprint: lem-sc-p1-ext-locally-free-naturality). -/
theorem locallyFreeExtAddEquivH_naturality {X : Scheme.{v}} [HasExt.{v} X.Modules]
    (F F' G : X.Modules) [F.IsFiniteLocallyFree] [F'.IsFiniteLocallyFree]
    (f : F' ⟶ F) (i : ℕ) (z : Ext F G i) :
    locallyFreeExtAddEquivH F' G i ((Abelian.Ext.mk₀ f).comp z (Nat.zero_add i)) =
      H.map (dualMap f ▷ G) i (locallyFreeExtAddEquivH F G i z) := sorry

/-- On the standard projective-line cover, the Ext pullback is multiplication on Cech
cochains, with the canonical sheaf identified with O(-2) by lem-sc-p1-monomial(iii).
Source: blueprint `thm-sc-p1-duality`, proof, Step 1.
Proof: write the section locally as sigma times the chosen generator. Its transpose sends
that generator's dual to sigma, so dual tensor followed by the unit identification sends
phi tensor tau to sigma times tau. On the affine standard cover the source and target are
quasi-coherent, so lem-pc-cech-computes identifies their Cech and sheaf cohomology. The
comparison is natural (lem-sc-cech-comparison-natural); its square, combined with
locallyFreeExtAddEquivH_naturality, is the displayed equality. The local scalar formula
holds on each chart and their overlap, hence componentwise on Cech cochains. The basis of
H1(omega) and omega = O(-2) are those of lem-sc-p1-monomial(ii),(iii).
The natural comparison is recorded on the full subcategory of affine-acyclic sheaves, as
in the existing proof of lem-pc-cech-computes; any such natural comparison gives the same
transported map. `E` records the generating sections of def-sc-p1-standard.
(blueprint: lem-sc-p1-ext-locally-free-naturality). -/
theorem p1_ext_pullback_cech_multiplication (k : Type v) [Field k] [IsAlgClosed k]
    (d : ℤ) :
    let X : Scheme.{v} := ProjectiveLine (Spec (.of k))
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    letI : IsGrothendieckAbelian.{v} X.Modules := isGrothendieckAbelian X
    let L : X.Modules := ProjectiveSpace.twist (ULift.{v} (Fin 2)) (Spec (.of k)) d
    letI : HasExt.{v} X.Modules :=
      IsGrothendieckAbelian.hasExt X.Modules
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI : O.IsInvertible := isInvertible_tensorUnit (X := X)
    letI : O.IsFiniteLocallyFree :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree O
        (h := IsInvertible.sheafOfModules_isInvertible O)
    let ω : X.Modules := (X ↘ Spec (.of k)).relativeDifferentials
    letI : ω.IsInvertible := IsInvertible.of_iso (X := X)
      (Classical.choice (ProjectiveLine.nonempty_relativeDifferentials_iso_twist k)).symm
    let U := ProjectiveSpace.standardOpen (ULift.{v} (Fin 2)) (Spec (.of k))
    let P := cechAcyclicOnAffines X
    let A : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
      SheafOfModules.toSheaf X.ringCatSheaf
    let unitMap : (dual (X := X) O) ⊗ ω ⟶ ω :=
      (((λ_ (dual (X := X) O)).inv ≫ dualEvaluation (X := X) O) ▷ ω) ≫ (λ_ ω).hom
    ∀ (E : ProjectiveLine.TwistData (Spec (.of k)) d L) (s : O ⟶ L),
      let m := (dualMap (X := X) s ▷ ω) ≫ unitMap
      ∃ (hM : P (A.obj ((dual (X := X) L) ⊗ ω))) (hω : P (A.obj ω))
        (e : P.ι ⋙ TopCat.Sheaf.cechCohomologyFunctor U 1 ≅
          P.ι ⋙ CategoryTheory.Sheaf.functorH.{v} (Opens.grothendieckTopology X) 1),
        (∀ z : Ext L ω 1,
          (e.app ⟨A.obj ω, hω⟩).hom
            ((TopCat.Sheaf.cechCohomologyFunctor U 1).map (A.map m)
              ((e.app ⟨A.obj ((dual (X := X) L) ⊗ ω), hM⟩).inv
                (locallyFreeExtAddEquivH (X := X) L ω 1 z))) =
            H.map unitMap 1
              (locallyFreeExtAddEquivH (X := X) O ω 1
                ((Abelian.Ext.mk₀ s).comp z (Nat.zero_add 1)))) ∧
        (∀ (p : ℕ) (c : TopCat.Presheaf.CechCochain U (A.obj ((dual (X := X) L) ⊗ ω)).obj p)
          (y : Fin (p + 1) → ULift.{v} (Fin 2)) (j : Fin 2),
          let V := ⨅ l, U (y l)
          ∀ (hV : V ≤ U ⟨j⟩) (φ : Γ((dual (X := X) L), V)) (τ : Γ(ω, V)) (σ : Γ(X, V)),
            let g := match j, hV with
              | 0, hV => L.presheaf.map (homOfLE hV).op E.g₀
              | 1, hV => L.presheaf.map (homOfLE hV).op E.g₁
            s.app V (unitSectionsEquiv V 1) = σ • g →
            (φ.app (op (Over.mk (𝟙 V)))).hom g = unitSectionsEquiv V 1 →
            c y = tmulSection φ τ →
            ((TopCat.Presheaf.cechComplex U).map (A.map m).hom).f p c y = σ • τ) := sorry

end AlgebraicGeometry.Scheme.Modules
