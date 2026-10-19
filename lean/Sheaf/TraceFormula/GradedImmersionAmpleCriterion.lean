/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.TraceFormula.SpaceLineModuleProjMap
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import Sheaf.AlgebraicGeometry.ProjCanonicalMapTwistComparison
import Sheaf.TraceFormula.ProjQcOpenTwistAmple
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.AmpleRestrictClosedImmersion

/-!
# Graded immersion criterion for ampleness

Source: Stacks Project, Morphisms, Tag 01VJ, implication (6) implies (1), with
Constructions, Tag 01O9 (blueprint: lem-trf-graded-immersion-ample-criterion).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A graded algebra map on affine base opens into tensor powers of an invertible module.
Source: Stacks Project, Constructions, Tag 01O9 (blueprint:
lem-trf-graded-immersion-ample-criterion). -/
structure RelativeGradedLineMap {Z S : Scheme.{u}} (h : Z ⟶ S)
    (A : S.GradedAlgebraData) (L : Z.Modules) where
  component (V : S.affineOpens) (n : ℕ) :
    A.grading V n →+ Γ(L.tensorPow n, h ⁻¹ᵁ V.1)
  smul (V : S.affineOpens) (n : ℕ) (r : Γ(S, V.1)) (a : A.grading V n) :
    component V n (r • a) = h.app V.1 r • component V n a
  one (V : S.affineOpens) :
    component V 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩ =
      unitSectionsEquiv (h ⁻¹ᵁ V.1) 1
  mul (V : S.affineOpens) (m n : ℕ) (a : A.grading V m) (b : A.grading V n) :
    component V (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      (L.tensorPowAddIso m n).inv.app (h ⁻¹ᵁ V.1)
        (tmulSection (component V m a) (component V n b))
  restriction {V W : S.affineOpens} (q : V ≤ W) (n : ℕ) (a : A.grading W n) :
    component V n ⟨A.res q a, (A.res q).map_mem a.property⟩ =
      (L.tensorPow n).val.map (homOfLE (h.preimage_mono q)).op (component W n a)

/-- Pull the component of a graded line map to a scheme chart.
Source: Stacks Project, Constructions, Tag 01O9 (blueprint:
lem-trf-graded-immersion-ample-criterion). -/
noncomputable def RelativeGradedLineMap.evaluate
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {W : Scheme.{u}} (j : W ⟶ Z)
    (V : S.affineOpens) (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (n : ℕ) (a : A.grading V n) :
    Γ(((tensorPullback j).obj L).tensorPow n, ⊤) :=
  (boundaryPullbackPowIso j L n).hom.app ⊤
    (((tensorPullback j).obj (L.tensorPow n)).val.map (homOfLE q).op
      (((tensorPullbackSectionAdjunction j).unit.app (L.tensorPow n)).app (h ⁻¹ᵁ V.1)
        (ψ.component V n a)))

/-- Positive-degree images generate the line module everywhere.
Source: Stacks Project, Constructions, Tag 01O9 (blueprint:
lem-trf-graded-immersion-ample-criterion). -/
def RelativeGradedLineMap.GeneratesEverywhere
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) : Prop :=
  ∀ x : Z, ∃ (V : S.affineOpens) (hx : x ∈ h ⁻¹ᵁ V.1) (n : ℕ), 0 < n ∧
    ∃ a : A.grading V n,
      (TopCat.Presheaf.germ (L.tensorPow n).val.presheaf (h ⁻¹ᵁ V.1) x hx)
          (ψ.component V n a) ∉
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk x)) •
          (⊤ : Submodule (Z.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk (L.tensorPow n).val.presheaf x))

/-- The usual homogeneous-fraction characterization of the canonical map to relative Proj.
Source: Stacks Project, Constructions, Tag 01O9 (blueprint:
lem-trf-graded-immersion-ample-criterion). -/
def RelativeGradedLineMap.IsCanonicalMap
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) (r : Z ⟶ A.relProj) : Prop :=
  r ≫ A.relProjHom = h ∧
    ∀ (W : Scheme.{u}) (j : W ⟶ Z), IsOpenImmersion j →
      ∀ (V : S.affineOpens)
        (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
        (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
        (α : A.obj V →+* Γ(W, ⊤)),
        (∀ (n : ℕ) (a : A.grading V n), α a =
          (unitSectionsEquiv ⊤).symm
            ((AlgebraicSpace.trivializedPower e n).hom.app ⊤
              (ψ.evaluate j V q n a))) →
        ∀ hα : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal = ⊤,
          j ≫ r = Proj.fromOfGlobalSections (A.grading V) α hα ≫ A.relProjι V

/-- If the positive-degree generation locus is all of `Z` and its canonical Proj map is an
immersion, the invertible module is ample over every affine open of the base.  The graded
algebra is arbitrary: it need not be generated in degree one and its degree-zero part need
not be the structure sheaf.

Source: Stacks Project, Morphisms, Tag 01VJ, implication (6) implies (1); Constructions,
Tag 01O9 (blueprint: lem-trf-graded-immersion-ample-criterion).

Proof:
1. Fix an affine open `V` of `S`, put `T = h ⁻¹ᵁ V`, `A = A(V)` and `P = Proj A`. The affine
restriction of relative Proj and of the canonical map (lem-trf-space-line-module-proj-map)
identifies `r` on `T` with the ordinary canonical map `T ⟶ P` of the graded ring map
`A → Γ_*(T, L|_T)` induced by `ψ`. Since `U(ψ) = Z` (`hgen`), the positive-degree images
generate `L|_T` at every point, so their nonvanishing opens cover `T`.
2. The map `T ⟶ P` is an immersion and `T` is quasi-compact, as `h` is quasi-compact and `V`
is affine. By lemma-nagata-immersion-shrink-to-closed-exists it factors as a closed
immersion `i : T ⟶ Y` followed by the inclusion `u : Y ⟶ P` of a quasi-compact open `Y`.
3. By lem-trf-proj-qc-open-twist-ample some `e ≥ 1` makes `O_Y(e)` invertible and ample.
By lem-trf-ample-restrict-closed-immersion, `i^* O_Y(e)` is ample on `T`; since
`u^* O_P(e) = O_Y(e)`, this is the pullback of `O_P(e)` along `T ⟶ P`.
4. Step 1 meets the hypotheses of lem-trf-proj-canonical-map-twist-comparison, so for some
`d ≥ 1` the pullback of `O_P(dk)` is isomorphic to `L|_T^(dk)` for all `k ≥ 1`; take
`k = e`. On `Y` (not on all of `P`, which fails without degree-one generation)
lem-trf-proj-qc-open-twist-ample gives `O_Y(e)^(d) ≅ O_Y(ed)`. Pullback commutes with
tensor products (def-pur-sheaf-tensor-product), so the pullback of `O_P(ed)` is
`(i^* O_Y(e))^(d)`, ample by Step 3 and lem-sc-ample-positive-tensor-power. Hence
`L|_T^(ed)` is ample.
5. As `ed > 0`, an affine nonvanishing section cover for `L|_T^(ed)` is a cover by sections
of positive powers of `L|_T`, so `L|_T` is ample by def-weil-pbc-ample-invertible-module.
This holds for every affine open `V` of `S`. Empty `Z`, empty `T`, an arbitrary degree-zero
part and generators in arbitrary positive degrees are all allowed. -/
theorem graded_immersion_ample_criterion
    {Z S : Scheme.{u}} (h : Z ⟶ S) [QuasiCompact h]
    (L : Z.Modules) [L.IsInvertible] (A : S.GradedAlgebraData)
    (ψ : RelativeGradedLineMap h A L) (hgen : ψ.GeneratesEverywhere)
    (r : Z ⟶ A.relProj) (hr : ψ.IsCanonicalMap r) [IsImmersion r] :
    ∀ (V : S.Opens), IsAffineOpen V →
      ∃ hL : ((tensorPullback (h ⁻¹ᵁ V).ι).obj L).IsInvertible,
        @IsAmple (h ⁻¹ᵁ V).toScheme
          ((tensorPullback (h ⁻¹ᵁ V).ι).obj L) hL := by
  sorry

end AlgebraicGeometry.Scheme.Modules
