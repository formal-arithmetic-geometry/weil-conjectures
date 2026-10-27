/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.SixFunctors.ScalarSixDirectImage
public import Sheaf.Paper.ProEtaleProperOpenInterchange
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Sheaf.SixFunctors.ScalarSixPullback
import Sheaf.SixFunctors.ScalarSixCtf
import Sheaf.SixFunctors.CtfStabilityDirectImages

/-! # Coefficient pasting on a fixed composite compactification

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Composition paragraph.
(blueprint: lem-sfb-scalar-composite-model-pasting).

The interchange families are specified by the published identity-on-restriction
normalization. Uniqueness in properOpenInterchange makes this a specification of the
canonical arrows. The compositor includes the actual proper and open compositors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The fixed compactification model Rp_* j_! on ordinary unbounded module categories.
Source: blueprint compact-support Composition paragraph
(blueprint: lem-sfb-scalar-composite-model-pasting). -/
def sfbScalarCompactModel (Λ : ScalarSixRing.{u}) {X B Y : Scheme.{u}}
    (j : X ⟶ B) [IsOpenImmersion j] (p : B ⟶ Y) :=
  (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙ RootCoordinateFace.lower Λ.X p

/-- The specified model comparison C = Rp_* delta after gamma, without flatness.
Source: blueprint compact-support comparison and Composition paragraph
(blueprint: lem-sfb-scalar-composite-model-pasting). -/
def sfbScalarCompactComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X B Y : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] (p : B ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a Y).obj ((sfbScalarCompactModel Λ j p).obj K) ⟶
      (sfbScalarCompactModel Λ' j p).obj ((scalarSixChange a X).obj K) :=
  (scalarDirectImageMate a p).app
      ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) ≫
    (RootCoordinateFace.lower Λ'.X p).map
      ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom.app K)

/-- The canonical composition of exact open extensions, conjugate to pullback composition.
Source: blueprint compact-support Composition paragraph, open composition identification
(blueprint: lem-sfb-scalar-composite-model-pasting). -/
def sfbScalarOpenComp (Λ : ScalarSixRing.{u}) {X B W : Scheme.{u}}
    (j : X ⟶ B) (l : B ⟶ W) [IsOpenImmersion j] [IsOpenImmersion l] :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ.X l).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ.X (j ≫ l)).mapDerivedCategory :=
  Adjunction.leftAdjointCompIso
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X l)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (j ≫ l))
    (RootCoordinateFace.upperComp Λ.X j l).symm

/-- Rq_* of the normalized interchange, followed by proper and open composition.
Source: blueprint compact-support Composition paragraph, the fixed-model alpha
(blueprint: lem-sfb-scalar-composite-model-pasting). -/
def sfbScalarModelCompositor (Λ : ScalarSixRing.{u})
    {X B Y C S : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (p : B ⟶ Y) (i : Y ⟶ C) [IsOpenImmersion i] (q : C ⟶ S)
    (c : Compactification.BoundaryCompactification (p ≫ i))
    (ι : RootCoordinateFace.lower Λ.X p ⋙
        (openImmersionLowerShriek Λ.X i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ.X c.obj.obj.g)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (sfbScalarCompactModel Λ i q).obj ((sfbScalarCompactModel Λ j p).obj K) ⟶
      (sfbScalarCompactModel Λ (j ≫ c.obj.obj.i) (c.obj.obj.g ≫ q)).obj K :=
  (RootCoordinateFace.lower Λ.X q).map
      (ι.app ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K)) ≫
    (RootCoordinateFace.lowerComp Λ.X c.obj.obj.g q).inv.app
      ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K)) ≫
    (RootCoordinateFace.lower Λ.X (c.obj.obj.g ≫ q)).map
      ((sfbScalarOpenComp Λ j c.obj.obj.i).hom.app K)

/-- The coefficient comparison commutes with the compositor on these fixed models.
The two normalized natural transformations denote the unique identity-on-Y interchange
arrows of det-sf-comp-composition-interchange, over the two coefficient rings.

Source: blueprint latest, compact-support proof, Composition paragraph
(blueprint: lem-sfb-scalar-composite-model-pasting).

Proof:
1. Put J = j_!, I = i_!, L = j'_!, P = Rp_*, Q = Rq_*, R = Rr_*.
By det-thm-sf-ctf-stability-direct-images (2), JK lies in Dctf. The same theorem's
clauses (2),(3) and det-prop-scalar-six-ctf (3) put the outputs in Dctf. Transport
along the proper/open compositors in sfbScalarModelCompositor, so alpha becomes Q iota.
2. Expand gamma for qr by det-prop-scalar-six-direct-image (2), and delta for j'j
by det-prop-scalar-six-pullback (2). The left side becomes
Q'(R'L'(d) R'(delta_j') gamma_r) gamma_q TQ(iota), with d = delta_j at K.
3. Naturality of gamma_q at iota moves TQ(iota) inside Q', immediately after gamma_r.
4. Apply lem-sfb-scalar-proper-open-interchange-square to JK: replace
R'(delta_j') gamma_r T(iota) with iota_T I'(gamma_p) delta_i.
Its proper, quasi-compact open and dense compactification hypotheses are precisely these.
5. Naturality of the primed interchange at d moves R'L'(d) through iota_T.
Regroup using functoriality of Q': the factors are alpha at TK, H'_g(C_f), and C_g.
Finally sk-def-sfb-constructible defines Dctf as a full subcategory, so this ambient
morphism equality is exactly the asserted equality in Dctf, without changing models. -/
theorem scalarCompositeModelPasting
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X B Y C S : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (j : X ⟶ B) (p : B ⟶ Y) (i : Y ⟶ C) (q : C ⟶ S)
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsProper p.left]
    [IsOpenImmersion i.left] [QuasiCompact i.left] [IsProper q.left]
    (c : Compactification.BoundaryCompactification (p.left ≫ i.left))
    [c.obj.obj.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))]
    [IsSeparated (c.obj.obj.Z ↘ Spec (.of k))]
    [c.obj.obj.i.IsOver (Spec (.of k))] [c.obj.obj.g.IsOver (Spec (.of k))]
    [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (ι : RootCoordinateFace.lower Λ.X p.left ⋙
        (openImmersionLowerShriek Λ.X i.left).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ.X c.obj.obj.g)
    (_hι : ∀ A, compositionInterchangeIsNormalized Λ.X p.left i.left c A (ι.app A))
    (ι' : RootCoordinateFace.lower Λ'.X p.left ⋙
        (openImmersionLowerShriek Λ'.X i.left).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ'.X c.obj.obj.g)
    (_hι' : ∀ A, compositionInterchangeIsNormalized Λ'.X p.left i.left c A (ι'.app A))
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (scalarSixChange a S.left).map
        (sfbScalarModelCompositor Λ j.left p.left i.left q.left c ι K.obj) ≫
      sfbScalarCompactComparison a (j.left ≫ c.obj.obj.i) (c.obj.obj.g ≫ q.left) K.obj =
    sfbScalarCompactComparison a i.left q.left
        ((sfbScalarCompactModel Λ j.left p.left).obj K.obj) ≫
      (sfbScalarCompactModel Λ' i.left q.left).map
        (sfbScalarCompactComparison a j.left p.left K.obj) ≫
      sfbScalarModelCompositor Λ' j.left p.left i.left q.left c ι'
        ((scalarSixChange a X.left).obj K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
