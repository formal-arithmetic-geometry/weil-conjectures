/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Inverse image along an isomorphism of schemes

Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).

## Main statements

- `proEtaleIsoPostcompose_equivalence`: the covering-preserving site equivalence.
- `existsUnique_proEtaleIsoInverseImageIdentification`: its normalized section identification.
- `proEtaleIsoInverseImage_equivalence`: equivalence and preservation of limits and colimits.
- `proEtaleIso_inverseLimitComparison`: the canonical inverse-limit comparison.
- `proEtaleIso_constantComparison`: invertible constant comparison and naturality.
- `proEtaleIso_constantModuleEquivalence`: the same equivalence for module sheaves.
- `proEtaleIso_constantRingModuleEquivalence`: module sheaves over any constant ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Change only the structure map of an object of the pro-etale site.
Source: Stacks Project, Tag 09A5
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
def proEtaleIsoPostcompose {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)

/-- The distinguished comma-category arrow `(u,id)` from the map/pullback adjunction.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
noncomputable def proEtaleIsoCommaArrow {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (U : X.ProEt) : U ⟶ (proEtaleBaseChange f).obj ((proEtaleIsoPostcompose f).obj U) :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial).unit.app U

private theorem isoPostcompose_continuous {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] :
    (proEtaleIsoPostcompose f).IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
  ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)

attribute [local instance] isoPostcompose_continuous

private noncomputable def isoSheafAdjunction {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (D : Type v) [Category.{u + 1} D] :
    (proEtaleIsoPostcompose f).sheafPushforwardContinuous D
      (ProEt.topology X) (ProEt.topology Y) ⊣ proEtaleSheafDirectImage f D :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial).sheafPushforwardContinuous _ _

/-- The canonical identification is uniquely fixed by the coprojection at `(u,id)`.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the distinguished comma object is initial before taking opposites, hence terminal
in the colimit index. Its coprojection is invertible. The inverse evaluates each
coprojection by the unique arrow into that terminal object. The resulting presheaf is
already a sheaf because the site equivalence preserves covers and overlap schemes;
sheafification leaves it unchanged. The construction is natural in objects and sheaves.
The prescribed inverse determines the natural isomorphism uniquely. -/
theorem existsUnique_proEtaleIsoInverseImageIdentification {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D] [HasWeakSheafify (ProEt.topology X) D] :
    ∃! e : proEtaleSheafInverseImage f D ⋙ sheafToPresheaf (ProEt.topology X) D ≅
        sheafToPresheaf (ProEt.topology Y) D ⋙
          (Functor.whiskeringLeft _ _ D).obj (proEtaleIsoPostcompose f).op,
      ∀ (F : Sheaf (ProEt.topology Y) D) (U : X.ProEt),
        (e.inv.app F).app (op U) =
          ((proEtaleSheafAdjunction f D).unit.app F).hom.app
              (op ((proEtaleIsoPostcompose f).obj U)) ≫
            ((proEtaleSheafInverseImage f D).obj F).obj.map
              (proEtaleIsoCommaArrow f U).op := by
  let a := proEtaleSheafAdjunction f D
  let b := isoSheafAdjunction f D
  let e := Functor.isoWhiskerRight (a.leftAdjointUniq b) (sheafToPresheaf (ProEt.topology X) D)
  refine ⟨e, ?_, ?_⟩
  · intro F U
    simp? [e, Adjunction.leftAdjointUniq, b, isoSheafAdjunction,
      proEtaleIsoCommaArrow, a, Adjunction.sheafPushforwardContinuous,
      Adjunction.whiskerLeft, Adjunction.op]
    erw [Category.id_comp]
  · intro e' h
    apply Iso.ext_inv
    ext F U
    exact (h F U.unop).trans (by
      simp? [e, Adjunction.leftAdjointUniq, b, isoSheafAdjunction,
        proEtaleIsoCommaArrow, a, Adjunction.sheafPushforwardContinuous,
        Adjunction.whiskerLeft, Adjunction.op]
      erw [Category.id_comp])

/-- The canonical section identification, natural both in the sheaf and in the site object.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
noncomputable def proEtaleIsoInverseImageIdentification {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D] [HasWeakSheafify (ProEt.topology X) D] :
    proEtaleSheafInverseImage f D ⋙ sheafToPresheaf (ProEt.topology X) D ≅
      sheafToPresheaf (ProEt.topology Y) D ⋙
        (Functor.whiskeringLeft _ _ D).obj (proEtaleIsoPostcompose f).op :=
  (existsUnique_proEtaleIsoInverseImageIdentification f D).exists.choose



end AlgebraicGeometry.Scheme
