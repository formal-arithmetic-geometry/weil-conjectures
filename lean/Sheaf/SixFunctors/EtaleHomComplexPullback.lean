/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingInverseImageComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Pullback comparison for ordinary étale Hom complexes

Source: Stacks Project, sites-modules.tex, Tags 0GMX, 03EL and 03EO, and
sites-cohomology.tex, Section 0A8X (blueprint: lem-sf-etale-hom-complex-pullback).
The module inverse image is the canonical module pullback of
`etaleInverseImageModulesExact`, identified by its specified adjunction.
Tensor and Hom remain the published constructions. Their local
pure-tensor formulas supply canonical comparisons at the actual small-etale universes.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- The constant commutative ring on the small étale site. Source: Stacks 0H7J
(blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable abbrev etaleHomRing (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :=
  (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj A

/-- Modules have section universe u+1, site objects u+1 and site morphisms u.
Source: the size convention and Stacks 03D2
(blueprint: lem-sf-etale-hom-complex-pullback). -/
abbrev EtaleHomModule (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (etaleHomRing X A))

/-- Unbounded cochain complexes of the node's module sheaves. Source: Stacks 0A8X
(blueprint: lem-sf-etale-hom-complex-pullback). -/
abbrev EtaleHomComplex (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :=
  CochainComplex (EtaleHomModule X A) ℤ

/-- Continuity for the named small-etale topology, the existing base-change instance
with the topology's definition unfolded. Source: Stacks, Sites 00WU
(blueprint: lem-sf-etale-hom-complex-pullback). -/
instance etaleHomBaseChange_continuous {X X' : Scheme.{u}} (g : X' ⟶ X) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      X.smallEtaleTopology X'.smallEtaleTopology :=
  Etale.isContinuous_overPullback g

/-- The canonical constant-ring map to direct image, from the inverse-image dependency.
Source: Stacks 0H7J, 03D2 (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomRingMap {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) :
    ((sheafCompose X.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (etaleHomRing X A)) ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous RingCat.{u + 1}
        X.smallEtaleTopology X'.smallEtaleTopology).obj
          ((sheafCompose X'.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (etaleHomRing X' A)) :=
  let h := etaleConstantRingInverseImageComparison X' X g A
  (sheafCompose X.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The actual direct image is a right adjoint at the small-etale universe sizes.
Source: Stacks 03D7 and the exact inverse-image proposition
(blueprint: lem-sf-etale-hom-complex-pullback).
Proof: the constant-ring comparison used in etaleHomRingMap is the gamma of the
inverse-image proposition: both send constant sections to the same constant sections,
and the sheafification universal property gives equality. That proposition supplies LM
and its adjunction to this direct image. Thus the direct image is a right adjoint. This
avoids the native presheaf construction's unnecessary same-universe site restriction. -/
theorem etaleHomPushforward_isRightAdjoint {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) :
    (SheafOfModules.pushforward.{u + 1}
      (F := MorphismProperty.Over.pullback @Etale ⊤ g) (etaleHomRingMap g A)).IsRightAdjoint := by
  sorry

attribute [instance 1100] etaleHomPushforward_isRightAdjoint

/-- The constant-coefficient module inverse image, constructed as the module pullback along
exactly the ring map of the dependency. Uniqueness of left adjoints canonically identifies
this with its LM. Source: Stacks 03D2, 03D7, 04JC
(blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomPullback {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) : EtaleHomModule X A ⥤ EtaleHomModule X' A :=
  SheafOfModules.pullback (F := MorphismProperty.Over.pullback @Etale ⊤ g)
    (etaleHomRingMap g A)

/-- Additivity of the actual module inverse image. Source: Stacks 04JC
(blueprint: lem-sf-etale-hom-complex-pullback).
Proof: the specified LM of etaleInverseImageModulesExact is additive and left adjoint to
this same pushforward along the constant-ring map. Uniqueness of left adjoints identifies
LM with the existing module pullback. Transport additivity across that natural isomorphism. -/
theorem etaleHomPullback_additive {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) : (etaleHomPullback g A).Additive := by
  sorry

attribute [instance] etaleHomPullback_additive

/-- The canonical module adjunction, uniquely identified with the dependency's adjunction.
Source: Stacks 03D7 (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable abbrev etaleHomPullbackAdjunction {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) :=
  SheafOfModules.pullbackPushforwardAdjunction
    (F := MorphismProperty.Over.pullback @Etale ⊤ g) (etaleHomRingMap g A)

/-- The inverse-image unit on sections over a base-changed étale object.
Source: Stacks 03D7 (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomUnit {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) (M : EtaleHomModule X A) (W : X.Etaleᵒᵖ)
    (x : M.val.obj W) :
    ((etaleHomPullback g A).obj M).val.obj
      ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj W) :=
  ((etaleHomPullbackAdjunction g A).unit.app M).val.app W x

/-- The ordinary tensor product, retaining the site's distinct object and Hom universes.
Source: Stacks 03EK (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable abbrev etaleHomTensor {X : Scheme.{u}} {A : CommRingCat.{u + 1}}
    (M N : EtaleHomModule X A) : EtaleHomModule X A :=
  (SheafOfModules.siteSheafTensorRight N).obj M

/-- The canonical tensor-Hom bijection with the symmetry incorporated: its local formula
is evaluation on (parameter, argument). Source: Stacks 03EO, the `tensorClosed` adjunction
(blueprint: lem-sf-etale-hom-complex-pullback).
Proof: a section of homObj U V is a module map on the slice. Evaluation is bilinear and
commutes with restriction, hence descends from sectionwise tensor to module sheafification.
Conversely curry a tensor map by restriction to each slice. Evaluation on every local
pure tensor makes these operations inverse and uniquely determines the equivalence.
This is the mixed-universe form of tensorClosed; no equality of site universes is imposed. -/
theorem etaleHomTensorEquiv_exists (X : Scheme.{u}) (A : CommRingCat.{u + 1})
    (P U V : EtaleHomModule X A) :
    ∃! e : (etaleHomTensor P U ⟶ V) ≃ (P ⟶ SheafOfModules.homObj (R := etaleHomRing X A) U V),
      ∀ (t : etaleHomTensor P U ⟶ V) (W : X.Etaleᵒᵖ)
        (x : P.val.obj W) (y : U.val.obj W),
        t.val.app W (SheafOfModules.siteSheafTensorTmul P U W x y) =
          ((e t).val.app W x).app (op (Over.mk (𝟙 W.unop))) y := by
  sorry

/-- Evaluation-normalized tensor-Hom transposition, including symmetry.
Source: Stacks 03EO (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomTensorEquiv {X : Scheme.{u}} {A : CommRingCat.{u + 1}}
    (P U V : EtaleHomModule X A) :
    (etaleHomTensor P U ⟶ V) ≃ (P ⟶ SheafOfModules.homObj (R := etaleHomRing X A) U V) :=
  (etaleHomTensorEquiv_exists X A P U V).choose

/-- Evaluation, the inverse transpose of the identity. Source: Stacks 03EO
(blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomEval {X : Scheme.{u}} {A : CommRingCat.{u + 1}}
    (U V : EtaleHomModule X A) :
    etaleHomTensor (SheafOfModules.homObj (R := etaleHomRing X A) U V) U ⟶ V :=
  (etaleHomTensorEquiv (SheafOfModules.homObj (R := etaleHomRing X A) U V) U V).symm (𝟙 _)

/-- The canonical ordinary tensor pullback comparison, pinned by its unit/pure-tensor
formula. Source: Stacks 03EL (`module_pullback_tensor_iso`)
(blueprint: lem-sf-etale-hom-complex-pullback).
Proof: the inverse-image adjunction identifies bilinear maps before and after pullback.
Apply the sheaf tensor universal property in both directions. On inverse images of local
pure tensors this sends x tensor y to unit(x) tensor unit(y). These locally generate the
pullback tensor sheaf, so the formula determines the comparison uniquely; the two maps
are inverse by the same formula. This argument retains site objects u+1 and morphisms u. -/
theorem etaleHomTensorPullback_exists {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) (U V : EtaleHomModule X A) :
    ∃! t : (etaleHomPullback g A).obj (etaleHomTensor U V) ≅
        etaleHomTensor ((etaleHomPullback g A).obj U) ((etaleHomPullback g A).obj V),
      ∀ (W : X.Etaleᵒᵖ) (x : U.val.obj W) (y : V.val.obj W),
        t.hom.val.app ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj W)
            (etaleHomUnit g A _ W (SheafOfModules.siteSheafTensorTmul U V W x y)) =
          SheafOfModules.siteSheafTensorTmul _ _ _
            (etaleHomUnit g A U W x) (etaleHomUnit g A V W y) := by
  sorry

/-- The normalized tensor comparison; uniqueness rules out an arbitrary tensor isomorphism.
Source: Stacks 03EL (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomTensorPullback {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) (U V : EtaleHomModule X A) :=
  (etaleHomTensorPullback_exists g A U V).choose

/-- The canonical q is the transpose of pullback of evaluation after the inverse tensor
comparison. Source: Stacks 0GMX (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomPullbackComparison {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) (U V : EtaleHomModule X A) :
    (etaleHomPullback g A).obj (SheafOfModules.homObj (R := etaleHomRing X A) U V) ⟶
      SheafOfModules.homObj (R := etaleHomRing X' A)
        ((etaleHomPullback g A).obj U) ((etaleHomPullback g A).obj V) :=
  etaleHomTensorEquiv _ _ _
    ((etaleHomTensorPullback g A (SheafOfModules.homObj (R := etaleHomRing X A) U V) U).inv ≫
      (etaleHomPullback g A).map (etaleHomEval U V))

/-- Product projection of the published Hom complex. Source: Stacks 0A8X
(blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def homProjection {X : Scheme.{u}} {A : CommRingCat.{u + 1}}
    (E I : EtaleHomComplex X A) (n p q : ℤ) (hpq : p + n = q) :
    (homComplex (R := etaleHomRing X A) E I).X n ⟶
      SheafOfModules.homObj (R := etaleHomRing X A) (E.X p) (I.X q) :=
  (homComplex_projections_exists (R := etaleHomRing X A)).choose E I n p q hpq

/-- Evaluation of the p-component of a degree-n family, using the existing tensor map.
Source: Stacks 0A8X and 03EO (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomDegreeEval {X : Scheme.{u}} {A : CommRingCat.{u + 1}}
    (E I : EtaleHomComplex X A) (n p q : ℤ) (hpq : p + n = q) :
    etaleHomTensor ((homComplex (R := etaleHomRing X A) E I).X n) (E.X p) ⟶ I.X q :=
  (SheafOfModules.siteSheafTensorRight (E.X p)).map (homProjection E I n p q hpq) ≫
    etaleHomEval (E.X p) (I.X q)

/-- Unique chain comparison with the canonical q-components. Source: Stacks 0GMX, 0A8X
(blueprint: lem-sf-etale-hom-complex-pullback).
Proof: use the target product universal property degreewise with components F(projection)
followed by the evaluation transpose q. Naturality of evaluation and of the tensor comparison
makes q commute with pre- and postcomposition. The two summands of the Hom differential
therefore commute with these components, using additivity for the sign. Target projections
detect the chain identity and uniqueness. No preservation of infinite products is used. -/
theorem homComplexPullbackComparison_exists {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) (E I : EtaleHomComplex X A) :
    ∃! c : ((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homComplex (R := etaleHomRing X A) E I) ⟶
      homComplex (R := etaleHomRing X' A)
        (((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
        (((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
      ∀ (n p q : ℤ) (hpq : p + n = q),
        c.f n ≫ homProjection _ _ n p q hpq =
          (etaleHomPullback g A).map (homProjection E I n p q hpq) ≫
            etaleHomPullbackComparison g A (E.X p) (I.X q) := by
  sorry

/-- Canonical chain map, determined uniquely by all product components.
Source: Stacks 0GMX, 0A8X (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def homComplexPullbackComparison {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) (E I : EtaleHomComplex X A) :=
  (homComplexPullbackComparison_exists g A E I).choose

/-- The signed source-shift isomorphism is fixed by the reindexing formula.
Source: Stacks 0A8X and the node's signed shift computation
(blueprint: lem-sf-etale-hom-complex-pullback).
Proof: lift the displayed components into the target product; the inverse reindexes by +m
with the same sign. The two composites are identities since the signs square to one.
Project the chain identity: the ratio of the signs in consecutive degrees is (-1)^m,
which matches the shifted differential, while the two precomposition signs also agree.
Thus this is a chain isomorphism. Product projections determine it uniquely. -/
theorem etaleHomSourceShift_exists (X : Scheme.{u}) (A : CommRingCat.{u + 1})
    (E I : EtaleHomComplex X A) (m : ℤ) :
    ∃! s : homComplex (R := etaleHomRing X A) (E⟦m⟧) I ≅
        (homComplex (R := etaleHomRing X A) E I)⟦-m⟧,
      ∀ (n p q : ℤ) (hpq : p + (n - m) = q),
        s.hom.f n ≫ homProjection E I (n - m) p q hpq =
          (m * n).negOnePow •
            (homProjection (E⟦m⟧) I n (p - m) q (by omega) ≫
              SheafOfModules.homObjMap (R := etaleHomRing X A)
                (E.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 (I.X q))) := by
  sorry

/-- The actual signed s, with its unique degreewise formula, on either scheme.
Source: Stacks 0A8X (blueprint: lem-sf-etale-hom-complex-pullback). -/
noncomputable def etaleHomSourceShift {X : Scheme.{u}} {A : CommRingCat.{u + 1}}
    (E I : EtaleHomComplex X A) (m : ℤ) :=
  (etaleHomSourceShift_exists X A E I m).choose

/-- Componentwise evaluation, two-variable naturality and the signed source-shift square.
Source: Stacks 0GMX, 03EL, 03EO and 0A8X
(blueprint: lem-sf-etale-hom-complex-pullback).
Proof: (1) the unique comparison's projections are F(pi) followed by q, the transpose of
F(evaluation) after the inverse tensor comparison. Naturality of tensor comparison moves
F(pi) inside that transpose and gives the displayed evaluation of the degree-n family.
(2) For a and b, project both paths to each sheaf Hom; naturality of evaluation identifies
both with q F([a,b] pi). Product projections imply equality of chain maps.
(3) Identify termwise pullback and shifts by mapCochainComplexShiftIso. In degree n and
component p, both paths are (-1)^(m*n) q F(pi at p-m). Additivity moves the sign through F.
The signed source shifts have already absorbed the differential sign. No boundedness,
flatness, injectivity, product preservation or invertibility of c is asserted. -/
theorem etaleHomComplexPullback {X X' : Scheme.{u}} (g : X' ⟶ X)
    (A : CommRingCat.{u + 1}) (E I : EtaleHomComplex X A) :
    (∀ (n p q : ℤ) (hpq : p + n = q),
      (homComplexPullbackComparison g A E I).f n ≫ homProjection _ _ n p q hpq =
        etaleHomTensorEquiv _ _ _
          ((etaleHomTensorPullback g A
              ((homComplex (R := etaleHomRing X A) E I).X n) (E.X p)).inv ≫
            (etaleHomPullback g A).map (etaleHomDegreeEval E I n p q hpq))) ∧
    (∀ (E₁ E₂ I₁ I₂ : EtaleHomComplex X A) (a : E₁ ⟶ E₂) (b : I₁ ⟶ I₂),
      ((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((homComplexFunctor (R := etaleHomRing X A)).map a.op).app I₁ ≫
            ((homComplexFunctor (R := etaleHomRing X A)).obj (op E₁)).map b) ≫
          homComplexPullbackComparison g A E₁ I₂ =
        homComplexPullbackComparison g A E₂ I₁ ≫
          ((homComplexFunctor (R := etaleHomRing X' A)).map
            (((etaleHomPullback g A).mapHomologicalComplex
              (ComplexShape.up ℤ)).map a).op).app
                (((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I₁) ≫
          ((homComplexFunctor (R := etaleHomRing X' A)).obj
            (op (((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).obj E₁))).map
              (((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).map b)) ∧
    (∀ m : ℤ,
      homComplexPullbackComparison g A (E⟦m⟧) I ≫
          ((homComplexFunctor (R := etaleHomRing X' A)).map
            (((etaleHomPullback g A).mapCochainComplexShiftIso m).inv.app E).op).app
              (((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          (etaleHomSourceShift
            (((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
            (((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) m).hom =
        ((etaleHomPullback g A).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (etaleHomSourceShift E I m).hom ≫
          ((etaleHomPullback g A).mapCochainComplexShiftIso (-m)).hom.app
            (homComplex (R := etaleHomRing X A) E I) ≫
          (shiftFunctor _ (-m)).map (homComplexPullbackComparison g A E I)) := by
  sorry

end CategoryTheory
