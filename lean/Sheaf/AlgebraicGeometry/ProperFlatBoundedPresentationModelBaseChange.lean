/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups A2 and T2
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Sheaf.AlgebraicGeometry.AffineFlatModuleTensorFlat
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A nonzero module placed in degree -1 violates negative homology vanishing,
even after pullback along the identity. This diagnostic uses no project sorries. -/
private theorem single_negative_homology_obstruction (S : Scheme.{u}) (M : S.Modules)
    (hM : ¬ IsZero M) :
    ¬ IsZero ((((Modules.pullback (𝟙 S)).mapHomologicalComplex _).obj
      ((HomologicalComplex.single S.Modules (ComplexShape.up ℤ) (-1)).obj M)).homology
        (-1)) := by
  intro h
  let C := (HomologicalComplex.single S.Modules (ComplexShape.up ℤ) (-1)).obj M
  let e := (NatIso.mapHomologicalComplex (Modules.pullbackId S) (ComplexShape.up ℤ)).app C
    ≪≫ (Functor.mapHomologicalComplexIdIso S.Modules (ComplexShape.up ℤ)).app C
  let eH := (HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℤ) (-1)).mapIso e
    ≪≫ HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (-1) M
  exact hM (h.of_iso eH.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 1024 in
/-- A bounded flat replacement of an actual nonnegative cohomology model computes
all base changes. The quasi-isomorphism `e` connects the replacement to that model;
boundedness and termwise flatness alone would not do so.
Source: Stacks Project, Tags 06YJ and 0A1D, applied to the models of Tags 0B91 and 08EB.
(blueprint: lem-pc-proper-flat-bounded-presentation-comparison-core).

Proof: Bounded-above flat complexes are K-flat. Ordinary pullback, identified with
tensor pullback by uniqueness of left adjoints, preserves a quasi-isomorphism between
K-flat complexes. In negative degrees the pulled-back nonnegative complex has zero
terms, hence zero homology. Transport this vanishing along the induced homology
isomorphism. In nonnegative degrees compose that same homology isomorphism with
the supplied comparison for the actual cohomology model. -/
theorem proper_flat_boundedPresentation_model_baseChange
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules) (U : T.Opens)
    (C D : CochainComplex U.toScheme.Modules ℤ) (b d : ℕ)
    (hCle : C.IsStrictlyLE b) (hDge : D.IsStrictlyGE 0) (hDle : D.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hDflat : ∀ n : ℤ, (D.X n).IsFlatOver (𝟙 U.toScheme))
    (e : C ⟶ D) (he : QuasiIso e)
    (hcomp :
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj D).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F))) :
      (∀ {S : Scheme.{u}} (g : S ⟶ U.toScheme) (i : ℤ), i < 0 →
        IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology i)) ∧
      (∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F))) := by
  have : C.IsStrictlyLE (b : ℤ) := hCle
  have : D.IsStrictlyLE (d : ℤ) := hDle
  have hC : CochainComplex.IsKFlat (R := U.toScheme.sheaf) C :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace U.toScheme.toRingedSpace C
      ⟨b, fun n hn ↦ C.isZero_of_isStrictlyLE b n hn⟩
      (fun n ↦ isFlat_of_affineFlatOver_identity (C.X n) (hCflat n))
  have hD : CochainComplex.IsKFlat (R := U.toScheme.sheaf) D :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace U.toScheme.toRingedSpace D
      ⟨d, fun n hn ↦ D.isZero_of_isStrictlyLE d n hn⟩
      (fun n ↦ isFlat_of_affineFlatOver_identity (D.X n) (hDflat n))
  have hbase {S : Scheme.{u}} (g : S ⟶ U.toScheme) :
      QuasiIso (((Modules.pullback g).mapHomologicalComplex (.up ℤ)).map e) := by
    have : (tensorPullback g).Additive :=
      (Classical.choice (nonempty_tensorPullbackAdjunction g)).left_adjoint_additive
    have hq := tensorPullback_quasiIso_of_isKFlat g e hC hD he
    let eg : tensorPullback g ≅ Modules.pullback g :=
      (Classical.choice (nonempty_tensorPullbackAdjunction g)).leftAdjointUniq
        (pullbackPushforwardAdjunction g)
    let ec := NatIso.mapHomologicalComplex eg (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (ec.app C) (ec.app D) (ec.hom.naturality e).symm)).mp hq
  constructor
  · intro S g i hi
    have := hbase g
    have := hDge
    have hz : IsZero (D.X i) := D.isZero_of_isStrictlyGE 0 i hi
    have hH : IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj D).homology i) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _ ((Modules.pullback g).map_isZero hz)
    exact hH.of_iso (isoOfQuasiIsoAt
      (((Modules.pullback g).mapHomologicalComplex _).map e) i)
  · intro T' X' g g' f' _ hsquare q
    have := hbase g
    obtain ⟨eq⟩ := hcomp g g' f' hsquare q
    exact ⟨isoOfQuasiIsoAt
      (((Modules.pullback g).mapHomologicalComplex _).map e) (q : ℤ) ≪≫ eq⟩

end AlgebraicGeometry.Scheme.Modules
