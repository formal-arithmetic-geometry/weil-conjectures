/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.FilteredCartesianFlatComplexDescent
import Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent
import Sheaf.AlgebraicGeometry.TensorPullbackFlatProperSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Noetherian approximation of tensor data

Source: Stacks Project, Tags 01ZR, 05LY, 081G, 09RF and Cohomology Lemma 30.26.7
(blueprint: lem-pc-noetherian-approximation-data).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Noetherian approximation simultaneously for a finitely presented scheme, a bounded
flat complex with proper support, and a perfect derived object.
Source: Stacks Project, Tags 01ZR, 05LY, 081G, 09RF and Cohomology Lemma 30.26.7
(blueprint: lem-pc-noetherian-approximation-data).

Proof:
1. By `thm-pd-spreading-out` (Tag 01ZM), descend the finitely presented morphism
   to a finitely presented `Xi` over a stage, with a cartesian comparison square.
2. By `lem-pc-finite-flat-proper-support-descent` (Tags 01ZR, 05LY, 081G and
   Cohomology Lemma 30.26.7), descend the finitely many terms, differentials and
   relations of `G`, their flatness over the base, and their proper supports.
   Increasing the stage gives a bounded finitely presented base-flat complex and
   an isomorphism of complexes after tensor pullback.
3. By `lem-pc-perfect-complex-descent` (Tag 09RF), increase the stage again to
   descend `E` to a perfect object, with its derived-pullback identification.
4. Filteredness gives a common later stage. Base change preserves finite presentation,
   boundedness, base-flatness, proper support, perfectness and all three identifications.
-/
theorem noetherian_approximation_data
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c)
    (X : Scheme.{u}) (f : X ⟶ Spec c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [∀ (Z : Scheme.{u}), HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {G : CochainComplex X.Modules ℤ}
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n))
    (E : schemeDerivedCategory X) (hE : X.IsPerfect E) :
    ∃ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ Spec (R.obj i)),
      LocallyOfFinitePresentation fi ∧ QuasiCompact fi ∧ QuasiSeparated fi ∧
      ∃ (hfi : LocallyOfFiniteType fi) (g : X ⟶ Xi),
        IsPullback g f fi (Spec.map (c.ι.app i)) ∧
        ∃ (Gi : CochainComplex Xi.Modules ℤ),
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Gi.X n)) ∧
          (∀ n : ℤ, (Gi.X n).IsFinitePresentation) ∧
          (∀ n : ℤ, (Gi.X n).IsFlatOver fi) ∧
          (∀ n : ℤ, @Scheme.Modules.HasSupportProperOver _ _ fi hfi (Gi.X n)) ∧
          ∃ e : ∀ n : ℤ, Scheme.Modules.tensorPullbackObj g (Gi.X n) ≅ G.X n,
            (∀ n m : ℤ, Scheme.Modules.tensorPullbackMap g (Gi.d n m) ≫ (e m).hom =
              (e n).hom ≫ G.d n m) ∧
            ∃ (Ei : schemeDerivedCategory Xi), Xi.IsPerfect Ei ∧
              Nonempty ((derivedPullback g).obj Ei ≅ E) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  let D : Iᵒᵖ ⥤ Scheme.{u} := R.op ⋙ Scheme.Spec
  let d : Cone D := Scheme.Spec.mapCone c.op
  have hd : IsLimit d := isLimitOfPreserves Scheme.Spec hc.op
  let (i : Iᵒᵖ) : CompactSpace (D.obj i) := by
    dsimp [D]
    infer_instance
  let (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by
    dsimp [D]
    infer_instance
  let (i j : Iᵒᵖ) (a : i ⟶ j) : IsAffineHom (D.map a) := by
    dsimp [D]
    infer_instance
  obtain ⟨i, Xi, fi, hfp, hqc, hqs, g, hcart⟩ :=
    Scheme.exists_isPullback_of_finitePresentation hd f
  have : LocallyOfFinitePresentation fi := hfp
  have : QuasiCompact fi := hqc
  have : QuasiSeparated fi := hqs
  obtain ⟨j, Xj, fj, hjfp, hjqc, hjqs, hjft, gj, hjcart,
      Gj, hJb, hJfp, hJflat, hJproper, eJ, heJ⟩ :=
    filtered_cartesian_flat_complex_descent R c hc X f i.unop Xi fi g hcart
      hGb hGflat hGproper
  have : LocallyOfFinitePresentation fj := hjfp
  have : QuasiCompact fj := hjqc
  have : QuasiSeparated fj := hjqs
  obtain ⟨k, a, Xk, fk, hkfp, hkqc, hkqs, hkft, p, gk, hpcart, htriangle,
      hkcart, Ek, hEk, eEk⟩ :=
    filtered_cartesian_perfect_descent R c hc X f j Xj fj gj hjcart E hE
  have : LocallyOfFiniteType fk := hkft
  let T := Scheme.Modules.tensorPullback p
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction p
  have : T.Additive := adj.left_adjoint_additive
  let Gk := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj Gj
  have hprops (n : ℤ) := by
    have : (Gj.X n).IsFinitePresentation := hJfp n
    exact tensorPullback_flat_proper_support fj fk p (Spec.map (R.map a)) hpcart
      (Gj.X n) (hJflat n) (hJproper n)
  obtain ⟨ec⟩ := Scheme.Modules.nonempty_tensorPullbackComp gk p
  let ecomp : Scheme.Modules.tensorPullback gj ≅
      Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.tensorPullback gk :=
    (eqToIso (congrArg Scheme.Modules.tensorPullback htriangle.symm)) ≪≫ ec
  let eK (n : ℤ) : Scheme.Modules.tensorPullbackObj gk (Gk.X n) ≅ G.X n :=
    (ecomp.app (Gj.X n)).symm ≪≫ eJ n
  refine ⟨k, Xk, fk, hkfp, hkqc, hkqs, hkft, gk, hkcart,
    Gk, ?_, (fun n ↦ (hprops n).1), (fun n ↦ (hprops n).2.1),
    (fun n ↦ (hprops n).2.2), eK, ?_, Ek, hEk, eEk⟩
  · obtain ⟨lo, hi, hb⟩ := hJb
    exact ⟨lo, hi, fun n hn ↦ T.map_isZero (hb n hn)⟩
  · intro n m
    change (Scheme.Modules.tensorPullback gk).map (T.map (Gj.d n m)) ≫
      ((ecomp.app (Gj.X m)).inv ≫ (eJ m).hom) =
        ((ecomp.app (Gj.X n)).inv ≫ (eJ n).hom) ≫ G.d n m
    have hn := ecomp.inv.naturality (Gj.d n m)
    change (Scheme.Modules.tensorPullback gk).map (T.map (Gj.d n m)) ≫
      (ecomp.app (Gj.X m)).inv =
        (ecomp.app (Gj.X n)).inv ≫ Scheme.Modules.tensorPullbackMap gj (Gj.d n m) at hn
    rw [← Category.assoc, hn]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ (ecomp.app (Gj.X n)).inv ≫ t) (heJ n m)

end AlgebraicGeometry
