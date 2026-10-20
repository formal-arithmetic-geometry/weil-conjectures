/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Constructible
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Sheaf.Paper.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism

/-! # Constructible geometric fibre dimensions of coherent cohomology

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
lem-fin-projective-flat-coherent-ranks; Stacks Project, Tags 0BDN and 0BDI
(blueprint: lem-fin-projective-flat-coherent-ranks).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem coherent_finitePresentation
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hc : RingedSpace.IsCoherent X.toRingedSpace F) : F.IsFinitePresentation := by
  have hq := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hc
  have hfp (U : X.affineOpens) : (F.over U.1).IsFinitePresentation := by
    have := IsLocallyNoetherian.component_noetherian U
    have := Scheme.Modules.coherent_affine_sections_finite X F hc U.1 U.2
    have hp := Module.finitePresentation_of_finite Γ(X, U.1) Γ(F, U.1)
    exact (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2 F hq.1).1
      U.1 U.2).2.mpr hp
  exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _ F
    X.affineOpens (fun U ↦ U.1) (by
      rw [Opens.coversTop_iff]
      exact iSup_affineOpens_eq_top X) hfp

private theorem finrank_moduleCohomology_eq_finrankH
    {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (F : Y.Modules) (r : ℕ) :
    Module.finrank k ((RingedSpace.moduleCohomology Y.toRingedSpace r ⋙
      ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).obj F) =
      (letI : Y.Over (Spec (.of k)) := ⟨g⟩; F.finrankH k r) := by
  let : Y.Over (Spec (.of k)) := ⟨g⟩
  obtain ⟨a, ha⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison Y r
  let C := (RingedSpace.moduleCohomology Y.toRingedSpace r ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).obj F
  let e : C ≃ₗ[k] F.H r :=
    { a F with
      map_smul' := fun c x ↦ by
        let b := Scheme.globalSectionsRingHom k (X := Y) c
        have hn := ha F F (F.smulHom b) x
        have hm := moduleCohomology_scalar_endomorphism F (F.smulHom b) b
          (fun U t ↦ Scheme.Modules.smulHom_app_apply F b U t) r x
        rw [hm] at hn
        exact hn }
  exact e.finrank_eq

/-- Geometric fibre coherent cohomology dimensions of a coherent module flat over a
Noetherian base of a projective morphism form a constructible function: its range is finite
and every level set is constructible. The scalar action is restricted from global functions
on the geometric fibre along its structure morphism to the algebraic closure.
Source: blueprint lem-fin-projective-flat-coherent-ranks; Stacks, Tags 0BDN and 0BDI
(blueprint: lem-fin-projective-flat-coherent-ranks).

Proof:
1. A locally Noetherian quasi-compact scheme has a Noetherian underlying space: choose
finitely many Noetherian affine charts and use lem-sc-affine-noetherian-underlying-space.
Every open is retrocompact, so finite unions of locally closed sets are constructible.
2. By lem-pc-projective-noetherian-rf-perfect the direct image is perfect. Use
 def-pc-perfect-complex and lem-weil-pbc-finite-projective-standard-free-cover to represent
it on a finite affine cover by bounded finite free complexes.
3. By cor-pc-projective-noetherian-rf-perfect-base-change, geometric fibre cohomology is
computed by the derived fibre of this model. Use lem-pc-localized-pullback-perfect-model
and def-pc-module-pullback to identify this with termwise tensoring with the algebraic
closure. Global sections on the spectrum of a field are exact; pqf-def-cohomology
identifies the resulting homology with coherent cohomology. Splitting cycles and boundaries
over the residue field shows that extending to its algebraic closure preserves dimension.
4. Apply lem-sc-finite-free-complex-homology-upper-semicontinuous on each chart. A level
set is the difference of two open sublevel sets, hence locally closed. Its dimension is
bounded by the finite rank of the term in degree r.
5. Take the finite union over the affine cover: each global level set is constructible
and only finitely many values occur. For an empty base the range is empty. -/
theorem projectiveFlatCoherent_geometricCohomology_constructible
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProjective f]
    [IsLocallyNoetherian S] [CompactSpace S]
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hflat : G.IsFlatOver f) (r : ℕ) :
    ∃ β : S → ℕ,
      (∀ s : S, β s = Module.finrank (AlgebraicClosure (S.residueField s))
        ((RingedSpace.moduleCohomology
          (pullback f
            (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
                S.fromSpecResidueField s)).toRingedSpace r ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (S.residueField s)))).inv ≫
              (pullback.snd f
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
                    S.fromSpecResidueField s)).appTop).hom).obj
          ((Scheme.Modules.tensorPullback
            (pullback.fst f
              (Spec.map (CommRingCat.ofHom
                (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
                  S.fromSpecResidueField s))).obj G))) ∧
      (Set.range β).Finite ∧
      ∀ n : ℕ, Topology.IsConstructible {s : S | β s = n} := by
  classical
  let : IsNoetherian S := ⟨⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : G.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG).1
  have : G.IsFinitePresentation := coherent_finitePresentation X G hG
  obtain ⟨n, hn, i, hi, hif⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  have : Finite n := hn
  have : IsClosedImmersion i := hi
  obtain ⟨hfinite, hcon⟩ :=
    Scheme.Modules.finite_range_and_isConstructible_finrankH_geometricFibre f i hif G hflat r
  let β : S → ℕ := fun s ↦
    letI : (pullback f (S.geometricPointAt s)).Over
        (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
    ((Scheme.Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj G).finrankH
      (AlgebraicClosure (S.residueField s)) r
  refine ⟨β, ?_, hfinite, ?_⟩
  · intro s
    let g := S.geometricPointAt s
    let Y := pullback f g
    let p : Y ⟶ X := pullback.fst f g
    let q := pullback.snd f g
    let : Y.Over (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨q⟩
    obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction p
    let e := (adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction p)).app G
    rw [finrank_moduleCohomology_eq_finrankH q]
    exact (Scheme.Modules.finrankH_congr (AlgebraicClosure (S.residueField s)) e r).symm
  · intro n
    exact hcon n

end AlgebraicGeometry
