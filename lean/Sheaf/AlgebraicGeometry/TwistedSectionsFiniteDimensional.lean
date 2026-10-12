/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import Sheaf.AlgebraicGeometry.ProjectiveLinePolynomialProjectionChartIso
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
/-! # Finiteness of twisted sections for the canonical base-field action

Source: Stacks Project, Lemma 01YS(3).
(blueprint: lem-sc-p1-twisted-sections-finite-dimensional).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- Transport finite dimensionality across a linear equivalence. -/
theorem finiteDimensional_of_linearEquiv
    {K V W : Type*} [Field K] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] (e : V ≃ₗ[K] W)
    [FiniteDimensional K W] : FiniteDimensional K V := by
  exact e.symm.finiteDimensional

/-- On a locally Noetherian scheme, a coherent module is finitely presented.
Source: Stacks Project, Tag 01XZ, implications (1) to (4) to (3).
Use finite direct image for the identity to obtain finite affine sections. Over a
Noetherian affine ring they are finitely presented, and the affine criterion and
locality of finite presentation give the assertion. -/
private theorem finitePresentation_of_coherent
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) : F.IsFinitePresentation := by
  have hq := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hq.1
  have hs := (Scheme.Modules.isCoherent_pushforward_of_isFinite (𝟙 X) F hF).2
  have (U : X.affineOpens) : (F.over U.1).IsFinitePresentation := by
    have : IsNoetherianRing Γ(X, U.1) :=
      IsLocallyNoetherian.component_noetherian U
    have : Module.Finite Γ(X, U.1) Γ(F, U.1) := hs U.1 U.2 |>.2
    exact (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2 F inferInstance).1
      U.1 U.2).2.mpr (Module.finitePresentation_of_finite Γ(X, U.1) Γ(F, U.1))
  exact SheafOfModules.IsFinitePresentation.of_coversTop F (fun U : X.affineOpens ↦ U.1)
    ((Opens.coversTop_iff X _).mpr
      (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X)))

/-- The canonical chart comparison transports twisted sections to projective-line
cohomology for the specified scalar action.
Source: Stacks Project, Lemma 01YS(3), with Tags 01XZ and 01NG.
(blueprint: lem-sc-p1-twisted-sections-transport).

Proof: the degree-one variable opens cover polynomial Proj, so every twist is
invertible, including negative twists. Proj is locally Noetherian; the coherent
module G is finitely presented. Tensoring with an invertible module preserves finite
presentation. The canonical linear projection is an isomorphism on the standard
charts, hence an isomorphism globally. Define L as its direct image of the twisted
module. A closed immersion preserves finite presentation and quasi-coherence, so
finite coherent cohomology on the projective line applies to L in degree zero.
Its degree-zero cohomology is linearly equivalent to its global sections, whose
underlying group is definitionally the original section group. The projection's
structure-map identity and naturality of ΓSpecIso show that its scalar action is
exactly restriction along ρ. The inverse of this equivalence gives the result. -/
theorem serreTwistedSectionsTransport
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (n : ℤ) :
    let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
      (Scheme.ΓSpecIso _).inv.hom).comp
        (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
    letI := Module.compHom
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) ρ
    ∃ (L : (ProjectiveLine (Spec (.of k))).Modules),
      Nonempty (Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤)
        ≃ₗ[k] L.H 0) ∧ FiniteDimensional k (L.H 0) := by
  classical
  dsimp
  let A := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let P := Proj A
  let F := G ⊗ Proj.twist A n
  let ρ := ((Proj.toSpecZero A).appTop.hom.comp (Scheme.ΓSpecIso _).inv.hom).comp
    (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
  let := Module.compHom Γ(F, ⊤) ρ
  have : IsNoetherianRing (A 0) :=
    isNoetherianRing_of_ringEquiv k (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k)
  have : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero A)
  have : G.IsFinitePresentation := finitePresentation_of_coherent P G hG
  have hcov : (⨆ i : ULift.{u} (Fin 2), Proj.basicOpen A (MvPolynomial.X i.down)) = ⊤ := by
    have h := Proj.iSup_basicOpen_eq_top' A MvPolynomial.X
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
      (MvPolynomial.adjoin_range_X_eq_top (Fin 2) k)
    refine top_le_iff.mp fun x hx ↦ ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have : (Proj.twist A n).IsInvertible := Proj.isInvertible_twist A n fun x ↦ by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
    exact ⟨MvPolynomial.X i.down, MvPolynomial.isHomogeneous_X k i.down, hi⟩
  have : F.IsFinitePresentation := Scheme.Modules.isFinitePresentation_tensorObj G _
  have : F.IsQuasicoherent := inferInstance
  let p := Proj.linearProjection A (fun j : ULift.{u} (Fin 2) ↦ MvPolynomial.X j.down)
    (fun j ↦ MvPolynomial.X_mem_homogeneousSubmodule_one k j.down) hcov
  have : IsIso p := by
    apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme) (f := p) _
      (ProjectiveSpace.iSup_standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)))).mpr
    intro i
    exact Proj.isIso_polynomial_linearProjection_restrict k hcov i
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  let L := (Scheme.Modules.pushforward p).obj F
  have : L.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom p F
  have : L.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pushforward_of_isClosedImmersion p F
  have hρ (c : k) : p.appTop
      (Scheme.globalSectionsRingHom k (X := ProjectiveLine (Spec (.of k))) c) = ρ c := by
    change ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).appTop ≫ p.appTop)
      ((Scheme.ΓSpecIso (.of k)).inv c) = _
    rw [← Scheme.Hom.comp_appTop, Proj.linearProjection_over]
    rw [Proj.toSpecBase, Scheme.Hom.comp_appTop]
    change (Proj.toSpecZero A).appTop
      ((Spec.map (CommRingCat.ofHom (algebraMap k (A 0)))).appTop
        ((Scheme.ΓSpecIso (.of k)).inv c)) = _
    have hn := congrArg (fun f ↦ f c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (A 0))))
    change (Scheme.ΓSpecIso (.of (A 0))).inv (algebraMap k (A 0) c) =
      (Spec.map (CommRingCat.ofHom (algebraMap k (A 0)))).appTop
        ((Scheme.ΓSpecIso (.of k)).inv c) at hn
    rw [← hn]
    rfl
  let e : L.H 0 ≃ₗ[k] Γ(F, ⊤) :=
    (show L.H 0 ≃+ Γ(F, ⊤) from
      (Scheme.Modules.H.zeroLinearEquiv L).toAddEquiv).toLinearEquiv fun c x ↦ by
      have h := (Scheme.Modules.H.zeroLinearEquiv L).map_smul
        (Scheme.globalSectionsRingHom k (X := ProjectiveLine (Spec (.of k))) c) x
      change Scheme.Modules.H.zeroLinearEquiv L (c • x) =
        p.appTop (Scheme.globalSectionsRingHom k c) •
          (show Γ(F, ⊤) from Scheme.Modules.H.zeroLinearEquiv L x) at h
      change Scheme.Modules.H.zeroLinearEquiv L (c • x) =
        ρ c • (show Γ(F, ⊤) from Scheme.Modules.H.zeroLinearEquiv L x)
      rw [← hρ]
      exact h
  exact ⟨L, ⟨e.symm⟩, ProjectiveLine.finiteDimensional_H k L (by omega)⟩

set_option linter.style.haveILetI false in
/-- Twisted sections are finite-dimensional for the action induced by the structure map.
Source: Stacks Project, Lemma 01YS(3).
(blueprint: lem-sc-p1-twisted-sections-finite-dimensional).
Proof: use serreTwistedSectionsTransport to identify the section space linearly
with finite-dimensional degree-zero cohomology on the projective line, then
transport finite dimensionality back along the equivalence. -/
theorem serreTwistedSectionsFiniteDimensional
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (n : ℤ) :
    let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
      (Scheme.ΓSpecIso _).inv.hom).comp
        (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
    letI := Module.compHom
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) ρ
    FiniteDimensional k
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) := by
  dsimp
  let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
    (Scheme.ΓSpecIso _).inv.hom).comp
      (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
  letI := Module.compHom
    Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) ρ
  obtain ⟨L, ⟨e⟩, hL⟩ := serreTwistedSectionsTransport k G hG n
  letI := hL
  exact finiteDimensional_of_linearEquiv e

end AlgebraicGeometry
