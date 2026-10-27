/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Sheaf.AlgebraicGeometry.BertiniSmoothAffineLinearSystem
import Sheaf.AlgebraicGeometry.BertiniFiniteCoverIrreducibleSystem
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# One smooth dimension cut preserving a connected finite étale cover

Source: the current blueprint, `lem-zl-bertini-finite-cover-curve.proof.md`,
paragraphs 2--4, through the construction of `X₁`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem coefficient_open_point {k : Type u} [Field k] [IsAlgClosed k]
    {r : ℕ} (O : (Spec (.of (MvPolynomial (Fin r) k))).Opens)
    (hO : (O : Set (Spec (.of (MvPolynomial (Fin r) k)))).Nonempty) :
    ∃ a : Fin r → k,
      Set.range (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) a))) ⊆
        (O : Set _) := by
  let q : Spec (.of (MvPolynomial (Fin r) k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom MvPolynomial.C)
  have : LocallyOfFiniteType q := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    change (MvPolynomial.C : k →+* MvPolynomial (Fin r) k).FiniteType
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  have : JacobsonSpace (Spec (.of (MvPolynomial (Fin r) k))) :=
    LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨x, hxO, hxc⟩ := nonempty_inter_closedPoints hO O.isOpen.isLocallyClosed
  let p := pointOfClosedPoint q x hxc
  let φ := (Spec.preimage p).hom
  have hC : φ.comp MvPolynomial.C = RingHom.id k := by
    have h := congrArg Spec.preimage (pointOfClosedPoint_comp q x hxc)
    simp only [Spec.preimage_comp, q, Spec.preimage_map, Spec.preimage_id] at h
    exact congrArg CommRingCat.Hom.hom h
  have he : MvPolynomial.eval₂Hom (RingHom.id k) (fun i ↦ φ (MvPolynomial.X i)) = φ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa using congrArg (fun h : k →+* k ↦ h c) hC.symm
    · intro i
      simp
  refine ⟨fun i ↦ φ (MvPolynomial.X i), ?_⟩
  rw [he, CommRingCat.ofHom_hom, Spec.map_preimage]
  rintro y ⟨z, rfl⟩
  simpa only [p, pointOfClosedPoint_apply] using hxO

/-- One simultaneous smooth and irreducible Bertini cut through prescribed rational points.
Source: blueprint `lem-zl-bertini-finite-cover-curve.proof.md`, paragraphs 2--4;
Stacks Project, Tags 0FD5, 0FD6, 0G4F.
(blueprint: lem-zl-bertini-finite-cover-dimension-cut).

Proof: Embed the affine finite-type scheme in affine space and take its reduced projective
closure. Represent the prescribed rational points by their finite set of closed images.
Apply `lem-zl-bertini-prescribed-point-smooth-system` to a sufficiently high twist of the
closure. Its finite basis spans precisely the sections vanishing on these points, generates
the twist away from them, and induces an immersion there. Use that basis to apply
`lem-zl-bertini-finite-cover-irreducible-system`. The nonempty smooth-member and
irreducible-member opens intersect because their affine coefficient space is irreducible.
Choose a rational point of the intersection over the algebraically closed field. Its zero
scheme is affine, smooth, of pure dimension `d - 1`, and contains the prescribed points.
Over an algebraically closed field pure dimension for a smooth finite-type scheme is
smooth relative dimension. Geometric irreducibility makes both the zero scheme and its
inverse image connected. The closed immersion of the zero scheme factors each prescribed
rational point: its defining section vanishes on that reduced point, so its pulled-back
ideal is zero. This is a single hypersurface cut, with no iteration or descent. -/
theorem exists_smooth_finiteCover_dimension_cut {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsAffine X] [ConnectedSpace X]
    {d : ℕ} (hd : 2 ≤ d) [SmoothOfRelativeDimension d f]
    {T : Scheme.{u}} (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T]
    (S : Finset (Spec (.of k) ⟶ X)) (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ f = 𝟙 _) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X), IsClosedImmersion j ∧ IsAffine Y ∧
      SmoothOfRelativeDimension (d - 1) (j ≫ f) ∧ ConnectedSpace Y ∧
      (∀ s ∈ S, ∃ t, t ≫ j = s) ∧ ConnectedSpace ↑(pullback π j) := by
  classical
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular X := IsRegular.of_smooth f
  have : IrreducibleSpace X := IsRegular.irreducibleSpace X
  have : Smooth (X ↘ Spec (.of k)) := ‹Smooth f›
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  have : QuasiCompact (X ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
  have hdim : X.IsPureDimension d := by
    intro Z hZ
    have hZeq : Z = Set.univ := by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hZ
    subst Z
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).trans
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension f d)
  let F : Finset X := S.image (fun s ↦ s (IsLocalRing.closedPoint k))
  have hF : F.Nonempty := hS.image _
  have hclosed : ∀ x ∈ F, IsClosed ({x} : Set X) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact ((pointEquivClosedPoint f) ⟨s, hS' s hs⟩).2
  obtain ⟨U₀, hU₀, L, hL, r, ψ, hlin, hvan, hgen, himm, O, hO, hsm⟩ :=
    exists_smooth_affine_prescribedPoint_linearSystem (k := k) X d hd hdim F hF hclosed
  have := hL
  have := himm
  obtain ⟨P, hP, hirr⟩ := exists_open_geometricallyIrreducible_finiteCover_linearSystem
    k X d hd hdim T π F hF hclosed U₀ hU₀ L (Fin r → k) r
      (Pi.basisFun k (Fin r)) ψ hlin hvan hgen
  have hOP : ((O : Set (Spec (.of (MvPolynomial (Fin r) k)))) ∩
      (P : Set (Spec (.of (MvPolynomial (Fin r) k))))).Nonempty :=
    nonempty_preirreducible_inter O.isOpen P.isOpen hO hP
  obtain ⟨a, ha⟩ := coefficient_open_point (k := k) (O ⊓ P) hOP
  have haO : Set.range
      (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) a))) ⊆
        (O : Set _) := fun _ hy ↦ (ha hy).1
  have haP : Set.range
      (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) a))) ⊆
        (P : Set _) := fun _ hy ↦ (ha hy).2
  obtain ⟨hsmooth, haff, hpure⟩ := hsm a haO
  have hgood := hirr a (by simpa only [Pi.basisFun_repr] using haP)
  obtain ⟨_, _, _, hconn, hcover⟩ := hgood.2.2 hsmooth
  let J := (Scheme.Modules.homOfGlobalSection L (ψ a)).zeroLocus
  have : Smooth (J.subschemeι ≫ f) := hsmooth
  have : ConnectedSpace J.subscheme := hconn
  have : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (J.subschemeι ≫ f)
  have : IsRegular J.subscheme := IsRegular.of_smooth (J.subschemeι ≫ f)
  have : IrreducibleSpace J.subscheme := IsRegular.irreducibleSpace J.subscheme
  have hdimY : topologicalKrullDim J.subscheme = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    have hp := hpure Set.univ (by simp only [irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff])
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ J.subscheme).isHomeomorph).symm.trans hp
  refine ⟨J.subscheme, J.subschemeι, inferInstance, haff,
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq (J.subschemeι ≫ f) (d - 1)).mpr
      hdimY, hconn, ?_, hcover⟩
  intro s hs
  apply (IsClosedImmersion.existsUnique_fac_of_field J.subschemeι s ?_).exists
  rw [J.range_subschemeι]
  exact hvan a _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

end AlgebraicGeometry
