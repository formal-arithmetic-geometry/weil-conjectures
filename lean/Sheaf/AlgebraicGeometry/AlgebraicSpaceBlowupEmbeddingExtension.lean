/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommonAdmissibleBlowups
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQcOpenBoundaryIdeal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceComposeAdmissibleBlowups
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence

/-! # Extending a prescribed projective immersion after admissible blowups

Source: Stacks Project, More on Morphisms of Spaces, Tag 088R,
with scheme base B; Divisors on Spaces, Tags 085Q, 085R, 085T and 085Z
(blueprint: lem-sfb-space-blowup-embedding-extension).

The blowup of X uses the existing affine-etale-chart presentation; the blowup of Z
is the ordinary scheme construction. A cartesian square with identity bottom map
specifies the inverse identification of the entire inverse image of U with U.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A prescribed projective immersion on a quasi-compact open extends to an open
immersion from an admissible blowup into a blowup of a projective closed subscheme.
Source: Stacks Project, More on Morphisms of Spaces, Tag 088R, with B a scheme;
Divisors on Spaces, Tags 085Q, 085R, 085T and 085Z
(blueprint: lem-sfb-space-blowup-embedding-extension).

Proof:
1. Projective space over the qcqs scheme B is proper, hence qcqs, by
   lemma-nagata-projective-space-base-change-proper and
   lem-sfb-space-qcqs-source-products. The immersion makes U a scheme and is
   quasi-compact by lem-sfb-space-qcqs-permanence. Its scheme-theoretic image
   (def-nagata-scheme-theoretic-image and def-nagata-scheme-image-factor) gives Z,
   with U open in Z by lemma-nagata-immersion-open-in-scheme-image. The closed
   immersion is proper by lem-sfb-space-closed-subspace-proper; composition uses
   lem-sfb-space-proper-composition.
2. U is separated of finite type over B. Apply lem-sfb-space-common-admissible-blowups
   to X and Z along U, obtaining blowups X_1 and Z_1 openly embedded in W, agreeing
   on U. All spaces are qcqs by lem-sfb-space-qcqs-source-products and
   lem-sfb-space-qcqs-permanence.
3. By lem-sfb-space-qc-open-boundary-ideal choose a finite-type ideal cutting out
   W minus U. Blow it up to T. By lem-sfb-space-blowup-chart-properties, U is
   schematically dense in T (complement of an effective Cartier divisor), and the
   inverse images A and D of X_1 and Z_1 are their restricted blowups. D is a scheme.
4. Use lem-sfb-space-compose-admissible-blowups on X and Z to replace A and D by
   single blowups in finite-type ideals I and J, unit on U and identified there.
   The scheme clause of lem-sfb-space-blowup-chart-properties identifies J with a
   Zariski quasi-coherent ideal and D with its ordinary scheme blowup.
5. D is proper over B by lem-sfb-space-proper-composition. T is separated over B by
   lem-sfb-space-separated-fp-composition and blowup properness. Thus D to T is
   proper by lem-sfb-space-proper-cancellation; its open image is also closed.
6. Pull back this closed immersion to A. Its ideal vanishes on U by
   lem-sfb-space-ideal-closed-subspace-correspondence. Schematic density of U in A
   forces the ideal to vanish. Hence A is the fibre product A times_T D and is open
   in the scheme D. Set V = A, and retain its identification with the blowup of X.
7. By lem-sfb-space-blowup-chart-properties its projection q is representable and
   proper, and its full inverse image of U is U. The inverse section is the common
   copy of U throughout these constructions. Thus b v s = u and i u = a.
   No density of U in X, Noetherianity or reducedness is used. -/
theorem exists_blowup_embedding_extension
    {S : Scheme.{u}} (B : Over S) [CompactSpace B.left] [QuasiSeparatedSpace B.left]
    (X U : AlgebraicSpace S) (f : X ⟶ schemeSpace B)
    (hfs : MapIsSeparated f) (hfft : MapIsFiniteType f) (j : U ⟶ X)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (hUqc : ∃ (T : Over S) (c : yoneda.obj T ⟶ U.obj.obj),
      CompactSpace T.left ∧ IsEtale c ∧ IsSurjective c)
    (n : ℕ)
    (a : U.obj.obj ⟶ yoneda.obj (Over.mk
      ((ProjectiveSpace (ULift.{u} (Fin (n + 1))) B.left) ↘ B.left ≫ B.hom)))
    (ha : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left) a)
    (haB : a ≫ yoneda.map (Over.homMk
        ((ProjectiveSpace (ULift.{u} (Fin (n + 1))) B.left) ↘ B.left)) =
      j.hom.hom ≫ f.hom.hom) :
    ∃ (Z : Over S)
      (i : Z ⟶ Over.mk
        ((ProjectiveSpace (ULift.{u} (Fin (n + 1))) B.left) ↘ B.left ≫ B.hom))
      (u₀ : U.obj.obj ⟶ yoneda.obj Z) (I : QuasiCoherentIdeal X)
      (J : Z.left.IdealSheafData),
      IsClosedImmersion i.left ∧
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) u₀ ∧
      u₀ ≫ yoneda.map i = a ∧
      (I.val : X.Modules).IsFiniteType ∧ J.toModules.IsFiniteType ∧
      (∀ T : X.EtaleSite,
        (∃ c : yoneda.obj T.obj.left ⟶ U.obj.obj,
          c ≫ j.hom.hom = T.obj.hom) → idealSectionImage I.val.arrow T = ⊤) ∧
      (∀ (T : Over S) (h : T ⟶ Z) (c : yoneda.obj T ⟶ U.obj.obj),
        c ≫ u₀ = yoneda.map h → J.comap h.left = ⊤) ∧
      ∃ (D : BlowupPresentation I) (V : Over S) (e : schemeSpace V ≅ D.space)
        (v : V ⟶ Over.mk (J.blowupMap ≫ Z.hom)),
        IsOpenImmersion v.left ∧
        IsRepresentable (e.hom.hom.hom ≫ D.projection.hom.hom) ∧
        MapIsProper (e.hom ≫ D.projection) ∧
        e.hom.hom.hom ≫ D.projection.hom.hom ≫ f.hom.hom =
          yoneda.map (v ≫ Over.homMk J.blowupMap ≫ i ≫ Over.homMk
            ((ProjectiveSpace (ULift.{u} (Fin (n + 1))) B.left) ↘ B.left)) ∧
        ∃ s : U.obj.obj ⟶ yoneda.obj V,
          IsPullback s (𝟙 U.obj.obj)
            (e.hom.hom.hom ≫ D.projection.hom.hom) j.hom.hom ∧
          s ≫ yoneda.map (v ≫ Over.homMk J.blowupMap) = u₀ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
