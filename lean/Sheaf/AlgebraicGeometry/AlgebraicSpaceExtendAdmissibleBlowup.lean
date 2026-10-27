/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTypeSubmoduleExtension

/-! # Extending an admissible blowup from an open algebraic subspace

Source: Stacks Project, Divisors on Spaces, Tag 086D (lemma-extend-admissible-blowups),
with Tag 086B (definition-admissible-blowup)
(blueprint: lem-sfb-space-extend-admissible-blowup).

The cartesian square exhibits the prescribed blowup of V as the full inverse image
of V in the extended blowup. The last two squares identify both blowups over U intersect V
with that intersection, and the last equation is the identity in these coordinates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite-type blowup on V, trivial on U intersect V, extends to one on T trivial on U.
Source: Stacks Project, Divisors on Spaces, Tags 086B and 086D
(blueprint: lem-sfb-space-extend-admissible-blowup).

Proof:
1. On W = U union V glue J on V with the unit ideal on U. Explicitly, on an etale
   scheme E over W take the sections of O_W whose restrictions to E times_W V lie
   in J. The overlap unit condition makes this ideal restrict to J and O_U. Sheaf
   gluing and the local presentations give quasi-coherence, and local finite
   generators on the two opens give finite type. The union of their quasi-compact
   etale atlases proves W quasi-compact.
2. Apply lem-sfb-space-finite-type-submodule-extension to W in T, ambient module
   O_T and this glued submodule. The resulting finite-type quasi-coherent submodule
   of O_T is an ideal I. Its restriction to W is the glued ideal as a subobject,
   hence I is unit on U and restricts to J on V.
3. Form the blowup in I by etale descent of scheme blowups. The open-base-change
   clause of lem-sfb-space-blowup-chart-properties gives the displayed cartesian
   square with the prescribed blowup C of J. Thus h is an open immersion.
4. The complement-isomorphism clause of lem-sfb-space-blowup-chart-properties
   identifies both blowups over U intersect V with that intersection, since both
   ideals are unit there. These inverse projection maps are s and t, characterized
   by their cartesian squares. The comparison is over T, so in these coordinates
   it is an endomorphism of the intersection over itself, necessarily the identity:
   s followed by h is t. No containment or density of either open is used. -/
theorem exists_blowupPresentation_extend_admissible
    {S : Scheme.{u}} (T V : AlgebraicSpace S)
    (hTqc : ∃ (A : Over S) (a : yoneda.obj A ⟶ T.obj.obj),
      CompactSpace A.left ∧ IsEtale a ∧ IsSurjective a)
    (hTqs : IsAbsolutelyQuasiSeparated T) (U : OpenSubspace T)
    (hUqc : ∃ (A : Over S) (a : yoneda.obj A ⟶ U.val.toFunctor),
      CompactSpace A.left ∧ IsEtale a ∧ IsSurjective a)
    (v : V ⟶ T)
    (hv : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) v.hom.hom)
    (hVqc : ∃ (A : Over S) (a : yoneda.obj A ⟶ V.obj.obj),
      CompactSpace A.left ∧ IsEtale a ∧ IsSurjective a)
    (J : QuasiCoherentIdeal V) (hJ : (J.val : V.Modules).IsFiniteType)
    (hJU : IdealIsUnitAbove J v U) (C : BlowupPresentation J) :
    ∃ (I : QuasiCoherentIdeal T), (I.val : T.Modules).IsFiniteType ∧
      IdealIsUnitAbove I (𝟙 T) U ∧
      ∃ (B : BlowupPresentation I) (h : C.space ⟶ B.space),
        IsPullback C.projection h v B.projection ∧
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) h.hom.hom ∧
        ∃ (s : Limits.pullback U.val.ι v.hom.hom ⟶ C.space.obj.obj)
            (t : Limits.pullback U.val.ι v.hom.hom ⟶ B.space.obj.obj),
          IsPullback s (𝟙 (Limits.pullback U.val.ι v.hom.hom)) C.projection.hom.hom
            (Limits.pullback.snd U.val.ι v.hom.hom) ∧
          IsPullback t (𝟙 (Limits.pullback U.val.ι v.hom.hom)) B.projection.hom.hom
            (Limits.pullback.fst U.val.ι v.hom.hom ≫ U.val.ι) ∧
          s ≫ h.hom.hom = t := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
