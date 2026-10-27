/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
import Sheaf.CategoryTheory.RingedCocontinuousMonoidal

/-! # Ordinary tensor transport through a ringed-site equivalence

Source: Stacks Project, Modules on Sites, Tags 03D1, 03EK and 03EL; Sites, lemma-equivalence.
-/

@[expose] public section
set_option autoImplicit false
universe u v u' v' w
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SheafOfModules

/-- A site equivalence and an invertible coefficient comparison preserve the ordinary
binary sheaf tensor product. Only existence is needed for transport of predicates;
no tensor comparison is chosen as data by this theorem.

Source: Stacks Project, Modules on Sites, Tags 03D1, 03EK and 03EL; Sites, lemma-equivalence.
This is the ordinary tensor-transport substep of Step 1 of
lem-sf-cbc-extension-zero-completion.

Proof: precompose module presheaves with the opposite site equivalence, and restrict
scalars along the given isomorphism of coefficient sheaves. On every object the
balanced tensor comparison sends a pure tensor to the tensor of the same two sections.
The inverse coefficient isomorphism gives its inverse; the balanced relations and
naturality of the coefficient map prove linearity and compatibility with restrictions.
Precomposition through an equivalence preserves sheaves and their sheafification:
the sheafification adjunctions correspond under the inverse equivalence. Apply this
sheafification comparison to the presheaf tensor isomorphism. The sheafified tensor
presentation then gives the displayed isomorphism, natural in both module variables.
The argument includes the zero ring and empty site, and requires no flatness of sections.
(blueprint: lem-sf-ringed-site-equivalence-tensor). -/
theorem pushforward_equivalence_tensor_iso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (R : Sheaf K CommRingCat.{w}) (S : Sheaf J CommRingCat.{w})
    (c : S ≅ (e.functor.sheafPushforwardContinuous CommRingCat.{w} J K).obj R) :
    letI := isMonoidal_W_independentCoefficients R
    letI := isMonoidal_W_independentCoefficients S
    letI := monoidalCategory R
    letI := monoidalCategory S
    let F := pushforward.{w} (F := e.functor) (J := J) (K := K)
      (R := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
      (S := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S)
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map c.hom)
    Nonempty (tensor _ ⋙ F ≅ F.prod F ⋙ tensor _) := by
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients S
  let := monoidalCategory R
  let := monoidalCategory S
  let F := pushforward.{w} (F := e.functor) (J := J) (K := K)
    (R := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S)
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map c.hom)
  change Nonempty (tensor _ ⋙ F ≅ F.prod F ⋙ tensor _)
  have : e.functor.IsCocontinuous J K :=
    (e.toAdjunction.isCocontinuous_iff_coverPreserving J K).2
      (CoverPreserving.of_isContinuous e.inverse K J)
  let a : (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S ≅
      (e.functor.sheafPushforwardContinuous RingCat.{w} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R) :=
    (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).mapIso c
  obtain ⟨h⟩ := ringed_cocontinuous_monoidal e.functor S R a
  let : F.Monoidal := h
  exact ⟨(Functor.Monoidal.μNatIso F).symm⟩

end SheafOfModules
