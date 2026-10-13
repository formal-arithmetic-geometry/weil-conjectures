/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel

/-! # Naturality of one tensor-Hom evaluation component

Source: Stacks Project, sites-cohomology.tex, Tag 0A90.
(blueprint: lem-pc-tensor-hom-uncurry-component-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Evaluation on a single degree pair commutes with simultaneous chain maps.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90, functoriality of the
Hom-total-tensor comparison; cohomology.tex, Tag 08DJ, componentwise evaluation.
(blueprint: lem-pc-tensor-hom-uncurry-component-naturality).

Proof: Let π be the chosen product projections of homComplex_exists and set
I = schemeHomKInjectiveResolution X. Its map specification gives
Hom(b,I(c)).f p followed by π(L',I(M'),p,q,n) equal to
π(L,I(M),p,q,n) followed by homObjMap(b.f q,I(c).f n).
Precompose this equation by a.f p followed by φ.f p. Apply the inverse
sheaf tensor-Hom equivalence. Naturality in its free variable precomposes
uncurrying by L'^q tensor a.f p; naturality in its Hom source precomposes
by b.f q tensor P^p; naturality in its target postcomposes by I(c).f n.
The two whiskerings combine to b.f q tensor a.f p. Naturality of the
braiding moves that tensor map past the symmetry and changes its order
to a.f p tensor b.f q. The definition of schemeTensorHomUncurryComponent
then identifies both sides with the displayed equality. No coproduct,
differential, localization, or flatness argument enters this calculation.
Identity maps give the original component; a zero map in any variable
gives zero on both sides by the additivity of internal Hom and tensor.
The argument uses only q+p=n, and applies in every integer degree. -/
theorem schemeTensorHomUncurryComponent_natural (X : Scheme.{u})
    (P P' L L' M M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : P' ⟶ P) (b : L' ⟶ L) (c : M ⟶ M')
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p q n : ℤ) (h : q + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    schemeTensorHomUncurryComponent X P' L' M'
        (a ≫ φ ≫ (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
          (X := (op L, (schemeHomKInjectiveResolution X).obj M))
          (Y := (op L', (schemeHomKInjectiveResolution X).obj M'))
          (b.op, (schemeHomKInjectiveResolution X).map c)) p q n h =
      (a.f p ⊗ₘ b.f q) ≫ schemeTensorHomUncurryComponent X P L M φ p q n h ≫
        ((schemeHomKInjectiveResolution X).map c).f n := by sorry

end AlgebraicGeometry
