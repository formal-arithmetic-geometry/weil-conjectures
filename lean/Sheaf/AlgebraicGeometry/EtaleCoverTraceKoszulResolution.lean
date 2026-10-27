/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.CategoryTheory.LargeSetSheafification
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian

/-! # The trace Koszul resolution of an étale scheme cover

Source: Stacks Project, Spaces Cohomology, Tag 0723, and More on Algebra, Tags 0622 and 0626
(blueprint: lem-sfb-etale-cover-trace-koszul-resolution).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

set_option autoImplicit false

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The constant integer ring on the small étale site, in its site value universe.
Source: Stacks 0723 (blueprint: lem-sfb-etale-cover-trace-koszul-resolution). -/
noncomputable abbrev traceKoszulRing : Sheaf X.etaleTopology CommRingCat.{u + 1} :=
  (constantSheaf X.etaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, 0} ℤ))

/-- The same coefficient sheaf with commutativity forgotten.
Source: Stacks 0723 (blueprint: lem-sfb-etale-cover-trace-koszul-resolution). -/
noncomputable abbrev traceKoszulCoefficients : Sheaf X.etaleTopology RingCat.{u + 1} :=
  (sheafCompose X.etaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj X.traceKoszulRing

/-- The sectionwise free module on maps into the étale scheme object `U`.
Source: Stacks 0723 (blueprint: lem-sfb-etale-cover-trace-koszul-resolution). -/
noncomputable abbrev traceKoszulFreePresheaf (U : X.EtaleSite) :=
  PresheafOfModules.freeObj (R := X.traceKoszulCoefficients.obj)
    (uliftYoneda.{u + 1}.obj U)

/-- The free integer sheaf with its canonical locally constant integer action.
This is module sheafification of the free coefficient presheaf. The resolution theorem
identifies its underlying abelian sheaf with sheafification of the free abelian presheaf.
Source: Stacks 0723 (blueprint: lem-sfb-etale-cover-trace-koszul-resolution). -/
noncomputable abbrev traceKoszulFree (U : X.EtaleSite) :=
  (PresheafOfModules.sheafification (𝟙 X.traceKoszulCoefficients.obj)).obj
    (X.traceKoszulFreePresheaf U)

/-- The local generator in the associated free sheaf.
Source: Stacks 0723 (blueprint: lem-sfb-etale-cover-trace-koszul-resolution). -/
noncomputable def traceKoszulGenerator (U V : X.EtaleSite) (a : V ⟶ U) :
    (X.traceKoszulFree U).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.traceKoszulCoefficients.obj)).unit.app (X.traceKoszulFreePresheaf U)).app
      (op V) (ModuleCat.freeMk (ULift.up a))

/-- The abelian sheaf specified directly by the free abelian presheaf on `U/X`.
Source: Stacks 0723 (blueprint: lem-sfb-etale-cover-trace-koszul-resolution). -/
noncomputable abbrev traceKoszulAbelian (U : X.EtaleSite) :=
  (presheafToSheaf X.etaleTopology AddCommGrpCat.{u + 1}).obj
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)

/-- The prescribed positive exterior terms `K_p = ∧^(p+1) E`.
Source: Stacks 0723 (blueprint: lem-sfb-etale-cover-trace-koszul-resolution). -/
noncomputable abbrev traceKoszulTerm (U : X.EtaleSite) (p : ℕ) :=
  SheafOfModules.siteExteriorPower (B := X.traceKoszulRing) (X.traceKoszulFree U) (p + 1)

/-- The sectionwise pure wedge followed by sheafification.
Source: Stacks 0723 (blueprint: lem-sfb-etale-cover-trace-koszul-resolution). -/
noncomputable abbrev traceKoszulWedge (U V : X.EtaleSite) (p : ℕ)
    (v : Fin (p + 1) → (X.traceKoszulFree U).val.obj (op V)) :=
  SheafOfModules.siteExteriorWedge (B := X.traceKoszulRing) (X.traceKoszulFree U)
    (p + 1) (op V) v

/-- The augmented trace Koszul complex of a surjective representable étale scheme cover
is exact, including the augmentation term. The comparison with the explicitly free
abelian sheaf identifies each generator, so fixes the integer-module interpretation.
Source: Stacks 0723, preceding Definition 0724; More on Algebra, Tags 0622 and 0626
(blueprint: lem-sfb-etale-cover-trace-koszul-resolution).

Proof: (1) constant integer sections are locally integers, using compatibility of
sheafification with underlying sets and the local-bijection criterion. Thus the free
abelian sheaf carries its canonical constant-integer action, giving the displayed
comparison and trace. Form sectionwise exterior powers and contraction by the trace
using `CliffordAlgebra.contractLeft`; its recurrence gives the displayed formula and
commutes with restriction, hence sheafifies. (2) In the double contraction, deletions
of positions i < j occur twice with opposite signs and equal scalar products. They
cancel, including the composite into the augmentation. (3) Over every test scheme V,
the base change V ×_X U is a surjective étale scheme cover. Its projection to U gives
a free generator e with trace 1, with no separation or fibre-finiteness hypothesis.
(4) Wedge multiplication by e contracts the augmented complex: D(e ∧ z) = z - e ∧ Dz,
and the degree-minus-one contraction sends r to re. Hence cycles locally become
boundaries and augmentation sections locally lift. (5) Objectwise homology is locally
zero; its underlying set map to the terminal presheaf is locally bijective. The
underlying-set sheafification comparison makes its abelian sheafification zero.
Exact sheafification commutes with homology, proving exactness at every term. -/
theorem etaleCover_traceKoszul_resolution (U : X.EtaleSite)
    (hf : IsSurjective U.obj.hom) :
    ∃ (i : (SheafOfModules.toSheaf X.traceKoszulCoefficients).obj
          (X.traceKoszulFree U) ≅ X.traceKoszulAbelian U)
      (ε : X.traceKoszulFree U ⟶ SheafOfModules.unit X.traceKoszulCoefficients)
      (a : X.traceKoszulTerm U 0 ⟶ SheafOfModules.unit X.traceKoszulCoefficients)
      (d : ∀ p : ℕ, X.traceKoszulTerm U (p + 1) ⟶ X.traceKoszulTerm U p),
      (∀ (V : X.EtaleSite) (b : V ⟶ U),
        i.hom.hom.app (op V) (X.traceKoszulGenerator U V b) =
          (toSheafify X.etaleTopology
            (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)).app (op V)
              (FreeAbelianGroup.of (ULift.up b))) ∧
      (∀ (V : X.EtaleSite) (b : V ⟶ U),
        ε.val.app (op V) (X.traceKoszulGenerator U V b) =
          (1 : X.traceKoszulRing.obj.obj (op V))) ∧
      (∀ (V : X.EtaleSite) (v : Fin 1 → (X.traceKoszulFree U).val.obj (op V)),
        a.val.app (op V) (X.traceKoszulWedge U V 0 v) = ε.val.app (op V) (v 0)) ∧
      (∀ (p : ℕ) (V : X.EtaleSite)
          (v : Fin (p + 1 + 1) → (X.traceKoszulFree U).val.obj (op V)),
        (d p).val.app (op V) (X.traceKoszulWedge U V (p + 1) v) =
          ∑ j : Fin (p + 1 + 1),
            (-1 : ℤ) ^ j.val •
              (ε.val.app (op V) (v j) •
                X.traceKoszulWedge U V p (fun k ↦ v (j.succAbove k)))) ∧
      (∃ h : (SheafOfModules.toSheaf X.traceKoszulCoefficients).map (d 0) ≫
            (SheafOfModules.toSheaf X.traceKoszulCoefficients).map a = 0,
        (ShortComplex.mk
          ((SheafOfModules.toSheaf X.traceKoszulCoefficients).map (d 0))
          ((SheafOfModules.toSheaf X.traceKoszulCoefficients).map a) h).Exact) ∧
      (∀ p : ℕ, ∃ h :
          (SheafOfModules.toSheaf X.traceKoszulCoefficients).map (d (p + 1)) ≫
            (SheafOfModules.toSheaf X.traceKoszulCoefficients).map (d p) = 0,
        (ShortComplex.mk
          ((SheafOfModules.toSheaf X.traceKoszulCoefficients).map (d (p + 1)))
          ((SheafOfModules.toSheaf X.traceKoszulCoefficients).map (d p)) h).Exact) ∧
      Epi ((SheafOfModules.toSheaf X.traceKoszulCoefficients).map a) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
