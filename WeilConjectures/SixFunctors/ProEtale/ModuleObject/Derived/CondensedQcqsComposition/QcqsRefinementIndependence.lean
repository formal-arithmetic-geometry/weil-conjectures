/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs

/-! # Transport of a fixed compositor through coherent compactification comparisons
(blueprint: new-p3-qcqs-refinement-independence).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coherent comparison restricted to bounded constructible targets. -/
def systemComparison {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (c d : Compactification f) : S.support ℓ c ≅ S.support ℓ d :=
  NatIso.ofComponents (fun K ↦ (bc ℓ Y).isoMk ((S.comparison c d).app K))
    (fun t ↦ ObjectProperty.hom_ext _ ((S.comparison c d).hom.naturality t))

/-- The comparison of a pair of compact-support models. -/
def inputComparison {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    (sh : System ℓ h) (sg : System ℓ g)
    (c c' : Compactification h) (d d' : Compactification g) :
    sh.support ℓ c ⋙ sg.support ℓ d ≅ sh.support ℓ c' ⋙ sg.support ℓ d' :=
  NatIso.hcomp (systemComparison ℓ sh c c') (systemComparison ℓ sg d d')

/-- Extend a compositor on one triangle using the specified comparison isomorphisms. -/
def extendCompositor {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    (sh : System ℓ h) (sg : System ℓ g) (sgh : System ℓ (h ≫ g))
    (T : Compactification.Triangle h g)
    (A : sh.support ℓ T.cf ⋙ sg.support ℓ T.cg ≅ sgh.support ℓ T.cfg)
    (c : Compactification h) (d : Compactification g) (e : Compactification (h ≫ g)) :
    sh.support ℓ c ⋙ sg.support ℓ d ≅ sgh.support ℓ e :=
  inputComparison ℓ sh sg c T.cf d T.cg ≪≫ A ≪≫ systemComparison ℓ sgh T.cfg e

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
