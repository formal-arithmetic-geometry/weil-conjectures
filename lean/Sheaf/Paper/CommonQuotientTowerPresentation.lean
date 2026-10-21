/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.RingTheory.Ideal.Maps

/-! # Presentations of towers of common quotient ring sheaves

Source: Stacks Project, proetale.tex, Tag 099L, section-derived-completion-noetherian;
sites-modules.tex, Tag 03EK, section-tensor-product.
(blueprint: def-weil-pbc-common-quotient-tower-presentation).

A quotient is specified by its locally surjective projection, rather than by a
sectionwise surjection. Extension of its kernel ideal is specified by the pushout
universal property in ring sheaves. This includes quotients whose sections lift only locally.
-/

@[expose] public section
set_option autoImplicit false
universe u v r m
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{r}}

/-- A tower `S_n = R/I_n = B/I_n B`, including the quotient projections and their
transition compatibility. Its ideals are the kernels of the projections from `R`.
The pushout with bottom map the identity says precisely that the projection from `B`
is the quotient by the extended ideal. Source: Stacks 099L and 03EK
(blueprint: def-weil-pbc-common-quotient-tower-presentation). -/
structure CommonQuotientTowerPresentation (φ : R ⟶ B) where
  /-- The common quotient rings; index zero denotes the first level. -/
  S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}
  /-- The compatible projections from the first coefficient ring. -/
  q : (Functor.const ℕᵒᵖ).obj R ⟶ S
  /-- The compatible projections from the second coefficient ring. -/
  b : (Functor.const ℕᵒᵖ).obj B ⟶ S
  /-- Quotient projections are locally surjective, with no assertion on global sections. -/
  q_surjective : ∀ n : ℕ, Presheaf.IsLocallySurjective J (q.app (op n)).hom
  /-- The specified common quotient is induced by the original coefficient morphism. -/
  pushout : ∀ n : ℕ, IsPushout φ (q.app (op n)) (b.app (op n)) (𝟙 _)

namespace CommonQuotientTowerPresentation
variable {φ : R ⟶ B} (D : CommonQuotientTowerPresentation φ)

/-- The quotient projection with its source ring explicit.
Source: Stacks 099L (blueprint: def-weil-pbc-common-quotient-tower-presentation). -/
abbrev projection (n : ℕ) : R ⟶ D.S.obj (op n) := D.q.app (op n)

/-- The projection from the second ring, with its source ring explicit.
Source: Stacks 099L (blueprint: def-weil-pbc-common-quotient-tower-presentation). -/
abbrev extensionProjection (n : ℕ) : B ⟶ D.S.obj (op n) := D.b.app (op n)

/-- The actual kernel ideal sheaf, evaluated on an object of the site.
Naturality of `q` makes these ideal sheaves descending with the tower index.
Source: Stacks 099L and 03EK
(blueprint: def-weil-pbc-common-quotient-tower-presentation). -/
def ideal (n : ℕ) (U : Cᵒᵖ) : Ideal (R.obj.obj U) :=
  RingHom.ker ((D.q.app (op n)).hom.app U).hom

/-- Local membership in `I_n M`: locally a section is a finite sum of products of
kernel-ideal sections and module sections. The generated sieve expresses local
membership without any enough-points hypothesis. Source: Stacks 03EK
(blueprint: def-weil-pbc-common-quotient-tower-presentation). -/
def locallyInIdealProduct
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (n : ℕ)
    (M : ringedSiteModules.{m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) : Prop :=
  Sieve.generate (fun (V : C) (f : V ⟶ U.unop) ↦
    M.val.map f.op x ∈ Submodule.span (R.obj.obj (op V))
      {y | ∃ j ∈ D.ideal n (op V), ∃ p : M.val.obj (op V), y = j • p}) ∈ J U.unop

end CommonQuotientTowerPresentation
end SheafOfModules
