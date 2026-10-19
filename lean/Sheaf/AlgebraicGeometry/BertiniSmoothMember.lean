/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

/-!
# Smooth general members of an immersive linear system

Source: Stacks Project, Varieties, Situation 0FD3 and Lemma 0FD6
(blueprint: lem-zl-bertini-smooth-member).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The coefficient point of affine space defined by a tuple over an extension field.
Source: Stacks Project, Situation 0FD3 (blueprint: lem-zl-bertini-smooth-member). -/
def bertiniCoefficientPoint {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type u} (a : I → K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (MvPolynomial I k)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap k K) a))

/-- The section `∑ aᵢ ψ(vᵢ)` on the field base change of `Y`, using the canonical
module-pullback unit. Scalars act through the projection to `Spec K`.
Source: Stacks Project, Situation 0FD3 (blueprint: lem-zl-bertini-smooth-member). -/
def bertiniMemberSection {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (a : I → K) :
    Γ((Scheme.Modules.tensorPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L, ⊤) :=
  ∑ i, (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (a i)) •
    Scheme.Modules.tensorSectionsUnit
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L
        (s i)

/-- A family of top-open sections as compatible global sections, through the existing
unit/global-section equivalence. Source: Stacks Project, Situation 0FD3
(blueprint: lem-zl-bertini-smooth-member). -/
def bertiniSectionFamily {Y : Scheme.{u}} (L : Y.Modules) {I : Type u}
    (s : I → Γ(L, ⊤)) : I → L.sections :=
  fun i ↦ (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (s i))

/-- An immersive generated linear system on a smooth scheme has smooth general members.
The additive map `ψ`, together with its displayed scalar law, is precisely a `k`-linear map
into global sections with the scalar action induced by `f`. A basis indexed by a finite set
expresses finite dimensionality. The single nonempty open works for all extension fields and tuples.

Source: Stacks Project, Varieties, Situation 0FD3 and Lemma 0FD6
(blueprint: lem-zl-bertini-smooth-member).

Proof:
1. Form the universal section `∑ xᵢ ψ(bᵢ)` on affine space times `Y`. Its zero scheme has
   fibre `Z(∑ aᵢ ψ(bᵢ))`, by zero-scheme formation and base change
   (`def-pc-zero-scheme`, `def-pc-base-change`).
2. The non-smooth locus of its projection to affine space has image in a proper closed
   subset, by `lem-zl-bertini-singular-locus-dimension` (Stacks 0FD6).
3. On the complementary open, the projection is smooth: use smoothness local on the source
   (`lem-weil-pbc-smooth-local-on-source`). Smooth base change
   (`lem-pc-proper-base-change`, clause 2) makes every field-valued fibre smooth.
4. The complement is nonempty. The universal-family fibre identification makes this same
   open work over every extension field, exactly the meaning of general in Situation 0FD3.
-/
theorem exists_open_smooth_bertiniMember
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible]
    {V : Type u} [AddCommGroup V] [Module k V] {I : Type u} [Fintype I]
    (b : Module.Basis I k V) (ψ : V →+ Γ(L, ⊤))
    (_hlinear : ∀ (c : k) (v : V),
      ψ (c • v) =
        f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) • ψ v)
    (hgen : Epi (L.freeHomEquiv.symm (bertiniSectionFamily L (fun i ↦ ψ (b i)))))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections I f L
      (bertiniSectionFamily L (fun i ↦ ψ (b i))) hgen)] :
    ∃ U : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
      (U : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
      ∀ (K : Type u) [Field K] [Algebra k K] (a : I → K),
        Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (U : Set _) →
        Smooth ((Scheme.Modules.homOfGlobalSection
          ((Scheme.Modules.tensorPullback
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L)
          (bertiniMemberSection f L (fun i ↦ ψ (b i)) a)).zeroLocus.subschemeι ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  sorry

end

end AlgebraicGeometry
