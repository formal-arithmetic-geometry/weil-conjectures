/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType

/-!
# The universal family of zero schemes of a finite family of sections

Source: Stacks Project, Varieties, Situation 0FD3.
(blueprint: def-zl-bertini-universal-family).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- The universal section `∑ xᵢ pr₂* sᵢ` on coefficient affine space times `Y`.
The coordinates are the polynomial variables under the canonical global-sections isomorphism.
Source: Stacks Project, Situation 0FD3 (blueprint: def-zl-bertini-universal-family). -/
def bertiniUniversalSection {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    Γ((Scheme.Modules.tensorPullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
        f)).obj L, ⊤) :=
  ∑ i, (pullback.fst
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I k))).inv (MvPolynomial.X i)) •
    Scheme.Modules.tensorSectionsUnit
      (pullback.snd (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
        f) L (s i)

/-- The ideal sheaf of the universal zero scheme, constructed using the recorded zero scheme.
Source: Stacks Project, Situation 0FD3 (blueprint: def-zl-bertini-universal-family). -/
def bertiniUniversalIdeal {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (pullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f).IdealSheafData :=
  (Scheme.Modules.homOfGlobalSection _ (bertiniUniversalSection f L s)).zeroLocus

/-- The projection `q : H_univ ⟶ A^I_k` from the universal zero scheme.
Source: Stacks Project, Tag 0FD6 (blueprint: def-zl-bertini-universal-family). -/
def bertiniUniversalProjection {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (bertiniUniversalIdeal f L s).subscheme ⟶ Spec (CommRingCat.of (MvPolynomial I k)) :=
  (bertiniUniversalIdeal f L s).subschemeι ≫
    pullback.fst
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f

/-- The non-smooth locus of the universal projection: points with no smooth open neighbourhood.
Source: Stacks Project, Tag 0FD6 (blueprint: def-zl-bertini-universal-family). -/
def bertiniUniversalSingularLocus {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    Set (bertiniUniversalIdeal f L s).subscheme :=
  {h | ¬ ∃ W : (bertiniUniversalIdeal f L s).subscheme.Opens,
    h ∈ W ∧ Smooth (W.ι ≫ bertiniUniversalProjection f L s)}

/-- The non-smooth subset is closed: its complement is the union of all opens on which the
projection is smooth. Source: Stacks Project, Tag 0FD6, first universal-family paragraph.
(blueprint: def-zl-bertini-universal-family). -/
theorem isClosed_bertiniUniversalSingularLocus {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    IsClosed (bertiniUniversalSingularLocus f L s) := by
  have hopen : IsOpen {h | ∃ W : (bertiniUniversalIdeal f L s).subscheme.Opens,
      h ∈ W ∧ Smooth (W.ι ≫ bertiniUniversalProjection f L s)} := by
    rw [show {h | ∃ W : (bertiniUniversalIdeal f L s).subscheme.Opens,
        h ∈ W ∧ Smooth (W.ι ≫ bertiniUniversalProjection f L s)} =
      ⋃ (W : (bertiniUniversalIdeal f L s).subscheme.Opens)
        (_ : Smooth (W.ι ≫ bertiniUniversalProjection f L s)), (W : Set _) by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun ⟨W, hh, hs⟩ ↦ ⟨W, hs, hh⟩, fun ⟨W, hs, hh⟩ ↦ ⟨W, hh, hs⟩⟩]
    exact isOpen_iUnion fun W ↦ isOpen_iUnion fun _ ↦ W.isOpen
  exact hopen.isClosed_compl

/-- The reduced closed subscheme structure on the non-smooth locus.
Source: Stacks Project, Tag 0FD6, first universal-family paragraph.
(blueprint: def-zl-bertini-universal-family). -/
def bertiniSingularIdeal {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (bertiniUniversalIdeal f L s).subscheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨bertiniUniversalSingularLocus f L s, isClosed_bertiniUniversalSingularLocus f L s⟩

/-- The projection of the reduced non-smooth locus to the original smooth scheme.
Source: Stacks Project, Tag 0FD6, universal-family diagram.
(blueprint: def-zl-bertini-universal-family). -/
def bertiniSingularToSource {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (bertiniSingularIdeal f L s).subscheme ⟶ Y :=
  (bertiniSingularIdeal f L s).subschemeι ≫ (bertiniUniversalIdeal f L s).subschemeι ≫
    pullback.snd
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f

/-- The closed-subscheme structure has precisely the topology of the singular subset.
Source: Stacks Project, Tag 0FD6, reduced induced structure.
(blueprint: def-zl-bertini-universal-family). -/
def bertiniSingularHomeomorph {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (bertiniSingularIdeal f L s).subscheme ≃ₜ bertiniUniversalSingularLocus f L s :=
  Homeomorph.setCongr (by simp [bertiniSingularIdeal])

/-- Coefficient affine space is locally of finite type over the field.
Source: Stacks Project, Tag 0FD3, the finite coefficient space.
(blueprint: def-zl-bertini-universal-family). -/
theorem bertiniCoefficient_locallyOfFiniteType {k : Type u} [Field k]
    {I : Type u} [Finite I] :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact (RingHom.finiteType_algebraMap).mpr inferInstance

end

end AlgebraicGeometry
