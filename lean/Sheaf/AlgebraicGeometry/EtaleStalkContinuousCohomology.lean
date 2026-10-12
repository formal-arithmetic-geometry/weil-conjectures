/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants
import Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison
import Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation
import Sheaf.FieldTheory.GaloisAutomorphismExtension
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Continuous cohomology of the geometric stalk over a field

Source: Stacks Project, Tags 04JQ, 03QU and Section 0DVG.
(blueprint: lem-sc-etale-stalk-continuous-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- Compare cohomology of any abelian etale sheaf with continuous cohomology of its stalk.
The additive identification `c` must carry geometric transport of germs to the action on
`M`. Coefficients live in the field universe; sheaf values may be one universe higher.

Source: Stacks Project, Tags 04JQ and 03QU; Section 0DVG.
(blueprint: lem-sc-etale-stalk-continuous-cohomology).

Proof: The abelian geometric stalk equivalence of Tag 04JQ carries `F` to a discrete
Galois module. Every Galois automorphism of the separable closure extends to the algebraic
closure, and germs jointly generate the stalk. Thus `hc` says precisely that `c` is an
isomorphism of coefficient modules. Global sections are the invariant elements (03QU).
The equivalence is exact and preserves injectives, so transport an injective resolution
of `F` to obtain the derived invariants of its stalk.
For a profinite group and discrete coefficients, continuous cochains form an exact
cohomological delta-functor: a cochain has finite image on each compact finite power, so
one can choose finitely many lifts through any surjection. It is effaceable in positive
degrees by embedding a module into locally constant functions on the group, with action
by right translation and embedding the orbit function. Compactness gives a common open
stabilizer for each such function. Insertion of the first coordinate gives the contracting
homotopy, and its continuity follows from the finite clopen partitions. Hence this
universal delta-functor agrees with derived invariants in every degree. This argument
uses integer modules, with no finiteness hypothesis on the coefficient ring.
Finally the compact-open exponential law identifies iterated continuous maps with maps on
finite powers. Evaluation at `(1, g1, g1*g2, ...)` and the inverse
`c ↦ ((g0, ..., gn) ↦ g0 • c(g0⁻¹*g1, ..., g(n-1)⁻¹*gn))` identify homogeneous invariant
cochains with inhomogeneous cochains and commute with differentials. The resulting
cohomology equivalences, followed by coefficient transport along `c`, give the assertion;
universe lifts are removed using their canonical additive equivariant lift/down maps. -/
theorem nonempty_equiv_etale_cohomology_continuous_stalk
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (M : TopRep.{u} ℤ (Gal(Ks/K))) [DiscreteTopology M]
    (c : ((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F
      ≃+ M)
    (hc : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)),
      c ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z) =
      M.ρ g (c ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z)))
    (n : ℕ) :
    Nonempty (Sheaf.H.{u + 1} F n ≃ continuousCohomology n M) := by
  classical
  obtain ⟨E, Eset, i, j, _, hi, _⟩ :=
    abelianSheaves_equiv_discreteGModules.{u, 0} K Ks Ω
  let S := Spec (.of K)
  let T : S.Etale := MorphismProperty.Over.mk ⊤ (𝟙 S)
    (MorphismProperty.id_mem @AlgebraicGeometry.Etale S)
  have hT : Limits.IsTerminal T := MorphismProperty.Over.mkIdTerminal _ S
  let V := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op T)
  obtain ⟨t, ht⟩ := etaleGlobalSections_galoisInvariants K Ks Ω T hT E i hi
  let d : (E.functor.obj F).obj.V ≃+ M :=
    (i.app F).addCommGroupIsoToAddEquiv.trans c
  have hd : ∀ (g : Gal(Ks/K)) (z : (E.functor.obj F).obj.V),
      d ((E.functor.obj F).obj.ρ g z) = M.ρ g (d z) := by
    intro g z
    obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
    have : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    obtain ⟨X, x, a, ha⟩ := p.toPresheafFiber_jointly_surjective
      (P := F.obj) ((i.hom.app F) z)
    let x' : p.fiber.obj X := Over.homMk
      (Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left) (by
        rw [Category.assoc, Over.w x]
        change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K Ω)) = _
        rw [← Spec.map_comp]
        congr 1
        ext b
        exact τ.commutes b)
    have hcanonical := hi F g τ hτ X x x' rfl a
    have hgiven := hc g τ hτ X x x' rfl a
    have hz : (i.inv.app F) (p.toPresheafFiber X x F.obj a) = z := by
      rw [ha]
      exact (i.app F).addCommGroupIsoToAddEquiv.symm_apply_apply z
    rw [hz] at hcanonical
    change c ((i.hom.app F) ((E.functor.obj F).obj.ρ g z)) =
      M.ρ g (c ((i.hom.app F) z))
    rw [hcanonical, ← ha]
    exact hgiven
  let η : V ≅ E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat :=
    NatIso.ofComponents (fun X ↦ (t X).toAddCommGrpIso) (by
      intro X Y f
      ext z
      apply Subtype.ext
      exact ht X Y f z)
  obtain ⟨e⟩ := Rep.nonempty_equiv_rightDerived_continuousCohomology.{u, u + 2, u + 1, u + 1, u}
    (Gal(Ks/K)) _ E V η F M d.toIntLinearEquiv hd n
  have hH : Nonempty (Sheaf.H.{u + 1} F n ≃+ (V.rightDerived n).obj F) := by
    cases n with
    | zero =>
      exact ⟨(Sheaf.H.equiv₀ F hT).trans
        (V.rightDerivedZeroIsoSelf.app F).addCommGroupIsoToAddEquiv.symm⟩
    | succ q =>
      exact Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
        S.smallEtaleTopology T hT F q
  obtain ⟨eH⟩ := hH
  exact ⟨eH.toEquiv.trans e⟩

end AlgebraicGeometry.Scheme
