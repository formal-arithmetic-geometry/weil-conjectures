/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Sheaf.AlgebraicGeometry.ProperFlatSectionNormalizedStalkComplex

/-! # Lifting fibre sections under first-cohomology vanishing

Source: Stacks Project, Cohomology of Schemes, Tag 07VK,
lemma-perfect-direct-image and remark-explain-perfect-direct-image;
the degree-zero section-lifting consequence extracted in the DAG.
(blueprint: lem-sfb-proper-flat-fibre-section-lifting).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Every section of an invertible, relatively flat module on a fibre with vanishing
first cohomology extends over an open neighbourhood of the base point. Restriction is
actual tensor pullback of the section followed by restriction to the whole fibre.

Source: Stacks Project, Cohomology of Schemes, Tag 07VK and
remark-explain-perfect-direct-image; Derived Categories of Schemes, Tag 0B91(2);
Algebra, Tags 00MT and 00NX; Cohomology, Tag 08HY.
(blueprint: lem-sfb-proper-flat-fibre-section-lifting).

Proof: Use a section-normalized finite free complex over the local ring of the base
at s. The normalized comparison identifies its zeroth cohomology with the pushforward
stalk and its first residue cohomology with the stated fibre cohomology. For a bounded
finite free complex over a local ring, vanishing of first residue cohomology implies
surjectivity of reduction on zeroth cohomology: pass to a minimal homotopy model,
apply Nakayama in degree one, and lift vectors in degree zero through the residue
quotient. Apply this algebraic result to lift the class of the prescribed fibre
section. Represent the resulting pushforward germ by a section on an open
neighbourhood of s. The normalized comparison says that its actual tensor-pullback
restriction is the prescribed section. The geometric model comparison is isolated
without a cohomology-vanishing hypothesis in
`exists_section_normalized_stalk_complex`; the local algebra is proved in
`CochainComplex.surjective_residueCohomologyMap_zero`.
-/
theorem exists_lift_section_of_fiber_h1_eq_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [CompactSpace S] [IsProper f]
    (F : X.Modules) [F.IsInvertible]
    (hflat : ∀ x : X, Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)))
    (s : S)
    (hH : Subsingleton ((RingedSpace.moduleCohomology (f.fiber s).toRingedSpace 1).obj
      ((tensorPullback (f.fiberι s)).obj F))) :
    ∀ t : Γ((tensorPullback (f.fiberι s)).obj F, ⊤),
      ∃ (U : S.Opens) (hs : s ∈ U) (t' : Γ(F, f ⁻¹ᵁ U)),
        ((tensorPullback (f.fiberι s)).obj F).val.map
          (homOfLE (fun x _ ↦ Eq.mpr
            (congrArg (fun y : S ↦ y ∈ U) (f.fiberHomeo s x).property) hs)).op
          (tensorPullbackSection (f.fiberι s) F (f ⁻¹ᵁ U) t') = t := by
  obtain ⟨C, a, b, hlow, hupp, hfree, hfinite, e₀, eF₀, eF₁, hcomparison⟩ :=
    exists_section_normalized_stalk_complex f F hflat s
  let := hlow
  let := hupp
  let := hfree
  let := hfinite
  let := hH
  have hres : Subsingleton (C.residueComplex.homology 1) := eF₁.injective.subsingleton
  intro t
  obtain ⟨y, hy⟩ := C.surjective_residueCohomologyMap_zero a b hres (eF₀.symm t)
  obtain ⟨U, hs, t', ht'⟩ :=
    TopCat.Presheaf.exists_germ_eq ((pushforward f).obj F).val.presheaf (e₀ y)
  refine ⟨U, hs, t', ?_⟩
  have hc := hcomparison U hs t'
  rw [ht', e₀.symm_apply_apply, hy, eF₀.apply_symm_apply] at hc
  exact hc.symm

end AlgebraicGeometry.Scheme.Modules
