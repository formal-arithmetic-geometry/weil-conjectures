/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Algebra.Homology.LocalResidueCohomologyLifting
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

/-! # A section-normalized local complex for a proper flat module

Source: Stacks Project, Cohomology of Schemes, Tag 07VK and its explanation;
Derived Categories of Schemes, Tag 0B91; Cohomology, Tag 08HY.
(blueprint: lem-sfb-proper-flat-section-normalized-stalk-complex).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded finite free complex over the base stalk computes the pushforward stalk
and the first two fibre cohomology groups, with its degree-zero comparison normalized
by actual tensor pullback of sections. There is no cohomology-vanishing hypothesis.

Source: Stacks Project, Cohomology of Schemes, Tag 07VK,
lemma-perfect-direct-image and remark-explain-perfect-direct-image;
Derived Categories of Schemes, Tag 0B91(2); Cohomology, Tag 08HY;
Schemes, Tags 01HV, 01I7 and 01I9; Sheaves, Tag 0096.
(blueprint: lem-sfb-proper-flat-section-normalized-stalk-complex).

Proof: Choose an affine neighbourhood of s. Properness and the Noetherian base give
finite presentation of the morphism. The local rank-one trivializations of F give its
quasi-coherence and finite presentation; its stated stalkwise flatness is relative
flatness. The proper-flat perfect-direct-image theorem gives a perfect model of Rf_*F
with canonical derived base change. Represent it near s by a bounded finite projective
complex; localize its terms at s. They are finite free over the local ring O_(S,s).
Fix this one model isomorphism throughout. Exactness of stalks, exactness of tilde on
modules, the affine tilde-sections unit, and the affine higher-direct-image comparison
identify its zeroth cohomology with (f_*F)_s. Derived pullback of the bounded flat model
is termwise scalar extension. The unit-normalized tilde-pullback comparison followed
by canonical perfect base change identifies its residue cohomology with fibre
cohomology. Degree zero uses the degree-zero right-derived/global-sections unit, and
degree one uses the same derived global sections that defines moduleCohomology.
Restriction of scalars is exact and does not change the underlying cohomology groups,
so these are the groups of residueComplex. Finally a representative section t' on
f^(-1)U represents its germ in the pushforward stalk. The scalar-extension unit sends
its cycle z to 1 tensor z. The canonical base-change mate is adjoint to pullback of the
counit; evaluating that counit by the tensor-pullback adjunction gives 1 tensor t',
restricted to the whole fibre. Thus the last displayed equality is the actual
restriction formula, with the same fixed model on both sides. Empty fibres give zero
cohomology groups, and no reducedness or closed-point hypothesis enters the argument. -/
theorem exists_section_normalized_stalk_complex {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [CompactSpace S] [IsProper f]
    (F : X.Modules) [F.IsInvertible]
    (hflat : ∀ x : X, Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F))) (s : S) :
    ∃ (C : CochainComplex (ModuleCat.{u} (S.presheaf.stalk s)) ℤ) (a b : ℤ),
      C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (S.presheaf.stalk s) (C.X i)) ∧
      (∀ i : ℤ, Module.Finite (S.presheaf.stalk s) (C.X i)) ∧
      ∃ (e₀ : C.homology 0 ≃+
          ((RingedSpace.moduleStalkFunctor S.toRingedSpace s).obj ((pushforward f).obj F)))
        (eF₀ : C.residueComplex.homology 0 ≃+ Γ((tensorPullback (f.fiberι s)).obj F, ⊤))
        (eF₁ : C.residueComplex.homology 1 ≃+
          ((RingedSpace.moduleCohomology (f.fiber s).toRingedSpace 1).obj
            ((tensorPullback (f.fiberι s)).obj F))),
        ∀ (U : S.Opens) (hs : s ∈ U) (t' : Γ(F, f ⁻¹ᵁ U)),
          eF₀ (C.residueCohomologyMap 0 (e₀.symm
            (TopCat.Presheaf.germ ((pushforward f).obj F).val.presheaf U s hs t'))) =
          ((tensorPullback (f.fiberι s)).obj F).val.map
            (homOfLE (fun x _ ↦ Eq.mpr
              (congrArg (fun y : S ↦ y ∈ U) (f.fiberHomeo s x).property) hs)).op
            (tensorPullbackSection (f.fiberι s) F (f ⁻¹ᵁ U) t') := by sorry

end AlgebraicGeometry.Scheme.Modules
