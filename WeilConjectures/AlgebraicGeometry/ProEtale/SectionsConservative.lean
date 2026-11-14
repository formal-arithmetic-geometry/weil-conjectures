/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Evaluation on affine weakly contractible objects is conservative

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-cor-pe-sections/det-pe-sections-conservative.md` (blueprint:
corollary-evaluation-weakly-contractible-objects).
-/

@[expose] public section

set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{t}}

/-- The module-sheaf category is abelian in the common site/coefficient universe.
Source: Stacks Project, Tag 03DA; `situation-conventions`
(blueprint: corollary-evaluation-weakly-contractible-objects). -/
noncomputable instance sections_module_abelian (R : Sheaf (topology X) RingCat.{u}) :
    Abelian (ringedSiteModules.{max u (t + 1)} R) := by
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses (topology X) R
  infer_instance

/-- Evaluation of module sheaves on a site object is additive.
Source: Stacks Project, Tag 03DA; `situation-conventions`
(blueprint: corollary-evaluation-weakly-contractible-objects). -/
noncomputable instance sections_evaluation_additive
    (R : Sheaf (topology X) RingCat.{u}) (W : X.ProEt) :
    (SheafOfModules.evaluation.{max u (t + 1)} R (op W)).Additive :=
  inferInstanceAs ((SheafOfModules.forget R ⋙
    PresheafOfModules.evaluation R.obj (op W)).Additive)

/-- Exactness is detected on affine weakly contractible objects by local lifting.
Source: Stacks Project, Tag 0947(1)
(blueprint: corollary-evaluation-weakly-contractible-objects). -/
private theorem exact_sections_iff
    (R : Sheaf (topology X) RingCat.{u})
    (S : ShortComplex (ringedSiteModules.{max u (t + 1)} R)) :
    S.Exact ↔ ∀ (W : X.ProEt), IsAffine W.left →
      (topology X).IsWeaklyContractible.{max u (t + 1)} W →
        (S.map (SheafOfModules.evaluation R (op W))).Exact := by
  have : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  have : HasSheafify (topology X) AddCommGrpCat.{max u (t + 1)} :=
    siteAbelianHasSheafify (topology X)
  have : (topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    siteAbelianWEqualsLocallyBijective (topology X)
  let F := SheafOfModules.toSheaf.{max u (t + 1)} R
  have : PreservesFiniteColimits F :=
    (moduleSheaves_colimits_forgetful.{t + 1, t, u, max u (t + 1)} R).2.2.1
  have key (W : X.ProEt) :
      (S.map (SheafOfModules.evaluation R (op W))).Exact ↔
        Function.Surjective ((F.map (kernel.lift S.g S.f S.zero)).hom.app (op W)) := by
    rw [ShortComplex.exact_map_iff_epi_map_kernel_lift, ModuleCat.epi_iff_surjective]
    rfl
  simp_rw [key]
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  constructor
  · intro h W _ hW
    have : Epi (F.map (kernel.lift S.g S.f S.zero)) := inferInstance
    exact hW ((sheafCompose (topology X) (CategoryTheory.forget AddCommGrpCat)).map
      (F.map (kernel.lift S.g S.f S.zero)))
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1
        ((Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)}
          (F.map (kernel.lift S.g S.f S.zero))).2 inferInstance))
  · intro h
    apply F.epi_of_epi_map (f := kernel.lift S.g S.f S.zero)
    apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)}
      (F.map (kernel.lift S.g S.f S.zero))).1
    refine ⟨fun {V} s ↦ ?_⟩
    obtain ⟨ι, W, f, hcov, hW⟩ := exists_wContractible_affine_cover X V
    have hcov' : Sieve.ofArrows W f ∈ topology X V :=
      Precoverage.generate_mem_toGrothendieck hcov
    refine (topology X).superset_covering ?_ hcov'
    rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
    obtain ⟨D, hD, e, _⟩ := hW i
    have : IsWContractibleRing D := hD
    have ha : IsAffine (W i).left := IsAffine.of_isIso e.inv
    have hw : (topology X).IsWeaklyContractible.{max u (t + 1)} (W i) :=
      isWeaklyContractible_of_iso e.symm
    exact (Presheaf.imageSieve _ s).downward_closed (h _ ha hw _) a

/-- Evaluation on affine weakly contractible objects detects exact sequences, acyclic
complexes, isomorphisms, and quasi-isomorphisms of modules on the small pro-etale site.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-cor-pe-sections/det-pe-sections-conservative.md`, clauses 1--3;
Stacks Project, Tags 0946, 0947, 05RT, and 0115
(blueprint: corollary-evaluation-weakly-contractible-objects).

Clause 1 is Proposition 0947(1); clauses 2--3 are its degreewise and cone
consequences, as expanded in the blueprint proof.

Proof:
1. Put `Z = ker g` and let `u : A ⟶ Z` be induced by `f`; its existence follows from
`f ≫ g = 0`.
The sequence is exact at `B` precisely when `coker u = Z / im f` is zero. The underlying
abelian sheaf of this cokernel is the abelian cokernel of `u`, by
`situation-conventions`; faithfulness reflects the zero object.
Thus exactness is equivalent to the underlying abelian map `u` being epic. By
`corollary-evaluation-weakly-contractible-objects`, this is equivalent to local lifting
of each section of `Z`. The equality `Z(V) = ker (g(V))` is the sectionwise kernel statement
from `situation-conventions`, yielding the local lifting formulation.
2. By `theorem-enough-affine-weakly-contractible-objects--1`, every site object has a covering by
affine objects `Spec D` with `D` w-contractible. The closed source theorem
`isWeaklyContractible_of_iso`, recorded in `corollary-evaluation-weakly-contractible-objects`, makes
each such object weakly contractible in the module universe. Thus every object has a covering by the
class used here.
3. If the sequence is exact, the underlying abelian map `u` is locally surjective. Forgetting
abelian groups to sets preserves local surjectivity. Apply the defining lifting property
`IsWeaklyContractible` directly to this set-sheaf morphism to obtain surjectivity over `W`.
The sectionwise kernel equality gives exactness after evaluation; the reverse inclusion
follows from `f ≫ g = 0`. No set-sheaf epimorphism conversion is needed.
4. Conversely, exactness on every affine weakly contractible member of a covering gives,
for a section in `ker (g(V))`, local lifts through `f`; these lifts need not agree on
overlaps, which is exactly local surjectivity and hence exactness of the sheaf sequence.
5. For every cochain complex `K`, its degree-`q` cohomology is `ker d^q / im d^(q-1)` by
`corollary-evaluation-weakly-contractible-objects`. It vanishes exactly when the adjacent maps are
exact. Apply clause 1 degreewise and exchange the quantifiers over `q` and `W`; no boundedness is
used.
6. An isomorphism of module sheaves has bijective components by evaluating its inverse.
Conversely, apply clause 1 to `A --0--> A --f--> B` and `A --f--> B --0--> B`.
Bijectivity of each evaluated map gives exactness of these evaluated short complexes.
Thus the original short complexes are exact, making `f` both mono and epi. The abelian
category criterion `isIso_of_mono_of_epi` proves that `f` is an isomorphism.
7. For a morphism `v : K ⟶ L`, use the cone with degree `q` equal to
`L^q ⊞ K^(q+1)` and differential `(l,k) ↦ (d_L l + v k, -d_K k)`. The cone criterion
`corollary-evaluation-weakly-contractible-objects` identifies quasi-isomorphisms with acyclic cones.
Finite biproducts and sectionwise limits from `situation-conventions`,
together with additivity, identify the evaluated cone with the cone of `v(W)`. Clause 2
therefore gives the quasi-isomorphism equivalence.
-/
theorem sections_conservative
    (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) :
    (∀ (A B C : ringedSiteModules.{max u (t + 1)} R)
        (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).Exact ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            ((ShortComplex.mk f g h).map
              (SheafOfModules.evaluation.{max u (t + 1)} R (op W))).Exact) ∧
    (∀ (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ),
      K.Acyclic ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            HomologicalComplex.Acyclic
              ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj K)) ∧
    (∀ (A B : ringedSiteModules.{max u (t + 1)} R) (f : A ⟶ B),
      IsIso f ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            Function.Bijective
              ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).map f).hom) ∧
    (∀ (K L : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
        (f : K ⟶ L),
      QuasiIso f ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            QuasiIso
              (((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f)) := by
  have hacyclic (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ) :
      K.Acyclic ↔ ∀ (W : X.ProEt), IsAffine W.left →
        (topology X).IsWeaklyContractible.{max u (t + 1)} W →
          ((SheafOfModules.evaluation R (op W)).mapHomologicalComplex
            (ComplexShape.up ℤ) |>.obj K).Acyclic := by
    constructor
    · intro h W ha hw i
      exact (exact_sections_iff R (K.sc i)).1 (h i) W ha hw
    · intro h i
      exact (exact_sections_iff R (K.sc i)).2 (fun W ha hw ↦ h W ha hw i)
  refine ⟨fun A B C f g h ↦ exact_sections_iff R (ShortComplex.mk f g h),
    hacyclic, ?_, ?_⟩
  · intro A B f
    constructor
    · intro hf W _ _
      have := hf
      exact (ConcreteCategory.isIso_iff_bijective _).1
        (inferInstanceAs (IsIso ((SheafOfModules.evaluation R (op W)).map f)))
    · intro hf
      have hm : Mono f := by
        let S := ShortComplex.mk (0 : A ⟶ A) f (by simp)
        apply (S.exact_iff_mono rfl).1
        apply (exact_sections_iff R S).2
        intro W ha hw
        have : Mono ((SheafOfModules.evaluation R (op W)).map f) :=
          (ModuleCat.mono_iff_injective _).2 (hf W ha hw).1
        exact ((S.map (SheafOfModules.evaluation R (op W))).exact_iff_mono
          (by simp [S])).2
          (show Mono ((SheafOfModules.evaluation R (op W)).map f) from inferInstance)
      have he : Epi f := by
        let S := ShortComplex.mk f (0 : B ⟶ B) (by simp)
        apply (S.exact_iff_epi rfl).1
        apply (exact_sections_iff R S).2
        intro W ha hw
        have : Epi ((SheafOfModules.evaluation R (op W)).map f) :=
          (ModuleCat.epi_iff_surjective _).2 (hf W ha hw).2
        exact ((S.map (SheafOfModules.evaluation R (op W))).exact_iff_epi
          (by simp [S])).2
          (show Epi ((SheafOfModules.evaluation R (op W)).map f) from inferInstance)
      exact isIso_of_mono_of_epi f
  · intro K L f
    rw [CochainComplex.mappingCone.quasiIso_iff_acyclic, hacyclic]
    constructor
    · intro h W ha hw
      rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
      exact fun i ↦ (h W ha hw i).of_iso
        (CochainComplex.mappingCone.mapHomologicalComplexIso f
          (SheafOfModules.evaluation R (op W)))
    · intro h W ha hw
      have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic _).1 (h W ha hw)
      exact fun i ↦ (hc i).of_iso
        (CochainComplex.mappingCone.mapHomologicalComplexIso f
          (SheafOfModules.evaluation R (op W))).symm

end AlgebraicGeometry.Scheme.ProEt
