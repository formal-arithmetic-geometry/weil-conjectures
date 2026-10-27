/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.QuotSMulTop
public import WeilConjectures.Mathlib.Algebra.Module.Torsion
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Principal supported-section quotients

Source: Stacks Project, Divisors, Tag 080W, algebra paragraph, and
Definition 080D (1); Schemes, Tags 01HV and 01I7
(blueprint: lem-trf-principal-support-quotient-exact).

The auxiliary maps are the actual open-restriction unit, its kernel, and its
cokernel. Torsion and its quotient maps are the existing upstream constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- Restriction to `D(a)` followed by open direct image.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalSupportRestriction (a : R) (N : ModuleCat.{u} R) :=
  (Scheme.Modules.restrictAdjunction
    (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen a))).unit.app (tilde N)

/-- The kernel inclusion defining the supported-section subsheaf `K`.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalSupportι (a : R) (N : ModuleCat.{u} R) :
    kernel (principalSupportRestriction a N) ⟶ tilde N :=
  kernel.ι (principalSupportRestriction a N)

/-- The module-sheaf quotient `Q = N~/K`, taken in the abelian sheaf category.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalSupportQuotient (a : R) (N : ModuleCat.{u} R) : (Spec R).Modules :=
  cokernel (principalSupportι a N)

/-- The canonical quotient map from `N~` to `Q`.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalSupportπ (a : R) (N : ModuleCat.{u} R) :
    tilde N ⟶ principalSupportQuotient a N :=
  cokernel.π (principalSupportι a N)

/-- The map on supported kernels induced by the naturality of open restriction.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalSupportKernelMap (a : R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    kernel (principalSupportRestriction a M) ⟶ kernel (principalSupportRestriction a N) :=
  kernel.map _ _ (tilde.map f)
    (((Scheme.Modules.restrictFunctor (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen a))) ⋙
      Scheme.Modules.pushforward
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen a))).map (tilde.map f))
    ((Scheme.Modules.restrictAdjunction
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen a))).unit.naturality
      (tilde.map f)).symm

/-- The canonical map on supported-section quotients induced by an `R`-linear map.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalSupportQuotientMap (a : R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    principalSupportQuotient a M ⟶ principalSupportQuotient a N :=
  cokernel.map _ _ (principalSupportKernelMap a f) (tilde.map f)
    (kernel.lift_ι _ _ _).symm

/-- The sheafification of the actual inclusion of power torsion.
Source: Stacks Project, Tag 080W, algebra paragraph; Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalTorsionι (a : R) (N : ModuleCat.{u} R) :
    tilde (ModuleCat.of R (Submodule.powTorsion R N a)) ⟶ tilde N :=
  tilde.map (ModuleCat.ofHom (Submodule.powTorsion R N a).subtype)

/-- The quotient module `N/Γ_(a)(N)`, using the existing submodule quotient.
Source: Stacks Project, Tag 080W, algebra paragraph
(blueprint: lem-trf-principal-support-quotient-exact). -/
abbrev principalTorsionQuotient (a : R) (N : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (N ⧸ Submodule.powTorsion R N a)

/-- The existing upstream torsion quotient map specialized to powers of `a`.
Source: Stacks Project, Tag 080W, algebra paragraph
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalTorsionQuotientMap (a : R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    principalTorsionQuotient a M ⟶ principalTorsionQuotient a N :=
  ModuleCat.ofHom (Submodule.torsion'QuotientMap (Submonoid.powers a) f.hom)

/-- Restriction of a linear map to its power-torsion submodules.
Source: Stacks Project, Tag 080W, algebra paragraph
(blueprint: lem-trf-principal-support-quotient-exact). -/
def principalTorsionMap (a : R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.of R (Submodule.powTorsion R M a) ⟶
      ModuleCat.of R (Submodule.powTorsion R N a) :=
  ModuleCat.ofHom ((f.hom.domRestrict (Submodule.powTorsion R M a)).codRestrict
    (Submodule.powTorsion R N a) (fun x ↦ by
      obtain ⟨s, hs⟩ := x.property
      refine ⟨s, ?_⟩
      change (s : R) • f x.val = 0
      simpa only [Submonoid.smul_def, map_smul, map_zero] using (congrArg f hs)))

/-- The categorical supported kernel has exactly the sections specified by the node.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact).

Proof: Kernels of module sheaves are computed sectionwise. The component of the
open-restriction adjunction unit is restriction to the intersection with the open.
Thus the image of its kernel inclusion consists precisely of the sections whose
restriction vanishes. This is the sectionwise description used in proof Step 2. -/
theorem principalSupport_section_kernel (a : R) (N : ModuleCat.{u} R)
    (W : (Spec R).Opens) :
    Set.range ((principalSupportι a N).app W) =
      {x | (tilde N).presheaf.map
        (homOfLE (inf_le_left : W ⊓ PrimeSpectrum.basicOpen a ≤ W)).op x = 0} := by
  sorry

/-- On every principal open, supported sections are power torsion and the injective
localized image of the original power-torsion submodule.
Source: Stacks Project, Definition 080D (1), Tags 080W, 01HV and 00CS
(blueprint: lem-trf-principal-support-quotient-exact).

Proof: Step 1 identifies tilde's maps on principal opens with localization of linear
maps. In Step 2 restriction from D(s) to D(s) intersect D(a) is the localization
N_s to N_sa. Apply the power-torsion-kernel-localization lemma over R_s. The
power-torsion-localization lemma identifies this with the localized image of T.
Exactness of localization makes T_s to N_s injective. The section module used here
is canonically N_s by tilde.toOpen; scalar multiplication by a is multiplication
by a/1 over R_s, so the displayed existential is exactly Γ_(a/1)(N_s). -/
theorem principalSupport_basicOpen (a : R) (N : ModuleCat.{u} R) (s : R) :
    Function.Injective ((principalTorsionι a N).app (PrimeSpectrum.basicOpen s)) ∧
    Set.range ((principalTorsionι a N).app (PrimeSpectrum.basicOpen s)) =
      Set.range ((principalSupportι a N).app (PrimeSpectrum.basicOpen s)) ∧
    Set.range ((principalSupportι a N).app (PrimeSpectrum.basicOpen s)) =
      {x | ∃ n : ℕ, a ^ n • x = 0} := by
  sorry

/-- Natural identifications `K = T~` as submodules and `Q ≅ (N/T)~`, with the actual
inclusions, quotient maps, and the naturality squares for every linear map.
Source: Stacks Project, Definition 080D (1), Tags 080W, 01HV and 01I7
(blueprint: lem-trf-principal-support-quotient-exact).

Proof: Step 1: the tilde functor preserves finite limits by
lem-sc-tilde-preserves-finite-limits and colimits by its affine tilde/Gamma
adjunction. Step 2: the basic-open calculation gives the same submodule on a basis,
hence the sheaf property identifies K with T~, compatibly with their inclusions.
This identification is a morphism of sheaves and therefore commutes with every
restriction. Every linear map preserves power torsion and the restriction kernel,
so cancellation of the kernel inclusion gives its naturality square.
Step 3: apply the exact tilde functor to T to N to N/T. The sheafified quotient
is a cokernel of the inclusion of K, hence the unique compatible isomorphism
from Q. Cancel the epimorphism N~ to Q to prove the naturality square. -/
theorem principalSupport_comparison (a : R) :
    ∃ (e : ∀ N : ModuleCat.{u} R,
        tilde (ModuleCat.of R (Submodule.powTorsion R N a)) ≅
          kernel (principalSupportRestriction a N))
      (θ : ∀ N : ModuleCat.{u} R,
        principalSupportQuotient a N ≅ tilde (principalTorsionQuotient a N)),
      (∀ N : ModuleCat.{u} R,
        (e N).hom ≫ principalSupportι a N = principalTorsionι a N) ∧
      (∀ (M N : ModuleCat.{u} R) (f : M ⟶ N),
        tilde.map (principalTorsionMap a f) ≫ (e N).hom =
          (e M).hom ≫ principalSupportKernelMap a f) ∧
      (∀ N : ModuleCat.{u} R,
        principalSupportπ a N ≫ (θ N).hom =
          tilde.map (ModuleCat.ofHom (Submodule.powTorsion R N a).mkQ)) ∧
      (∀ (M N : ModuleCat.{u} R) (f : M ⟶ N),
        principalSupportπ a M ≫ principalSupportQuotientMap a f =
          tilde.map f ≫ principalSupportπ a N) ∧
      (∀ (M N : ModuleCat.{u} R) (f : M ⟶ N),
        principalSupportQuotientMap a f ≫ (θ N).hom =
          (θ M).hom ≫ tilde.map (principalTorsionQuotientMap a f)) := by
  sorry

/-- Powerwise injectivity gives the short exact torsion-quotient sequence, its
associated-sheaf sequence, and the identified supported-section quotient sequence.
Source: Stacks Project, Tag 080W, final algebra paragraph; Definition 080D (1)
(blueprint: lem-trf-principal-support-quotient-exact).

Proof: Step 4: a linear map preserves power torsion, giving the coset formulas.
If i(y) is power torsion, injectivity of i makes y power torsion. Surjectivity
of j supplies representatives of every target quotient class.
Step 5: if j(x) is killed by a^n, write i(y)=a^n x by exactness. The powerwise
injectivity assumption forces y=a^n z. Thus a^n(x-i(z))=0, and the class of x
is the image of the class of z. Conversely the composite vanishes since ji=0.
This includes n=0. The element to subtract is i(z), correcting the final variable
error in the printed Stacks proof.
Step 6: tilde is exact by finite-limit preservation and the affine tilde/Gamma
adjunction's colimit preservation. Apply it to this short exact sequence.
The comparison theorem's naturality squares for i and j identify its arrows
with the induced Q arrows. Hence the Q sequence is short exact as well.
Neither localization nor this calculation requires a regular element, finiteness,
or a nonzero ring. -/
theorem principalSupportQuotient_exact (a : R) {N₁ N₂ N₃ : ModuleCat.{u} R}
    (i : N₁ ⟶ N₂) (j : N₂ ⟶ N₃)
    (hi : Function.Injective i) (hij : Function.Exact i j) (hj : Function.Surjective j)
    (hpow : ∀ n : ℕ, Function.Injective (QuotSMulTop.map (a ^ n) i.hom)) :
    Function.Injective (principalTorsionQuotientMap a i) ∧
    Function.Exact (principalTorsionQuotientMap a i) (principalTorsionQuotientMap a j) ∧
    Function.Surjective (principalTorsionQuotientMap a j) ∧
    (∀ y : N₁, principalTorsionQuotientMap a i (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (i y)) ∧
    (∀ x : N₂, principalTorsionQuotientMap a j (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (j x)) ∧
    (∃ h : tilde.map (principalTorsionQuotientMap a i) ≫
        tilde.map (principalTorsionQuotientMap a j) = 0,
      (ShortComplex.mk (tilde.map (principalTorsionQuotientMap a i))
        (tilde.map (principalTorsionQuotientMap a j)) h).ShortExact) ∧
    (∃ h : principalSupportQuotientMap a i ≫ principalSupportQuotientMap a j = 0,
      (ShortComplex.mk (principalSupportQuotientMap a i)
        (principalSupportQuotientMap a j) h).ShortExact) := by
  sorry

end AlgebraicGeometry
