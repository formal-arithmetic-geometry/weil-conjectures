/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The closed support adjunction and internal sheaf Hom

Source: Stacks Project, etale-cohomology.tex, Tag 09XQ and Section 09XP,
localized on each etale object; ILO, Expose XVII, proof of Lemma 7.6.10, p. 313
(blueprint: lem-per-etale-closed-sheaf-internal-adjunction).

Constant-coefficient modules use `Sheaf ... (ModuleCat A)`. Their ordinary internal Hom
is the existing closed tensor-Hom object, equivalently the sheaf of module maps on slices.
The support functor is written as the kernel of the actual open adjunction unit followed
by closed inverse image. The comparison is fixed by evaluation and the support counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]

/-- The bifunctor `(G,F) ↦ Hom(i_*G,F)`, using ordinary internal Hom.
Source: Stacks Tag 09XQ on every slice
(blueprint: lem-per-etale-closed-sheaf-internal-adjunction). -/
def etaleClosedSheafHomSource {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  ((lowerStar (ModuleCat.{u + 1} A) i).op.prod
      (𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) ⋙
    Functor.uncurry.obj MonoidalClosed.internalHom

/-- The bifunctor `(G,F) ↦ i_*Hom(G,i^*ker(F → j_*j^*F))`.
Source: Stacks Tag 09XQ on every slice
(blueprint: lem-per-etale-closed-sheaf-internal-adjunction). -/
def etaleClosedSheafHomTarget {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :=
  ((𝟭 (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))).op.prod
      (kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit ⋙
        upperStar (ModuleCat.{u + 1} A) i)) ⋙
    Functor.uncurry.obj MonoidalClosed.internalHom ⋙ lowerStar (ModuleCat.{u + 1} A) i

/-- The inverse internal-adjunction arrow: push forward evaluation, compose with the
support inclusion, and transpose under tensor-Hom. On each slice this is
`k ↦ i_*k ≫ c_F`. The lax tensor map of direct image is the sectionwise tensor map,
so this specifies all local scalar actions as well as the underlying additive map.
Source: Stacks Tag 09XQ, support factorization and its inverse
(blueprint: lem-per-etale-closed-sheaf-internal-adjunction). -/
def etaleClosedSheafHomComparison {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    (a : lowerStar (ModuleCat.{u + 1} A) i ⊣
      kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit ⋙
        upperStar (ModuleCat.{u + 1} A) i)
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleClosedSheafHomTarget A i j).obj (op G, F) ⟶
      (etaleClosedSheafHomSource A i).obj (op G, F) :=
  (ihom.adjunction ((lowerStar (ModuleCat.{u + 1} A) i).obj G)).homEquiv _ _
    (Functor.LaxMonoidal.μ (lowerStar (ModuleCat.{u + 1} A) i) G
        ((ihom G).obj ((kernel
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit ⋙
            upperStar (ModuleCat.{u + 1} A) i).obj F)) ≫
      (lowerStar (ModuleCat.{u + 1} A) i).map
        ((ihom.ev G).app ((kernel
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit ⋙
            upperStar (ModuleCat.{u + 1} A) i).obj F)) ≫ a.counit.app F)

/-- Closed direct image is exact, its supported right adjoint preserves injectives,
and its internal adjunction is the support adjunction on every etale slice. The
normalization fixes the counit as the support inclusion: the closed unit on the
support kernel, followed by this counit, is the kernel inclusion. The natural
isomorphism's inverse is specified by evaluation and this same counit.

Source: Stacks Project, Tags 09XQ, 09XP and 04CA; ILO Expose XVII, Lemma 7.6.10,
p. 313 (blueprint: lem-per-etale-closed-sheaf-internal-adjunction).

Proof plan, following the seven steps of the DAG node:
1. Forget scalars using lem-weil-pbc-module-sheaves-colimits-forgetful. Kernels,
   direct images, and the inverse-image units are the underlying abelian ones
   (prop-weil-pbc-inverse-image-modules-exact, def-weil-pbc-direct-image).
   The closed unit q on P=ker(id → j_*j^*) is invertible by
   lem-pur-etale-supported-kernel-adjunction. It is module-linear, hence so is
   its inverse. Set c=q^{-1} followed by the kernel inclusion. Exactness of i_*
   is reflected by the faithful exact forgetful functor.
2. The open pullback of i_*G is zero: on W over U its sections are G(empty)=0
   (lem-weil-pbc-etale-inverse-image-restriction, def-weil-pbc-direct-image,
   lem-weil-pbc-etale-composition-cancellation). A map i_*G → F therefore factors
   uniquely through P(F). Compose with q, then use full faithfulness
   (lem-kun-04ca) to transpose it to G → i^*P(F). Its inverse pushes forward
   and composes with c. Both composites are identities. Naturality makes the
   additive bijection commute with constant scalar multiplication; sections of
   the constant ring sheaf are locally constant scalars (def-weil-pbc-constant-sheaf),
   so these are precisely the module-linear maps. This gives the normalized adjunction.
3. An injective I extends maps along i_* of a monomorphism since i_* is exact.
   Transpose the extension back. Naturality shows it extends the original map,
   proving injectivity of i^!_0(I) (def-sp-injective-resolutions).
4. For V etale over X put Z_V=Z×_X V and U_V=U×_X V. Closed immersions and etale
   morphisms are stable under base change (lem-weil-pbc-closed-immersion-base-change,
   lem-weil-pbc-etale-base-change-finite-limits). Etale composition/cancellation
   identifies their sites with the slice sites (def-pur-localized-ringed-site).
   Restriction of i_* and P is sectionwise direct image and the same kernel,
   including scalar actions and kernel inclusions.
5. Compare the restricted q with the q constructed on V. Full faithfulness of i_V*
   gives the unique comparison b between the two supported inverse images, with
   i_V*b=q_V(q|_V)^{-1}. Thus c_V followed after i_V*b is c|_V.
6. On V send h:i_V*G|_ZV → F|_V to its support transpose followed by b^{-1}.
   By def-pur-sheaf-hom this is the desired bijection of internal-Hom sections.
   Its inverse is i_V* of the local map followed by c|_V, exactly the evaluation
   formula etaleClosedSheafHomComparison. The two support-adjunction identities
   prove that both composites are identities.
7. Restrict the inverse formula further to W over V; uniqueness of the support
   factorization proves compatibility with restriction. The same formula gives
   naturality in G and F. All maps are module-linear, so it commutes with every
   local scalar section. Hence the slice bijections form the natural isomorphism.
   No finite generation, finite coefficient ring, or nonempty scheme is used. -/
theorem etale_closed_sheaf_internal_adjunction
    {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} A) i) ∧
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i) ∧
    ∃ a : lowerStar (ModuleCat.{u + 1} A) i ⊣
        kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit ⋙
          upperStar (ModuleCat.{u + 1} A) i,
      (∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
            ((kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit).obj F) ≫
              a.counit.app F =
          (kernel.ι (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit).app F) ∧
      (∀ I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A), Injective I →
        Injective ((kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit ⋙
          upperStar (ModuleCat.{u + 1} A) i).obj I)) ∧
      ∃ e : etaleClosedSheafHomSource A i ≅ etaleClosedSheafHomTarget A i j,
        ∀ (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
          (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
          e.inv.app (op G, F) = etaleClosedSheafHomComparison A i j a G F := by
  sorry

end AlgebraicGeometry.Etale
