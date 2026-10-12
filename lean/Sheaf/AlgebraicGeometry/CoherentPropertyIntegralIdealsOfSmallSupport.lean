/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion
import Sheaf.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
import Sheaf.Paper.SchemeTheoreticSupport
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# The integral-support induction step for coherent devissage

Source: Stacks Project, Cohomology of Schemes, Lemma 01YL.
(blueprint: lem-weil-pbc-coherent-property-integral-ideals-of-small-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The generic-point patching step of higher-rank coherent devissage: assuming the
property for coherent modules supported on this integral closed subscheme and vanishing
at its generic point, the distinguished module gives the property for every ideal.

Source: Stacks Project, Cohomology of Schemes, Lemma 01YL, third paragraph and its end,
with the explicit zero hypothesis needed for the zero ideal.
(blueprint: lem-weil-pbc-coherent-property-integral-ideals-of-small-support)

Proof:
1. Extension closure and P(0) give isomorphism invariance: use 0 → 0 → F → G → 0
for an isomorphism F ≅ G of coherent modules. All proper-support cokernels below have
P by hsmall; no induction on smaller integral subschemes is needed in this lemma.
2. Generic-point uniqueness identifies ξ with i(η). Apply the generic-point
ideal-inclusion lemma to G. It embeds a finite direct sum of
a coherent ideal I on Z into G, isomorphically near ξ. The nonzero generic stalk of G
forces both I nonzero and the number r of summands positive. Pushforward commutes with
finite sums. For every nonzero ideal I' contained in I, compose the sum of its inclusions
with this embedding to obtain a mono β : (i_* I')^{⊕ r} → G, bijective at ξ.
3. Its coherent cokernel Q is supported in i(Z) and misses ξ. The annihilator J of Q is
quasi-coherent and coherent: it is the kernel of the structure-sheaf quotient for its
closed subscheme, whose structure sheaf has coherent finite pushforward. On the open
complement of Supp(Q), all stalks of Q vanish, so Q restricts to zero by stalk detection.
Its annihilator is the unit ideal there; in particular J has full stalk at ξ.
Moreover JG is contained in the image of β: multiplication
by J followed by the cokernel map is zero. Apply hG to J to get G' contained in JG, with
full generic stalk and P(G'). Pull it back through the mono β. The resulting coherent
submodule H of (i_* I')^{⊕ r} is isomorphic to G'. Its cokernel misses ξ and is supported
in i(Z), hence has P by hsmall. Extension closure gives P((i_* I')^{⊕ r}); hP_sum gives
P(i_* I').
4. For an arbitrary nonzero ideal I'', the intersection I'' ∩ I is nonzero: on a nonempty
affine open the product of nonzero sections is nonzero since Z is integral. Apply step 3
to this intersection. The inclusion into I'' is generically an isomorphism, so its coherent
pushforward cokernel misses ξ and has P by hsmall. Extension closure gives P(i_* I'').
All ideal modules and their pushforwards are coherent, since the source is locally
Noetherian and closed pushforward is finite. For the zero ideal its pushforward is zero;
isomorphism invariance and hP_zero finish.
-/
theorem coherent_property_integral_ideals_of_small_support
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : P (0 : X.Modules))
    (hP_ext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hP_sum : ∀ (F : X.Modules) (r : ℕ),
      RingedSpace.IsCoherent X.toRingedSpace F → 1 ≤ r →
      P (@biproduct (Fin r) X.Modules _ _ (fun _ : Fin r ↦ F)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ F))) → P F)
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (hsmall : ∀ Q : X.Modules, RingedSpace.IsCoherent X.toRingedSpace Q →
      {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊆ Set.range i.base →
      Subsingleton (Q.presheaf.stalk ξ) → P Q)
    (hG :
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        ({x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base) ∧
        (∀ g : X.presheaf.stalk ξ, ∀ m : (RingedSpace.moduleStalkFunctor
          X.toRingedSpace ξ).obj G, g ∈ IsLocalRing.maximalIdeal _ → g • m = 0) ∧
        ∀ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
          [Mono ι] [J.IsQuasicoherent],
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom →
          ∃ G' : Subobject G,
            RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
            (∃ h : (G' : X.Modules) ⟶ idealModuleProduct ι G,
              G'.arrow = h ≫ idealModuleProductι ι G) ∧
            Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
              G'.arrow).hom ∧ P (G' : X.Modules)) :
    ∀ I : Z.IdealSheafData, P ((pushforward i).obj I.toModules) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
