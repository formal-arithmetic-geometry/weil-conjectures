module

public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import Sheaf.RingTheory.RelativeMPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import Sheaf.AlgebraicGeometry.AffineMPseudoCoherentCriterion
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Relative degreewise pseudo-coherence and affine derived sections

Source: Stacks Project, More on Morphisms, Tag 09VF,
lemma-qcoh-relative-pseudo-coherence-characterize, equivalence (1)--(3)
(blueprint: lem-sfb-relative-m-pseudocoherence-derived-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u w wA

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Relative degreewise pseudo-coherence is detected by module-valued derived sections
on an affine covering, equivalently on every affine source/base pair. The algebra action
is the one induced by `f.appLE`; `U.topIso` identifies the global functions of the open
subscheme with the functions on `U`. Derived global sections is the unbounded right
derived functor of module-valued global sections, as in the affine derived equivalence.

Source: Stacks Project, More on Morphisms, Tag 09VF,
lemma-qcoh-relative-pseudo-coherence-characterize
(blueprint: lem-sfb-relative-m-pseudocoherence-derived-sections).

Proof:
1. For an affine pair U over V, locally finite type gives a finite type algebra of
   sections (lem-weil-pbc-lft-affine-pairs). Choose a finite polynomial presentation.
   Its surjection corresponds to a closed embedding in finite affine space over V
   (def-nagata-relative-affine-space, def-weil-closed-immersion).
2. The affine derived equivalence (lem-pc-affine-qcoh-derived-equivalence) represents
   E restricted to U by a termwise associated-sheaf complex of its derived sections M.
   Resolve that complex by a K-injective complex to compute the closed pushforward
   (def-pc-ringed-spaces-derived-direct-image). Since the embedding is affine,
   lem-pc-affine-pushforward-resolution-quasi-iso identifies that pushforward with the
   termwise pushforward of the associated-sheaf complex. By
   lem-weil-pbc-pushforward-tilde-spec this is the associated-sheaf complex of M with
   scalars restricted along the polynomial presentation, compatibly with differentials.
3. Apply lem-sfb-affine-m-pseudocoherent-criterion to that derived isomorphism.
   The absolute approximation condition is invariant under isomorphism. Taking the
   existential quantifier over polynomial presentations gives exactly
   def-sfb-ring-relative-m-pseudocoherent, using the same presentation on both sides.
4. Apply this comparison to the covers defining
   def-sfb-relative-pseudo-coherent-complex to obtain (1) iff (2).
   The all-charts criterion lem-sfb-relative-pseudocoherence-all-affine-charts gives
   (1) implies (3). Choosing affine covers by lem-weil-pbc-affine-opens-basis gives
   (3) implies (2). All choices are for the fixed integer m; no global bound is used.
-/
theorem relative_mPseudoCoherence_derivedSections_tfae
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ (R : Type u) [CommRing R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) (m : ℤ) :
    List.TFAE [
      IsMPseudoCoherentRelativeTo f m E,
      (∀ s : S, ∃ V : S.Opens, ∃ hV : IsAffineOpen V, s ∈ V ∧
        ∀ x : X, f x ∈ V → ∃ U : X.Opens, ∃ hU : IsAffineOpen U, x ∈ U ∧
          ∃ hUV : U ≤ f ⁻¹ᵁ V,
            @DerivedCategory.IsMPseudoCoherentRelativeTo Γ(S, V) Γ(X, U) _ _
              ((f.appLE V U hUV).hom.toAlgebra) (f.finiteType_appLE hV hU hUV)
              _ _ m
              ((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
                ModuleCat.restrictScalars U.topIso.inv.hom).rightDerivedFunctor.obj
                  ((derivedPullback U.ι).obj E))),
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
          (hUV : U ≤ f ⁻¹ᵁ V),
        @DerivedCategory.IsMPseudoCoherentRelativeTo Γ(S, V) Γ(X, U) _ _
          ((f.appLE V U hUV).hom.toAlgebra) (f.finiteType_appLE hV hU hUV)
          _ _ m
          ((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
            ModuleCat.restrictScalars U.topIso.inv.hom).rightDerivedFunctor.obj
              ((derivedPullback U.ι).obj E)))] := by
  sorry

end AlgebraicGeometry.Scheme
