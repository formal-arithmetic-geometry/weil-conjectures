/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons

import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.DerivedCategories
/-!
# Exceptional adjunction on the comparison class

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-existence,
thm-sf-ambient-adjoint-class.md (blueprint: thm-sf-ambient-adjoint-class).

The interface retains the natural Hom equivalences and the compactification comparisons.
The right functor is written as the specified comparison composite, without an ambient
pro-etale adjunction hypothesis. A single etale right adjoint normalizes the right functors
for all compactifications; compatibility of the Hom equivalences characterizes the left
comparisons, and the right comparisons are identities in this normalization. The left
comparisons are required to equal the existing canonical comparison on every
bounded-below étale representative, rather than being chosen as a free coherent family.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The relative adjunction and its coherent compactification comparisons, with the right
functor normalized to `nu_X^* G Rnu_Y,*`. `P` and `Q` specify precisely the allowed inputs
and targets. For the finite coefficient ring `Λ`, the comparison components must equal
`fixedCompactSupportOriginIso`, the existing transport of the
canonical étale comparisons. The Hom bijection at `c₀` must be the transport of `adj` by
the fixed compact-support comparison and derived comparison adjunction. The datum also
includes preservation of bounded-below complexes by the transported right functor.
Source: Weil blueprint, thm-sf-ambient-adjoint-class.md, clauses (2)--(3)
(blueprint: thm-sf-ambient-adjoint-class). -/
structure ComparisonClassAdjunction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (c₀ : Compactification f)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)
    (P : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))))
    (Q : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))) where
  /-- The transported ordinary right adjoint preserves bounded-below complexes. -/
  boundedBelow (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
      (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    _root_.DerivedCategory.TStructure.t.plus
      ((R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙
        D(ν^*(X)[ModuleCat.{u + 1} Λ])).obj L)
  /-- The adjunction bijections for each compactification and each allowed pair. -/
  homEquiv (c : Compactification f) (K) (hK : P K) (L) (hL : Q L) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K ⟶ L) ≃
      (K ⟶ (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])).obj L)
  /-- At the chosen compactification, the Hom bijection is the transported chosen
  étale adjunction, through the fixed compact-support and site comparisons. -/
  homEquiv_normalized
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hK : P (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj)) (L) (hL : Q L)
      (a : (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c₀).obj K.obj ⟶
        R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L) :
    homEquiv c₀ (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj) hK L hL
        ((fixedCompactSupportComparisonIso
            Λ c₀).hom.app K ≫
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).symm a) =
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).map ((adj.homEquiv K.obj _) a)
  /-- Naturality with respect to every morphism between allowed inputs. -/
  naturality_left (c : Compactification f) (K K') (hK : P K) (hK' : P K')
      (L) (hL : Q L) (a : K ⟶ K')
      (b : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K' ⟶ L) :
    homEquiv c K hK L hL
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map a ≫ b) =
      a ≫ homEquiv c K' hK' L hL b
  /-- Naturality with respect to every morphism between allowed targets. -/
  naturality_right (c : Compactification f) (K) (hK : P K)
      (L L') (hL : Q L) (hL' : Q L')
      (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K ⟶ L)
      (b : L ⟶ L') :
    homEquiv c K hK L' hL' (a ≫ b) =
      homEquiv c K hK L hL a ≫
        (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])).map b
  /-- Compactification comparisons on exactly the permitted input class. -/
  comparison (c d : Compactification f) :
    P.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
      P.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d
  /-- On every étale-origin input, the comparison is the canonical étale comparison
  transported through `ν^*`; this fixes the comparison rather than allowing scalar twists. -/
  comparison_normalized (c d : Compactification f)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hK : P (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj)) :
    (comparison c d).hom.app ⟨D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj, hK⟩ =
      (fixedCompactSupportOriginIso Λ c d).hom.app K
  /-- Comparing a compactification with itself gives the identity. -/
  comparison_refl (c : Compactification f) : comparison c c = Iso.refl _
  /-- The comparison isomorphisms satisfy the cocycle condition. -/
  comparison_trans (c d e : Compactification f) :
    comparison c e = comparison c d ≪≫ comparison d e
  /-- The comparisons identify the Hom bijections; this determines their components. -/
  comparison_homEquiv (c d : Compactification f) (K) (hK : P K) (L) (hL : Q L)
      (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d).obj K ⟶ L) :
    homEquiv c K hK L hL ((comparison c d).hom.app ⟨K, hK⟩ ≫ a) =
      homEquiv d K hK L hL a

/-- The etale exceptional adjoint, transported by comparison, is the exceptional adjoint
relative to bounded-below etale-origin inputs, with uniform class-restricted vanishing
and coherent compactification comparisons.
Source: Weil blueprint, thm-sf-ambient-adjoint-class.md, clauses (1)--(3)
(blueprint: thm-sf-ambient-adjoint-class).

Proof: apply thm-sf-fullcd-class to the proper part of the chosen compactification to get
the bound `2*d`, including every pro-etale base change. Choose the ordinary etale right
adjoint by Brown representability (thm-amb-etale-exceptional-adjoint). For `K = nu_X^* K'`
with `K'` bounded below, use the compact-support comparison, the comparison adjunction,
the etale exceptional adjunction, and full faithfulness of `nu_X^*` on bounded-below
complexes, in that order. Finite cohomological amplitude ensures that the etale right
adjoint preserves bounded-below objects. All four Hom identifications are natural.
The normalization equation at the chosen compactification records this chain against
the chosen étale adjunction.
Etale compactification independence transports the bijections to every compactification.
Use the existing `fixedCompactSupportOriginIso` on every
étale representative, then descend along full faithfulness and essential image to `P`.
This gives the normalization equation; the existing étale identity and cocycle laws
give the two coherence equations. Compatibility with the Hom bijections follows from
the same comparison/adjunction chain. This uses no all-sheaf cohomological bound or
ambient pro-etale adjunction, and makes no assertion about preservation of constructibility
or finite Tor amplitude. -/
theorem exists_comparisonClassAdjunction
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    HasCohomologicalDimensionLEOnEtaleOrigin
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c.g (2 * d) ∧
      ∃ G : _root_.DerivedCategory
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) ⥤
        _root_.DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))),
        ∃ adj : Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c ⊣ G,
        Nonempty (@ComparisonClassAdjunction
          (Padic.coefficientExtensionRing l E n) inferInstance
          (Padic.finite_coefficientExtensionRing l E n _hn) X Y f inferInstance c G adj
          (DerivedCategory.plusEtaleOrigin
            (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X)
          _root_.DerivedCategory.TStructure.t.plus) := by
  sorry

end AlgebraicGeometry.ProEtale
