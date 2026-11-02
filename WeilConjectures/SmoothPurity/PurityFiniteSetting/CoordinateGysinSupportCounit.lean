/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData
import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportKernelClass
import WeilConjectures.AlgebraicGeometry.SupportedHomPairAdjunctionNormalization

/-! # Supported global classes and the normalized closed counit

(blueprint: lem-pur-coordinate-gysin-support-counit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The support comparison sends a global exceptional class to its closed counit map.
This assertion concerns the global support comparison, not a section-to-support chart.
Source: latest blueprint, lem-pur-gysin-structure.proof.md, supported-Hom identification;
Milne, Etale Cohomology, Theorem 9.4 and Example 9.5.
(blueprint: lem-pur-coordinate-gysin-support-counit).

Proof: let B be the ordinary etale twist input. On an injective representative of B,
the exceptional right adjoint of exact closed direct image preserves injectives.
Sections of its closed value are the kernel of restriction to the complementary
open; its counit is the inclusion of that kernel. Applying a morphism m to the
constant unit and then this inclusion therefore gives its supported Hom cocycle.
The canonical comparison from the ordinary exceptional value to gysinValue is eK,
and the closed-image mate is d, by heK and hd. Consequently their inverses transport
the ordinary closed counit to map(eK.inv), then d.inv, then nu(boundaryEtaleCounit),
then the nu shift comparison, with exactly the displayed sources and targets.
It remains to identify this kernel calculation with D.comparison.supportIso.
Do this naturally for every bounded-below ordinary etale input, before specializing
to B. Closed adjunction, global evaluation on one, and the etale/pro-etale comparison
identify both sides with Hom from the closed direct image of the constant object,
shifted by minus the cohomological degree. The kernel comparison is normalized by
the same supported-section inclusion as supportIso, by global_first. Their ratio is
therefore an automorphism of this representable functor whose composite with the
forget-support transformation is unchanged. Yoneda identifies it with an
endomorphism of the shifted closed constant object. Forgetting support is
precomposition with the canonical quotient from the ambient constant sheaf to its
closed direct image. Deshift and use full faithfulness of the single-object functor:
that quotient is epimorphic as a sheaf map, so the endomorphism is the identity.
This fixes the comparison in the given degree without assuming shift coherence of
an arbitrary family of support isomorphisms. Hence supportIso sends the global
class of m to the kernel-supported cocycle computed by the closed counit.
For the pro-etale pair use the actual supported object lowerStar(P.constant T).
Its comparison to the generic supported constant normalization is lowerStar.mapIso
of comparisonUpperStarUnitIso. The pair's constantRestriction already includes the
inverse of this unit isomorphism; composition with its hom cancels the inverse.
Thus the transported cocycle satisfies normalization for this precise pair, rather
than silently identifying its supported object with a different constant model.
Apply chi.normalization to the resulting supported cocycle. It sends its class to
the localized Hom cocycle of closed direct image of m followed by the transported
counit. The exact-functor single comparison is inverse at its degree-zero source,
which accounts for the first factor on the right side. Naturality in the resolution
and compatibility of the exact comparisons with shifts remove the representatives.
No section-to-support chart, realization Hom isomorphism, or realization evaluation
formula is used. Zero maps give zero, and the empty base gives zero modules. -/
theorem coordinateGysin_support_counit
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (D : OrientationSupportData P h T)
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h T))
    (eK : (nu P T).obj (P.boundaryEtaleValue h T) ≅ P.gysinValue h T)
    (d : (nu P (Line T)).obj
        ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
          (P.boundaryEtaleValue h T)) ≅
      (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
        ((nu P T).obj (P.boundaryEtaleValue h T)))
    (heK : eK.hom = P.boundaryExceptionalComparison h T)
    (hd : d.hom = P.boundaryImageComparison T ⟨P.boundaryEtaleValue h T, hb⟩)
    (chi : (proEtaleSupportHomPair P (zeroSection T)).Identification)
    (m : P.derivedSheaf h T false ⟶ P.gysinValue h T) :
    (chi.chi (P.gysinInput h T) 2)
      (((D.comparison.supportIso 2).hom.app (P.gysinEtaleInput h T))
        (P.gysinGlobalClass T 2 m)) =
      ((lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constant T) ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map m ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map eK.inv ≫
        d.inv ≫ (nu P (Line T)).map (P.boundaryEtaleCounit h T) ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h T).obj := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  have : LocallyOfFiniteType (lineProjection T) :=
    inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin 1)) T) ↘ T))
  have : IsLocallyNoetherian (Line T) :=
    LocallyOfFiniteType.isLocallyNoetherian (lineProjection T)
  exact (congrArg (chi.chi (P.gysinInput h T) 2)
    (kernel_support_class P h T D.comparison hb eK d heK hd m)).trans
      (supportedHomPairAdjunctionClass_normalization P (zeroSection T) chi
        (P.gysinInput h T) 2 _)

end WeilConjectures.PurityFiniteSetting
