module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.Paper.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.ExcellentOfWeaklyEtale
import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.RingTheory.RegularLocalMaximal
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.SmoothColimitRegular
import WeilConjectures.RingTheory.RegularComposition
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.GeometricRegularitySeparableExtension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.RingTheory.RegularBaseChange

/-! # Compatible strict localizations of a regular morphism

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé XVII, 4.3.2.1 and
4.3.2.3–4.3.2.4; Stacks Project, Tags 07C0, 07C1, 06LJ and 06LN.
(blueprint: lem-per-regular-strict-local-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Compatible strict and ordinary localizations preserve regularity, excellence and local
fibre dimensions. The two squares characterize the induced pointed local morphism, including
its dependence on the specified map of geometric points.
Source: ILO, Exposé XVII, 4.3.2.1 and 4.3.2.3–4.3.2.4; Stacks 07C0, 07C1, 06LJ, 06LN.
(blueprint: lem-per-regular-strict-local-model).

Proof:
1. Choose compatible affine neighbourhoods at the geometric points. Their stalk rings R,S
are excellent Noetherian local rings by lem-exc-finite-type-localization-excellent.
The affine-neighbourhood/triples comparison lem-weil-pbc-etale-local-ring-triples and
lem-sbc-etale-triples-localized-strict-henselization identify the chosen strict-local rings
A,B with algebraic strict henselizations. The pair and triple diagrams agree by taking the
kernel of the residue-field pointing. Thus lem-sc-strict-henselization-noetherian makes
A,B Noetherian. Functoriality gives the unique pointed local map A → B over R → S.
2. The triple diagrams express R → A and S → B as filtered colimits of étale algebras.
By lem-weil-pbc-ind-etale-stability these maps are weakly étale. Excellence ascends by
lem-exc-weakly-etale-excellent, since A,B are Noetherian. The multiplication A ⊗[R] A → A
is flat by weak étaleness.
3. The map R → S is regular by lem-weil-pbc-regular-local-maximal. Each étale S-algebra
is smooth, and the fibres of S → B are Noetherian by lem-weil-pbc-fibre-ring-noetherian.
Apply lem-per-smooth-colimit-regular and lem-weil-pbc-regular-composition to get regularity
of S → B and R → B.
4. Base change of the flat R → B makes A → A ⊗[R] B flat. The flat multiplication of A
and lem-per-flat-tensor-scalar-comparison make A ⊗[R] B → A ⊗[A] B ≅ B flat.
Composition proves flatness of A → B.
5. At u in Spec A over p in Spec R, lem-weil-pbc-henselization-finite-separable-fibres
writes A ⊗[R] κ(p) as a finite product of separable algebraic fields Lᵢ. Tensor cancellation
identifies B ⊗[R] κ(p) with B ⊗[A] (A ⊗[R] κ(p)). The coordinate idempotents give its
product decomposition into B ⊗[A] Lᵢ: the maps are coordinate projection and summation.
6. The whole product is geometrically regular over κ(p) by step 3, hence each factor is:
a localization of a finite product is the localization of its selected factor, also after
finite field extension. Apply lem-weil-pbc-geometric-regularity-separable-extension to
pass from κ(p) to Lᵢ. Taking the factor for u proves regularity of A → B.
7. The flat height formula for R → A and S → B, whose local fibres are fields by the
finite separable fibre decomposition, identifies their corresponding local dimensions.
They are finite by lem-weil-pbc-noetherian-local-system-of-parameters.
8. Apply the flat height formula to R → S and A → B, substitute step 7, and cancel
the common finite base dimension. The remaining quotient dimensions agree. The quotients
are the local fibre stalks by lem-sbc-scheme-fibre-stalk-quotient, at every point.
9. For ordinary localizations use the spectra of R,S themselves. Excellence and regularity
were checked in steps 1 and 3. Transitivity of localization identifies the two local fibre
rings with the same quotient of the original stalk ring, proving the dimension equality.
10. A closed subscheme of Spec A is Spec(A/I). The affine fibre-product description gives
Spec(B ⊗[A] A/I) ≅ Spec(B/IB), via b ⊗ (a+I) ↦ ab+IB and b+IB ↦ b ⊗ 1.
Regularity follows from lem-weil-pbc-regular-base-change since A/I is finite type over A.
Both quotients are Noetherian excellent by lem-exc-finite-type-localization-excellent.
The case I = A includes the empty closed subscheme. -/
theorem regular_strict_local_model
    {X Y : Scheme.{u}} (h : Y ⟶ X) [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hY : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U)) [Flat h]
    (hreg : ∀ (x : X) (L : Type u) [Field L] [Algebra (X.residueField x) L]
      [Module.Finite (X.residueField x) L],
      IsRegularScheme (pullback (h.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) L)))))
    {ΩX ΩY : Type u} [Field ΩX] [Field ΩY] [IsAlgClosed ΩX] [IsAlgClosed ΩY]
    (barX : Spec (.of ΩX) ⟶ X) (barY : Spec (.of ΩY) ⟶ Y) (e : ΩX →+* ΩY)
    (hbar : barY ≫ h = Spec.map (CommRingCat.ofHom e) ≫ barX) :
    ∃! H : Scheme.strictHenselizationScheme barY ⟶ Scheme.strictHenselizationScheme barX,
      (H ≫ Scheme.strictHenselizationStructuralMap barX =
        Scheme.strictHenselizationStructuralMap barY ≫ h) ∧
      (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation barY)) ≫ H =
        Spec.map (CommRingCat.ofHom e) ≫
          Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation barX))) ∧
      IsLocalHom H.appTop.hom ∧
      Flat H ∧
      (∀ (u₀ : Scheme.strictHenselizationScheme barX) (L : Type u) [Field L]
        [Algebra ((Scheme.strictHenselizationScheme barX).residueField u₀) L]
        [Module.Finite ((Scheme.strictHenselizationScheme barX).residueField u₀) L],
        IsRegularScheme (pullback (H.fiberToSpecResidueField u₀)
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((Scheme.strictHenselizationScheme barX).residueField u₀) L))))) ∧
      IsNoetherian (Scheme.strictHenselizationScheme barX) ∧
      IsNoetherian (Scheme.strictHenselizationScheme barY) ∧
      (∀ U : (Scheme.strictHenselizationScheme barX).affineOpens,
        IsExcellent Γ(Scheme.strictHenselizationScheme barX, U)) ∧
      (∀ V : (Scheme.strictHenselizationScheme barY).affineOpens,
        IsExcellent Γ(Scheme.strictHenselizationScheme barY, V)) ∧
      (∀ v : Scheme.strictHenselizationScheme barY,
        ringKrullDim ((H.fiber (H v)).presheaf.stalk (H.asFiber v)) =
          ringKrullDim ((h.fiber
            (h (Scheme.strictHenselizationStructuralMap barY v))).presheaf.stalk
            (h.asFiber (Scheme.strictHenselizationStructuralMap barY v)))) ∧
      (∀ (C : Scheme.{u}) (i : C ⟶ Scheme.strictHenselizationScheme barX)
        [IsClosedImmersion i],
        Flat (pullback.snd H i) ∧
        (∀ (c : C) (L : Type u) [Field L] [Algebra (C.residueField c) L]
          [Module.Finite (C.residueField c) L],
          IsRegularScheme (pullback ((pullback.snd H i).fiberToSpecResidueField c)
            (Spec.map (CommRingCat.ofHom (algebraMap (C.residueField c) L))))) ∧
        IsNoetherian (pullback H i) ∧ IsNoetherian C ∧
        (∀ U : (pullback H i).affineOpens, IsExcellent Γ(pullback H i, U)) ∧
        (∀ V : C.affineOpens, IsExcellent Γ(C, V))) ∧
      (∀ y₀ : Y,
        Flat (Spec.map (h.stalkMap y₀)) ∧
        (∀ (u₀ : Spec (X.presheaf.stalk (h y₀))) (L : Type u) [Field L]
          [Algebra ((Spec (X.presheaf.stalk (h y₀))).residueField u₀) L]
          [Module.Finite ((Spec (X.presheaf.stalk (h y₀))).residueField u₀) L],
          IsRegularScheme (pullback ((Spec.map (h.stalkMap y₀)).fiberToSpecResidueField u₀)
            (Spec.map (CommRingCat.ofHom
              (algebraMap ((Spec (X.presheaf.stalk (h y₀))).residueField u₀) L))))) ∧
        IsNoetherian (Spec (X.presheaf.stalk (h y₀))) ∧
        IsNoetherian (Spec (Y.presheaf.stalk y₀)) ∧
        (∀ U : (Spec (X.presheaf.stalk (h y₀))).affineOpens,
          IsExcellent Γ(Spec (X.presheaf.stalk (h y₀)), U)) ∧
        (∀ V : (Spec (Y.presheaf.stalk y₀)).affineOpens,
          IsExcellent Γ(Spec (Y.presheaf.stalk y₀), V)) ∧
        ∀ v : Spec (Y.presheaf.stalk y₀),
          ringKrullDim (((Spec.map (h.stalkMap y₀)).fiber
            ((Spec.map (h.stalkMap y₀)) v)).presheaf.stalk
              ((Spec.map (h.stalkMap y₀)).asFiber v)) =
            ringKrullDim ((h.fiber (h (Y.fromSpecStalk y₀ v))).presheaf.stalk
              (h.asFiber (Y.fromSpecStalk y₀ v)))) := by
  sorry

end AlgebraicGeometry
