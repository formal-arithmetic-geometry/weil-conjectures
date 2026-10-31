/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.ExceptionalSupportDomain
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenMateNormalization

/-! # Compact-support comparison after total limit

Source: Zheng, Construction 5.25; the actual open reduction mate and proper limit comparison.
(blueprint: lem-sf-exceptional-support-limit-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

/-- Compare the actual support system with the recorded integral functor after limit.
The comparison is constructed, rather than selected from an existence theorem.
Proof: whisker the actual open reduction mate by the finite-Tor inclusion and apply
limit. Compose with the inverse actual unit of the integral open extension; both
are invertible by open reconstruction on the support domain. Precede this by the
proper limit comparison and follow it by the recorded compact-support realization.
Naturality is preserved by whiskering and composition. Inverses are uniquely fixed
by the displayed maps. Zero inputs and empty opens require no separate choices.
Source: Zheng, Construction 5.25; Stacks Tags 0941 and 0D6E.
(blueprint: lem-sf-exceptional-support-limit-comparison) -/
def finiteTorSupportLimitComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (finiteTorConstructibleIntegral l E X).ι ⋙ (calculus l E X).reduction ⋙
      Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ⋙
        coefficientSequenceLimit l E Y ≅
    PurCompactSupport.finiteTorIntegralInclusion l E X ⋙
      sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⋙
          (sfIntegralConstructible l E Y).ι := by
  let P := finiteTorConstructibleIntegral l E X
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hx : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using (PurCompactSupport.coefficientPrimeUnit l D hl).map
      ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop).hom
  have hz : IsUnit (l : Γ(c.Z, ⊤)) := by
    simpa only [map_natCast] using (PurCompactSupport.coefficientPrimeUnit l D hl).map
      ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (c.g ≫ (Y ↘ Spec (.of D.k))).appTop).hom
  have hopen (K : P.FullSubcategory) :=
    integralOpenMateNormalization l E o m c.i hx hz K.obj K.property.1
      (basicSupportDomain_of_constructible l E D hl o c K.obj K.property.1).1.2.1
      (basicSupportDomain_of_constructible l E D hl o c K.obj K.property.1).2
  let r := Functor.whiskerLeft P.ι (m.openReduction l E c.i)
  have : ∀ K, IsIso (r.app K) := fun K ↦ (hopen K).2
  let η := Functor.whiskerLeft (P.ι ⋙ ringedOpen l E c.i)
    (calculus l E c.Z).adjunction.unit
  have : ∀ K, IsIso (η.app K) := fun K ↦ (hopen K).1
  let openIso := Functor.isoWhiskerRight
    (NatIso.ofComponents (fun K ↦ asIso (r.app K)) (fun v ↦ r.naturality v))
    (coefficientSequenceLimit l E c.Z) ≪≫
      (NatIso.ofComponents (fun K ↦ asIso (η.app K)) (fun v ↦ η.naturality v)).symm
  exact Functor.isoWhiskerLeft
      (P.ι ⋙ (calculus l E X).reduction ⋙ Operations.shriek l E o c.i)
      (m.push l E c.g) ≪≫
    Functor.isoWhiskerRight openIso (ringedPush l E c.g) ≪≫
    Functor.isoWhiskerLeft (PurCompactSupport.finiteTorIntegralInclusion l E X)
      (sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c)

end WeilConjectures.IntegralSystemRealization
