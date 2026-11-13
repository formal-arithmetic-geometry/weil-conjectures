/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete

/-! # Constant coefficients and local power-torsion towers

We use the existing coefficient-sized small model of the unchanged small pro-etale site.
It is equivalent via AsSmall.down to X.ProEt; its topology is the induced topology.
Thus this changes sizes only, not objects, covers, slices, or coefficient sheaves up to
canonical equivalence. Local completeness is the existing slice internal-Hom definition.
The extended ideal is constructed as the kernel of the constant quotient map.

## References

* [Stacks Project, Tag 099P](https://stacks.math.columbia.edu/tag/099P)
* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 03DA](https://stacks.math.columbia.edu/tag/03DA)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The constant commutative coefficient sheaf on the recorded small model. -/
abbrev torsionCompletionRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (constantSheaf (coefficientProEtaleModelTopology.{t, u} X)
    CommRingCat.{max u (t + 1)}).obj (CommRingCat.of (ULift.{t + 1} A))

/-- Forget commutativity of the constant ring sheaf, retaining the actual ring sheaf. -/
abbrev torsionCompletionModuleRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (torsionCompletionRing X A)

/-- The module-sheaf category on this model is precisely the recorded ringed-site category. -/
abbrev TorsionCompletionModules (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  ringedSiteModules.{max u (t + 1)} (torsionCompletionModuleRing X A)

/-- The constant quotient morphism, obtained by sheafifying the actual quotient ring map. -/
def torsionCompletionQuotient (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    torsionCompletionModuleRing X A ⟶ torsionCompletionModuleRing X (A ⧸ I) :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))))

/-- The quotient ring as a module over the constant original ring. -/
abbrev torsionCompletionQuotientModule (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :=
  (SheafOfModules.restrictScalars (torsionCompletionQuotient X I)).obj
    (SheafOfModules.unit (torsionCompletionModuleRing X (A ⧸ I)))

/-- The unit sections of the quotient ring form a global section of its module sheaf. -/
def torsionCompletionQuotientOne (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) : (torsionCompletionQuotientModule X I).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (1 : (torsionCompletionModuleRing X (A ⧸ I)).obj.obj U))
    (fun {_ _} f ↦ ((torsionCompletionModuleRing X (A ⧸ I)).obj.map f).hom.map_one)

/-- The quotient map on modules sends the unit generator to one, hence sends a to its
quotient image. No arbitrary map is chosen. -/
def torsionCompletionQuotientMap (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    SheafOfModules.unit (torsionCompletionModuleRing X A) ⟶
      torsionCompletionQuotientModule X I :=
  (SheafOfModules.unitHomEquiv _).symm (torsionCompletionQuotientOne X I)

/-- The extended ideal I A is the kernel of A → A/I as module sheaves. Constant
sheafification is exact, so this is the ideal generated locally by the constants in I. -/
def torsionCompletionIdeal (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    TorsionCompletionModules X A :=
  kernel (torsionCompletionQuotientMap X I)

/-- The canonical ideal inclusion, not a separately chosen embedding. -/
def torsionCompletionIdealInclusion (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :
    torsionCompletionIdeal X I ⟶ SheafOfModules.unit (torsionCompletionModuleRing X A) :=
  kernel.ι (torsionCompletionQuotientMap X I)

/-- Sheafification of abelian coefficients on the coefficient-sized small model, at the pinned
universes `(t, u)`: the global instance form of `coefficientModelAdditiveSheafify` kept at its
former priority. -/
instance (priority := 20000) torsionCompletionSheafify (X : Scheme.{t}) :
    HasSheafify (coefficientProEtaleModelTopology.{t, u} X)
      AddCommGrpCat.{max u (t + 1)} :=
  coefficientModelAdditiveSheafify.{t, u} X

/-- The same abelian sheafification on each slice of the unchanged model site. -/
instance (priority := 20000) torsionCompletionSliceSheafify (X : Scheme.{t})
    (U : coefficientProEtaleSiteModel.{t, u} X) :
    HasSheafify ((coefficientProEtaleModelTopology.{t, u} X).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

end AlgebraicGeometry.Scheme
