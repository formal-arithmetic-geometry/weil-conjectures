/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar
public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel

/-! # Scalar compatibility of affine realization

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
(blueprint: lem-sc-affine-open-realization-scalar).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Scalar identities commute with every affine realization comparison isomorphism.
This requires neither perfectness nor a cohomology support condition.
Source: Stacks Project, Tag 06Z0, termwise associated-sheaf construction, and
Tag 08EJ, identification of the affine scalar action.
(blueprint: lem-sc-affine-open-realization-scalar).

Proof: Give the localized-site sheaf category the action of global sections of X
by restricting each compatible family of scalars to objects over U. The overFunctor
is linear for this action. Give A-modules the same action via evaluation at U.
Compatibility of sections says that affinePerfectSheafification sends a|U times
any module map to multiplication by the corresponding restricted global scalar.
Indeed tilde applies the scalar in each local module localization, scheme-isomorphism
restriction transports it through the structure-sheaf ring map, and the over-site
inverse equivalence only reindexes the sections. These identities pass termwise to
complexes and then through Q, which is linear. Naturality of the given comparison at
K identifies F(a|U id_Q(K)) with the scalar identity on F(Q(K)). Centrality of scalar
multiplication in the target derived category allows this scalar identity to commute
with the arbitrary comparison e. Linearity of derived restriction identifies the
scalar identity on R(E) with R(schemeDerivedScalar X a id_E). Compose the resulting
equality with e.hom. For zero scalars and empty U the same equations hold, and no
choice of e or perfect model is needed. -/
theorem affine_open_realization_scalar
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) →
      ∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (E : schemeDerivedCategory X)
        (e : F.obj (DerivedCategory.Q.obj K) ≅ R.obj E)
        (a : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})),
        F.map ((show A from a.val (op U)) • 𝟙 (DerivedCategory.Q.obj K)) ≫ e.hom =
          e.hom ≫ R.map (schemeDerivedScalar X a (𝟙 E)) := by sorry

end AlgebraicGeometry.Scheme
