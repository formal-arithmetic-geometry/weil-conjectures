module
public import Sheaf.AlgebraicGeometry.FiniteLisseFieldDual
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
/-- The pairing-transpose comparison gives invertible ordinary exchange after shrinking.
Source: lem-asd-smooth-generic-direct-image, final pairing comparison
(blueprint: lem-asd-smooth-lisse-ordinary-exchange).

Proof: transpose the internal-adjunction evaluation pairing. Compact-support exchange naturality
and smooth exceptional base change transport it to the pulled-back pairing, which is the
ordinary exchange map. -/
theorem isIso_smooth_lisse_ordinary_exchange
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    (S : Scheme.{u}) [IsIntegral S] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (hℓ : ℓ ≠ ringChar k)
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) (U : S.Opens)
    (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme)
    (sqU : IsPullback p fU f U.ι) :
    ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
      (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
      (sq : IsPullback vX fT fU v),
      IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sq.toCommSq).app ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L))) := by sorry
end AlgebraicGeometry.Etale
