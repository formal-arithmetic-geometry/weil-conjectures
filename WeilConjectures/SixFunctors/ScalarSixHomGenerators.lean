/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ScalarInternalAdjunctionPairingChange
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.SixFunctors.ScalarSixHomGeneratorComparison
import WeilConjectures.SixFunctors.ScalarSixHomGeneratorFiniteness

/-! # Scalar internal Hom on locally closed scalar-perfect generators

Source: current blueprint det-prop-scalar-six-tensor-hom.proof.md,
The generator and It is v
(blueprint: lem-sfb-native-scalar-hom-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native scalar mate is the arrow in the recorded immersion pairing square.
Source: blueprint det-prop-scalar-six-tensor-hom, It is v
(blueprint: lem-sfb-native-scalar-hom-generators).

Proof: both arrows are the same evaluation transpose. The inverse of the canonical
oplax tensor comparison is the lax tensorator of the derived monoidal functor. -/
theorem scalarSixHom_pairingComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u})
    (L N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (Functor.LaxMonoidal.ihomComparison (scalarSixChange a X) L).natTrans.app N =
      immersionPairingScalarHom a X L N := by
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry]
  rfl

/-- The native comparison is invertible on finite-projective unit models.
Source: blueprint det-prop-scalar-six-tensor-hom, The generator, finite free modules
and their direct summands (blueprint: lem-sfb-native-scalar-hom-generators).

Proof: the strong monoidal unit comparison identifies Hom from the tensor unit
with the target itself. Additivity extends this to a finite biproduct of units.
Naturality exhibits the comparison at a retract as an arrow-category retract
of that biproduct comparison, hence it too is invertible. The empty biproduct
and zero-rank retract satisfy exactly the same argument. No flatness is used. -/
theorem scalarSixHom_finiteFreeRetract {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u})
    (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (n : ℕ) (r : Retract K (⨁ fun _ : Fin n ↦
      𝟙_ (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)))) :
    IsIso ((Functor.LaxMonoidal.ihomComparison (scalarSixChange a X) K).natTrans.app M) := by
  let F := scalarSixChange a X
  let adj : F ⊣ (Mod.comap
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  have : F.Additive := adj.left_adjoint_additive
  let units : Fin n → DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) :=
    fun _ ↦ 𝟙_ _
  have hu : ∀ j, IsIso ((Functor.LaxMonoidal.ihomComparison F (units j)).natTrans.app M) :=
    fun _ ↦ Functor.LaxMonoidal.isIso_ihomComparison_app_unit F M
  have hfree : IsIso ((Functor.LaxMonoidal.ihomComparison F (⨁ units)).natTrans.app M) := by
    exact @Functor.LaxMonoidal.isIso_ihomComparison_app_biproduct
      _ _ _ _ _ _ _ _ F _ _ _ _ _ _ (Fin n) _ units _ M hu
  let β : (derivedHom Λ.X X).flip.obj M ⋙ F ⟶
      F.op ⋙ (derivedHom Λ'.X X).flip.obj (F.obj M) :=
    { app := fun J ↦ (Functor.LaxMonoidal.ihomComparison F J.unop).natTrans.app M
      naturality := fun _ _ f ↦
        Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app F f.unop M }
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    (β.retractArrowApp r.op) hfree

/-- The generator calculation, including membership of its unextended Hom.
Source: blueprint det-prop-scalar-six-tensor-hom, The generator and It is v
(blueprint: lem-sfb-native-scalar-hom-generators).

Proof: factor b through its scheme-theoretic image as an open immersion u
followed by a closed immersion i. Let j be the complementary open immersion in X.
The ambient support model is RΓ_i(M)=fiber(M → Rj_*j^*M), and set
N=u^*i^*RΓ_i(M)=b^!M. The relative immersion finiteness theorem is checked after
separably closed base change: etale localization commutes with these immersion
functors, strict-local cohomological bounds depend on dim X, and constructibility
and finite Tor amplitude descend through the conservative base change. Finite
coefficient models give these bounds; integral and rational scalar models and
finite-subextension descent give the other listed coefficients. Thus N has
constructible finite Tor amplitude without an absolute bound on the original
field. For locally scalar-perfect P,
perfect duality identifies H=RHom(P,N) with P-dual tensor N. The immersion support
formula identifies RHom(b_!P,M) with Rb_*H, proving its constructible finite Tor
membership by the relative immersion stability calculation.
On every perfect chart scalar extension of Hom(P,N) is the evaluation-defined
Hom comparison: finite free modules give finite powers, finite projectives give
retracts, and the finite stupid filtration handles bounded projective complexes.
Restriction is compatible with this precise transpose, so cover conservativity
gives its invertibility globally. The immersion-specific direct-image and
exceptional coefficient comparisons on H and M, and the normalized coefficient
comparison for b_!, identify the two support models after scalar change. Their
pairing square is scalarInternalAdjunctionPairingChange: transpose both routes,
use the closed-counit/open-tensor projection square, the ordinary counit square,
and the exceptional counit equation. Both transposes are scalar extension of the
original pairing composed with the inverse tensorator. Hence the resulting
invertible composite is exactly the native ihomComparison displayed below.
Empty strata, the zero ring, and zero-rank projective summands use zero objects;
the identity immersion reduces to the local perfect calculation.
In Lean the invertibility conjunct is scalarSixHom_generator_comparison and the
membership conjunct is scalarSixHom_generator_finiteness; the proof pairs them. -/
theorem scalarSixHom_generator (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (M : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (S : Scheme.{u}) (b : S ⟶ X.left) (hb : IsImmersion b)
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hP : IsLocallyPerfectScalarModel Λ.X S P) :
    IsIso ((Functor.LaxMonoidal.ihomComparison (scalarSixChange a X.left)
      ((sfbLocallyClosedDerivedExtension Λ b hb).obj P)).natTrans.app M.obj) ∧
    (constantModelBoundedConstructible Λ.X X.left
      (((derivedHom Λ.X X.left).obj
        (.op ((sfbLocallyClosedDerivedExtension Λ b hb).obj P))).obj M.obj) ∧
      DerivedCategory.finiteTorAmplitude _
        (((derivedHom Λ.X X.left).obj
          (.op ((sfbLocallyClosedDerivedExtension Λ b hb).obj P))).obj M.obj)) := by
  exact ⟨scalarSixHom_generator_comparison ell k a ha X M S b hb P hP,
    scalarSixHom_generator_finiteness ell k a ha X M S b hb P hP⟩

end AlgebraicGeometry.ProEtale.CondensedRing
