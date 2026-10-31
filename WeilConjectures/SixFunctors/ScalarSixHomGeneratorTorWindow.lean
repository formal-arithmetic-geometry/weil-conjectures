/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.AdmissibleDirectImage
import WeilConjectures.SixFunctors.ListedCoefficientCtf

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option linter.unusedVariables false in
/-- Direct images along a locally closed immersion preserve bounded constant-model
constructibility and finite Tor amplitude.
Source: blueprint det-prop-scalar-six-tensor-hom.proof.md, “The generator”, which applies
det-thm-sf-ctf-stability-direct-images to the direct image `Rb_*` of the local Hom.
(blueprint: lem-sfb-native-scalar-hom-generator-tor-window).
Proof: the listed coefficient map `a` makes `Λ.X` a localizing admissible coefficient
ring (first conjunct of [lem-sfb-listed-coefficient-ctf]). Give `S` the structure map
`b ≫ X.hom` over `Spec k`; an immersion is locally of finite type, quasi-compact (`X` is
Noetherian, being of finite type over a field) and separated, so `S` satisfies the standing
finite-type, quasi-compact and separated hypotheses over `k` and `b` is a separated morphism
of finite type over `k`. The admissible direct-image theorem [lem-sfb-admissible-direct-image]
(the direct-image clause of det-thm-sf-ctf-stability-direct-images) then gives that `Rb_* Q`
is bounded constant-model constructible of finite Tor amplitude. The object `M` of the
statement is not used.
-/
theorem scalarSixHom_generator_torWindow
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (M : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (S : Scheme.{u}) (b : S ⟶ X.left) (hb : IsImmersion b)
    (Q : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hQ : constantModelBoundedConstructible Λ.X S Q ∧
      DerivedCategory.finiteTorAmplitude _ Q) :
    constantModelBoundedConstructible Λ.X X.left
        ((R((b)_*⟦Λ.X⟧)).obj Q) ∧
      DerivedCategory.finiteTorAmplitude _
        ((R((b)_*⟦Λ.X⟧)).obj Q) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := {}
  let : IsImmersion b := hb
  let : TopologicalSpace.NoetherianSpace S := b.isEmbedding.isInducing.noetherianSpace
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian b
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  have : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  have : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  let : S.Over (Spec (.of k)) := ⟨b ≫ X.hom⟩
  have : b.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (b ≫ X.hom)
    infer_instance
  have : QuasiCompact (S ↘ Spec (.of k)) := by
    change QuasiCompact (b ≫ X.hom)
    infer_instance
  have : IsSeparated (S ↘ Spec (.of k)) := by
    change IsSeparated (b ≫ X.hom)
    infer_instance
  exact constructibleFiniteTor_rightDerivedLowerStar_of_admissible ell k Λ.X
    (listedCoefficientCtf ell a ha).1 (X := S) (Y := X.left) b Q hQ

end AlgebraicGeometry.ProEtale.CondensedRing
