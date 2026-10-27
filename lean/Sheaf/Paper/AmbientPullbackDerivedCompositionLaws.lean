module

public import Sheaf.Paper.AmbientPullbackTensorData

/-! Derived pullback associativity and unit laws.

Source: Stacks 015F and 04VG.
(blueprint: new-lem-sf-ambient-pullback-derived-composition-laws).

This is the exact-localization part of the ambient pullback coherence argument.
The ordinary equations are preserved by the exact termwise functors and their
localizations; the resulting three equations are recorded here separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Derived associativity and unit laws for the ambient pullback comparisons.
Source: Stacks 015F and 04VG.
(blueprint: new-lem-sf-ambient-pullback-derived-composition-laws).
Proof: apply the exact termwise pullback functors to the ordinary equations,
then use the localization universal property and the specified factorization
isomorphisms.  This preserves composition, identities and all endpoint
transports, giving the three displayed derived clauses. -/
theorem derived_pullback_compositionLaws (K : Scheme.{t}) (s : Option ℕ) :
    (∀ {W X Y Z : Scheme.{t}} (w : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
      (aW : W ⟶ K) (aX : X ⟶ K) (aY : Y ⟶ K) (aZ : Z ⟶ K)
      [LocallyOfFiniteType aW] [QuasiCompact aW] [LocallyOfFiniteType aX]
      [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
      [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (_hw : w ≫ aX = aW) (_hf : f ≫ aY = aX) (_hg : g ≫ aZ = aY)
      (M : Derived ell E Z s),
      (derivedPull ell E w s).map ((derivedComp ell E f g s).hom.app M) ≫
          (derivedComp ell E w (f ≫ g) s).hom.app M =
        (derivedComp ell E w f s).hom.app ((derivedPull ell E g s).obj M) ≫
          (derivedComp ell E (w ≫ f) g s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M)
            (Category.assoc w f g))) ∧
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Derived ell E Y s),
      (derivedPull ell E f s).map ((derivedIdentity ell E Y s).hom.app M) =
        (derivedComp ell E f (𝟙 Y) s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M)
            (Category.comp_id f))) ∧
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Derived ell E Y s),
      (derivedIdentity ell E X s).hom.app ((derivedPull ell E f s).obj M) =
        (derivedComp ell E (𝟙 X) f s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M)
            (Category.id_comp f))) := by
  sorry

end WeilConjectures.AmbientPullbackTensor
