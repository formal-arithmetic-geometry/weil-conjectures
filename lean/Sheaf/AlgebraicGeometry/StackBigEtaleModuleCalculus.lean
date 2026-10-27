module

public import Sheaf.AlgebraicGeometry.StackBigEtaleModuleFunctors
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Module calculus on big etale stack sites

Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus).

The site and regular-function presheaf are reused. Precomposition retains all module
sections. Its right adjoint is determined up to the unique adjunction-compatible
isomorphism, and is the compatible-family direct image. The square comparison is
characterized on every section before taking its adjunction mate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Degree zero of the recorded injective resolution gives an injective embedding.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-calculus). -/
instance moduliBigEtale_enoughInjectives {S : AlgebraicGeometry.Scheme.{u}}
    (X : BasedCategory.{v, w} (Over S)) (hX : IsFibredInGroupoids X) :
    EnoughInjectives (ModuliBigEtaleModules X hX) where
  presentation M :=
    Nonempty.map (fun I : InjectiveResolution M ↦
      { J := I.cocomplex.X 0, f := I.ι.f 0 }) (HasInjectiveResolution.out (Z := M))

/-- Module precomposition is additive and exact.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus).

Proof: Addition and kernels are sectionwise. A section of a cokernel locally
lifts to a representative. Cartesian lifting of etale covers along a based functor
preserves this description, so precomposition also preserves cokernels and finite sums. -/
theorem moduliBigEtalePrecomposition_exact {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : BasedCategory.{v, w} (Over S)} (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    (moduliBigEtalePrecomposition hX hY f).Additive ∧
      PreservesFiniteLimits (moduliBigEtalePrecomposition hX hY f) ∧
      PreservesFiniteColimits (moduliBigEtalePrecomposition hX hY f) := by
  sorry

/-- The additive component of exact precomposition.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-calculus). -/
instance moduliBigEtalePrecomposition_additive {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : BasedCategory.{v, w} (Over S)} (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    (moduliBigEtalePrecomposition hX hY f).Additive :=
  (moduliBigEtalePrecomposition_exact hX hY f).1

/-- The limits component of exact precomposition.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-calculus). -/
instance moduliBigEtalePrecomposition_limits {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : BasedCategory.{v, w} (Over S)} (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    PreservesFiniteLimits (moduliBigEtalePrecomposition hX hY f) :=
  (moduliBigEtalePrecomposition_exact hX hY f).2.1

/-- The colimits component of exact precomposition.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-calculus). -/
instance moduliBigEtalePrecomposition_colimits {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : BasedCategory.{v, w} (Over S)} (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    PreservesFiniteColimits (moduliBigEtalePrecomposition hX hY f) :=
  (moduliBigEtalePrecomposition_exact hX hY f).2.2

/-- The selected direct image has its canonical precomposition adjunction.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus). -/
def moduliBigEtaleAdjunction {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : BasedCategory.{v, w} (Over S)} (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    moduliBigEtalePrecomposition hX hY f ⊣ moduliBigEtaleDirectImage hX hY f :=
  Adjunction.ofIsLeftAdjoint _

/-- Module precomposition is additive and exact.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus).

Proof: Addition and kernels are sectionwise. A section of a cokernel locally
lifts to a representative. Cartesian lifting of etale covers along a based functor
preserves this description, so precomposition also preserves cokernels and finite sums. -/
theorem moduliBigEtaleWidePrecomposition_exact {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, max v w} (Over S)} {Y : BasedCategory.{v, w} (Over S)}
    (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    (moduliBigEtaleWidePrecomposition hX hY f).Additive ∧
      PreservesFiniteLimits (moduliBigEtaleWidePrecomposition hX hY f) ∧
      PreservesFiniteColimits (moduliBigEtaleWidePrecomposition hX hY f) := by
  sorry

/-- The additive component of exact precomposition.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-calculus). -/
instance moduliBigEtaleWidePrecomposition_additive {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, max v w} (Over S)} {Y : BasedCategory.{v, w} (Over S)}
    (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    (moduliBigEtaleWidePrecomposition hX hY f).Additive :=
  (moduliBigEtaleWidePrecomposition_exact hX hY f).1

/-- The limits component of exact precomposition.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-calculus). -/
instance moduliBigEtaleWidePrecomposition_limits {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, max v w} (Over S)} {Y : BasedCategory.{v, w} (Over S)}
    (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    PreservesFiniteLimits (moduliBigEtaleWidePrecomposition hX hY f) :=
  (moduliBigEtaleWidePrecomposition_exact hX hY f).2.1

/-- The colimits component of exact precomposition.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-calculus). -/
instance moduliBigEtaleWidePrecomposition_colimits {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, max v w} (Over S)} {Y : BasedCategory.{v, w} (Over S)}
    (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    PreservesFiniteColimits (moduliBigEtaleWidePrecomposition hX hY f) :=
  (moduliBigEtaleWidePrecomposition_exact hX hY f).2.2

/-- The selected direct image has its canonical precomposition adjunction.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus). -/
def moduliBigEtaleWideAdjunction {S : AlgebraicGeometry.Scheme.{u}}
    {X : BasedCategory.{v, max v w} (Over S)} {Y : BasedCategory.{v, w} (Over S)}
    (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) :
    moduliBigEtaleWidePrecomposition hX hY f ⊣ moduliBigEtaleWideDirectImage hX hY f :=
  Adjunction.ofIsLeftAdjoint _

/-- The second projection of the recorded two-fibre product lies over the base.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus).

Proof: For each comma object its comparison arrow lies over the identity,
so its two base objects agree. The comma square and the lift identity identify the
two projected base arrows. Functor extensionality gives the equality. -/
theorem moduliBigEtaleSnd_over {S : AlgebraicGeometry.Scheme.{u}}
    {X Y Y' : BasedCategory.{v, w} (Over S)}
    (f : BasedFunctor X Y) (b : BasedFunctor Y' Y) :
    (ObjectProperty.ι _ ⋙ Comma.snd b.toFunctor f.toFunctor) ⋙ X.p =
      (moduliTwoFiberProduct b f).p := by
  sorry

/-- The projection a to the second factor, with its specified map over the base.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus). -/
def moduliBigEtaleSnd {S : AlgebraicGeometry.Scheme.{u}}
    {X Y Y' : BasedCategory.{v, w} (Over S)}
    (f : BasedFunctor X Y) (b : BasedFunctor Y' Y) :
    BasedFunctor (moduliTwoFiberProduct b f) X where
  toFunctor := ObjectProperty.ι _ ⋙ Comma.snd b.toFunctor f.toFunctor
  w := moduliBigEtaleSnd_over f b

/-- The recorded two-fibre product remains fibred in groupoids.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus).

Proof: Lift a base arrow in each factor. The cartesian property lifts the
comparison isomorphism uniquely; the resulting comma object is a lift. The strong
cartesian universal property and uniqueness are checked in the two factors. -/
theorem moduliBigEtaleTwoFiber_isFibred {S : AlgebraicGeometry.Scheme.{u}}
    {X Y Y' : BasedCategory.{v, w} (Over S)}
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (hY' : IsFibredInGroupoids Y') (f : BasedFunctor X Y) (b : BasedFunctor Y' Y) :
    IsFibredInGroupoids (moduliTwoFiberProduct b f) := by
  sorry

variable {S : AlgebraicGeometry.Scheme.{u}}
  {X Y Y' : BasedCategory.{v, w} (Over S)}
  (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
  (hY' : IsFibredInGroupoids Y') (f : BasedFunctor X Y) (b : BasedFunctor Y' Y)

/-- The square transport is uniquely specified by restriction along its comma isomorphism.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus).

Proof: At z use the restriction map of M along its comma isomorphism. The
comparison is vertical, so its regular-function restriction is the identity after
the based-functor ring identifications, and this map is linear. The comma square
proves naturality in z, and naturality of module morphisms proves naturality in M.
These component equations uniquely determine the natural transformation. -/
theorem moduliBigEtaleSquare_existsUnique :
    ∃! θ :
      moduliBigEtalePrecomposition hX hY f ⋙
          moduliBigEtaleWidePrecomposition (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hX
            (moduliBigEtaleSnd f b) ⟶
        moduliBigEtalePrecomposition hY' hY b ⋙
          moduliBigEtaleWidePrecomposition (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hY'
            (moduliTwoFiberFst b f),
      ∀ (M : ModuliBigEtaleModules Y hY) (z : (moduliTwoFiberProduct b f).obj),
        (forget₂ (ModuleCat _) AddCommGrpCat).map ((θ.app M).val.app (op z)) =
          M.val.presheaf.map z.obj.hom.op := by
  sorry

/-- The canonical square transport on precomposition functors.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus). -/
def moduliBigEtaleSquare :
    moduliBigEtalePrecomposition hX hY f ⋙
        moduliBigEtaleWidePrecomposition (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hX
          (moduliBigEtaleSnd f b) ⟶
      moduliBigEtalePrecomposition hY' hY b ⋙
        moduliBigEtaleWidePrecomposition (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hY'
          (moduliTwoFiberFst b f) :=
  Classical.choose (moduliBigEtaleSquare_existsUnique hX hY hY' f b)

/-- The sectionwise square transport is invertible.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus).

Proof: The comma comparison is an isomorphism. Restriction along its inverse
is inverse to restriction along it. The component characterization of the square
transport therefore gives an inverse at every section, hence a natural inverse. -/
@[instance] theorem moduliBigEtaleSquare_isIso :
    IsIso (moduliBigEtaleSquare hX hY hY' f b) := by
  sorry

/-- The underived base-change map is the counit mate of the specified square.
Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W5 and 075H
(blueprint: def-sfb-stack-big-etale-module-calculus). -/
def moduliBigEtaleBaseChange :
    moduliBigEtaleDirectImage hX hY f ⋙ moduliBigEtalePrecomposition hY' hY b ⟶
      moduliBigEtaleWidePrecomposition (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hX
          (moduliBigEtaleSnd f b) ⋙
        moduliBigEtaleWideDirectImage (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hY'
          (moduliTwoFiberFst b f) :=
  Adjunction.exchangeRight (moduliBigEtaleAdjunction hX hY f)
    (moduliBigEtaleWideAdjunction (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hY'
      (moduliTwoFiberFst b f)) (asIso (moduliBigEtaleSquare hX hY hY' f b)).symm

/-- The canonical degreewise comparison, obtained by deriving the counit mate.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-calculus).
The auxiliary derived categories use the standard localization, while the source and
target are Mathlib's injective-resolution right derived functors. -/
def moduliBigEtaleHigherBaseChange (i : ℕ) :
    moduliBigEtaleHigherImage hX hY f i ⋙
        moduliBigEtalePrecomposition hY' hY b ⟶
      moduliBigEtaleWidePrecomposition (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hX
          (moduliBigEtaleSnd f b) ⋙
        moduliBigEtaleWideHigherImage (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hY'
          (moduliTwoFiberFst b f) i :=
  letI := HasDerivedCategory.standard
    (ModuliBigEtaleModules X hX)
  letI := HasDerivedCategory.standard
    (ModuliBigEtaleModules Y hY)
  letI := HasDerivedCategory.standard
    (ModuliBigEtaleModules Y' hY')
  letI := HasDerivedCategory.standard
    (ModuliBigEtaleModules (moduliTwoFiberProduct b f)
      (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b))
  Functor.rightDerivedBaseChange
    (G := moduliBigEtaleDirectImage hX hY f)
    (G' := moduliBigEtaleWideDirectImage
      (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hY' (moduliTwoFiberFst b f))
    (β := moduliBigEtaleWidePrecomposition
      (moduliBigEtaleTwoFiber_isFibred hX hY hY' f b) hX (moduliBigEtaleSnd f b))
    (γ := moduliBigEtalePrecomposition hY' hY b)
    (moduliBigEtaleBaseChange hX hY hY' f b) i

end CategoryTheory
