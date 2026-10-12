module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable local instance tensorNaturality (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The tensor comparison for canonical open restriction is natural in both modules.
Source: Stacks Project, Tag 01CD, functoriality of pullback and tensor product;
Tag 08DX, proof of (1), applies the resulting comparison locally.
Proof: apply exists_restriction_tensor_comparison to U.ι. Its inverse is determined
by its pure-tensor formula: a map from a sheafified sectionwise tensor is determined
by local pure tensors. For maps f and g, the two naturality composites both send
a pure tensor s tensor t to the tensor of f(s) and g(t). This proves naturality of
the inverse comparisons. Multiply by the comparisons on both sides to obtain the
stated naturality of the forward comparisons. Use Scheme.Modules.overFunctorEquiv U,
which is natural and identifies over-site restriction followed by overEquiv with
restriction along U.ι. Transport the comparisons along its components, using the
canonical agreement between Scheme.Modules and the underlying SheafOfModules carrier.
The naturality squares of overFunctorEquiv transport the previous tensor naturality
square to the displayed square. No complexes, coproducts, boundedness or flatness
occur in this assertion. For the empty open all objects are zero, and the unique maps
satisfy the same formula.
(blueprint: lem-pc-open-restriction-tensor-natural). -/
theorem exists_openRestriction_tensor_natural (X : Scheme.{u}) (U : X.Opens) :
    let R :=
      SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)
    ∃ e : ∀ (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      R.obj (F ⊗ G) ≅ R.obj F ⊗ R.obj G,
      ∀ (F F' G G' : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (f : F ⟶ F') (g : G ⟶ G'),
        R.map (f ⊗ₘ g) ≫ (e F' G').hom =
          (e F G).hom ≫ (R.map f ⊗ₘ R.map g) := by
  sorry

end AlgebraicGeometry
