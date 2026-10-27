module

public import Sheaf.AlgebraicGeometry.SpaceFormalFunctionsData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Formal functions at a geometric stalk

Source: Stacks Project, spaces-cohomology.tex, Tag 08B1
(blueprint: lem-sfb-space-formal-functions-geometric-stalk).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace
open FormalFunctions

/-- Formal functions for a proper algebraic space at a geometric point, with the
canonical infinitesimal restriction maps and completed coefficient action.
Source: Stacks Project, Tag 08B1 (lemma-formal-functions-stalk)
(blueprint: lem-sfb-space-formal-functions-geometric-stalk).
Proof: geometric stalks of the structure sheaf of a locally Noetherian scheme are
Noetherian local rings. Construct c from pointed affine etale neighbourhood germs;
the filtered-colimit universal property makes the maps independent of the chart.
Base change f along c. Flat base change identifies the higher-image geometric stalk
with cohomology over this strict local base. Properness and coherence survive this
base change. The affine formal-functions theorem, Tag 08AZ, identifies the completion
of that cohomology with the inverse limit over powers of the maximal ideal.
Fibre-product associativity identifies the finite spaces with the X_n here, and
tensor transitivity identifies their sheaves and restriction maps. All comparisons
are normalized on chart sections and their derived units, so the finite-coordinate
maps are exactly Cohomology.map. They respect the quotient coefficient actions,
hence the resulting isomorphism is linear over the completed ring. Uniqueness follows
coordinatewise: finite-level cohomology is annihilated by the corresponding maximal
ideal power, and the finite higher-image stalk has the same quotient as its completion.
This also proves independence from resolutions and from the pullback presentations. -/
theorem formalFunctions_geometricStalk
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (X : AlgebraicSpace Y) (f : X ⟶ FormalFunctions.base Y) (hf : MapIsProper f)
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hfinite : ∃ (I : Type (u + 1)) (T : I → X.EtaleSite),
      IsJointlySurjective (fun i ↦ (T i).obj.hom) ∧
      ∀ i : I, IsAffine (X.etaleForget.obj (T i)) ∧
        IsNoetherianRing (X.structureSheaf.obj.obj (op (T i))) ∧
        Module.Finite (X.structureSheaf.obj.obj (op (T i))) (F.val.obj (op (T i))))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    IsNoetherianRing (FormalFunctions.ring y) ∧
      ∃ (D : Geometry X f y) (C : Cohomology D), ∀ q : ℕ,
        ∃! e : ModuleCat.of D.completion
            (AdicCompletion D.ideal (source f y F q)) ≅ limit (C.tower F q),
          ∀ (n : ℕ) (m : source f y F q),
            (e.hom ≫ limit.π (C.tower F q) (op n))
              (AdicCompletion.of D.ideal (source f y F q) m) = C.map F n q m := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
