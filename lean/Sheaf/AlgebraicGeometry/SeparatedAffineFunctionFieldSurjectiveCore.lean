module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry

universe u
namespace AlgebraicGeometry

/-- The separated affine function-field construction yields a closed immersion of spectra.
Source: Varieties Lemma 09NB, separatedness paragraph
(blueprint: lem-sc-separated-affine-function-field-surjective-core).
The proof constructs the pullback of the diagonal along the affine charts, identifies it
with `Spec K`, and transports the resulting closed immersion through the affine-spectrum
identifications. -/
theorem Scheme.isClosedImmersion_specMap_tensor_functionField
    (X : Scheme.{u}) [IsIntegral X]
    [hsep : X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) [hUn : Nonempty U]
    (x : X) (hx : x ∉ U)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    let A : Type u := Γ(X, U)
    let B : Type u := X.presheaf.stalk x
    let K : Type u := X.functionField
    let φ : TensorProduct ℤ A B →ₐ[ℤ] K :=
      Algebra.TensorProduct.lift
        (X.germToFunctionField U).hom.toIntAlgHom
        (algebraMap B K).toIntAlgHom
        (fun _ _ => Commute.all _ _)
    IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
  sorry

/-- A closed immersion between affine spectra induces a surjective ring map.
Source: Stacks Project, Morphisms Lemma 01IQ (blueprint: lem-sc-closed-immersion-affine-surjective).
The affine closed-immersion criterion gives surjectivity on global sections; the
canonical global-sections isomorphisms for spectra transport this to the original map. -/
theorem surjective_of_isClosedImmersion_specMap
    (R S : CommRingCat.{u}) (f : R ⟶ S)
    [IsClosedImmersion (Spec.map f)] : Function.Surjective f := by
  obtain ⟨_, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map f)
  intro a
  obtain ⟨b, hb⟩ := hsurj ((Scheme.ΓSpecIso S).inv a)
  refine ⟨(Scheme.ΓSpecIso R).hom b, ?_⟩
  have hnat := DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality f)) b
  calc
    f.hom ((Scheme.ΓSpecIso R).hom b) =
        (Scheme.ΓSpecIso S).hom ((Spec.map f).appTop.hom b) := hnat.symm
    _ = (Scheme.ΓSpecIso S).hom ((Scheme.ΓSpecIso S).inv a) := by rw [hb]
    _ = a := by simp

end AlgebraicGeometry
