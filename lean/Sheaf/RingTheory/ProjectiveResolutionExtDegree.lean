module
public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Sheaf.RingTheory.ProjectiveResolutionSuccSplice
@[expose] public section
universe u v
open CategoryTheory
namespace ModuleCat
/-- The explicit bounded-resolution predicate agrees with Mathlib's projective-dimension
predicate. Unlike the Ext criteria already in Mathlib, the reverse implication constructs
an actual bounded projective resolution. Induct on the bound: at zero use the identity
resolution of a projective object; at a successor use Mathlib's dimension shifting for
the kernel of a projective epimorphism and augment its shorter resolution. Exactness,
projectivity and the support bound of the augmented complex give the required resolution.
The forward implication represents Ext classes by cocycles on the zero resolution terms
and applies Mathlib's `HasProjectiveDimensionLT.mk`.
Source: Stacks Project, Algebra, Lemma 065R, parts (1)--(3).
(blueprint: lem-weil-pbc-projective-resolution-ext-degree). -/
theorem projective_resolution_ext_degree
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE X n ↔ HasProjectiveDimensionLE X n := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  constructor
  · rintro ⟨P, hP⟩
    apply HasProjectiveDimensionLT.mk
    intro i hi Y a
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective a (i + 1) (by omega)
    have hfzero : f = 0 := (hP i (by omega)).eq_of_src _ _
    subst f
    exact P.extMk_zero _ _
  · intro h
    induction n generalizing X with
    | zero =>
      have : Projective X := (projective_iff_hasProjectiveDimensionLE_zero X).mpr h
      refine ⟨ProjectiveResolution.self X, fun i hi ↦ ?_⟩
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    | succ n ih =>
      let S := ShortComplex.mk _ _ (Limits.kernel.condition (Projective.π X))
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π X) }
      have hK : HasProjectiveDimensionLE S.X₁ n :=
        (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
      exact hasProjectiveResolutionLE_of_shortExact_projective_middle n S hS
        inferInstance (ih S.X₁ hK)
end ModuleCat
