module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.Algebra.Module.Presentation.Tensor
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

/-! # Tensor products of finitely presented scheme module sheaves

Source: Stacks Project, Modules, Tag 01CE, Lemma `modules-lemma-tensor-product-permanence`,
clause (4), specialized to schemes (blueprint: lem-trf-fp-sheaf-tensor-product).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem finitePresentation_tensor (R M N : Type u) [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N] :
    Module.FinitePresentation R (TensorProduct R M N) := by
  obtain ⟨p, hpG, hpR⟩ := Module.finitePresentation_iff_exists_presentation.{u, u}.mp
    (inferInstance : Module.FinitePresentation R M)
  obtain ⟨q, hqG, hqR⟩ := Module.finitePresentation_iff_exists_presentation.{u, u}.mp
    (inferInstance : Module.FinitePresentation R N)
  let := hpG
  let := hpR
  let := hqG
  let := hqR
  have : Finite (p.tensor q).G := inferInstanceAs (Finite (p.G × q.G))
  have : Finite (p.tensor q).R :=
    inferInstanceAs (Finite ((p.R × q.G) ⊕ (p.G × q.R)))
  exact (p.tensor q).finitePresentation

private theorem finitePresentation_tilde (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] : (tilde M).IsFinitePresentation := by
  obtain ⟨s, hs, t, ht⟩ := (inferInstance : Module.FinitePresentation R M).out
  let P := presentationTilde M (s : Set M) hs (t : Set _) ht
  have : P.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set M))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ R)))⟩ }
  exact P.isFinitePresentation

private theorem finitePresentation_tensor_affine (R : CommRingCat.{u})
    (F G : (Spec R).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation] :
    (F ⊗ G).IsFinitePresentation := by
  let M := moduleSpecΓFunctor.obj F
  let N := moduleSpecΓFunctor.obj G
  have : Module.FinitePresentation R M := finitePresentation_sections_top F
  have : Module.FinitePresentation R N := finitePresentation_sections_top G
  have : Module.FinitePresentation R (TensorProduct R M N) :=
    finitePresentation_tensor R M N
  have : IsIso F.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent F
  have : IsIso G.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent G
  obtain ⟨_, _, _, α, _, hα, _⟩ := affine_tilde_tensor R M N
  let := hα
  have := finitePresentation_tilde R (ModuleCat.of R (TensorProduct R M N))
  exact isFinitePresentation_of_iso
    (asIso α ≪≫ (asIso F.fromTildeΓ ⊗ᵢ asIso G.fromTildeΓ))

/-- The tensor product of two finitely presented sheaves of modules on a scheme is
finitely presented. The predicate `SheafOfModules.IsFinitePresentation` means locally a
cokernel of a map between finite free module sheaves; the tensor is the sheafification
of the sectionwise tensor product.

Source: Stacks Project, Modules, Tag 01CE, clause (4)
(blueprint: lem-trf-fp-sheaf-tensor-product).

Proof:
1. For ordinary modules use `Module.finitePresentation_iff_exists_presentation` to
   choose finite presentations. Their tensor presentation has generators indexed by
   the product of the two generator types, and relations indexed by the disjoint union
   of relations times generators and generators times relations. These types are finite,
   so `Module.Presentation.finitePresentation` proves finite presentation of the tensor.
2. On Spec R, quasi-coherent sheaves F and G are the tilde sheaves of their global
   sections M and N. These modules are finitely presented by
   `finitePresentation_sections_top`. The affine tensor comparison identifies
   F tensor G with tilde (M tensor N). Applying `presentationTilde` to finite generators
   and relations of M tensor N gives a finite global presentation of that sheaf.
3. Cover X by all affine opens. Restriction preserves finite presentation, and the
   restriction tensor comparison identifies the restricted tensor with the tensor of
   the restricted factors. Step 2 applies on each affine chart. Finite presentation is
   local for this open-immersion cover, giving the conclusion. All constructions allow
   zero generators or relations, and the argument also covers the empty scheme. -/
theorem isFinitePresentation_tensorProduct {X : Scheme.{u}} (F G : X.Modules)
    [F.IsFinitePresentation] [G.IsFinitePresentation] :
    (F ⊗ G).IsFinitePresentation := by
  refine isFinitePresentation_of_isOpenImmersion (F ⊗ G)
    (fun U : {U : X.Opens // IsAffineOpen U} ↦ U.2.fromSpec)
    iSup_opensRange_fromSpec_eq_top fun U ↦ ?_
  obtain ⟨e, _⟩ := exists_restriction_tensor_comparison U.2.fromSpec F G
  have := finitePresentation_tensor_affine (CommRingCat.of Γ(X, U.1))
    (F.restrict U.2.fromSpec) (G.restrict U.2.fromSpec)
  have : ((F ⊗ G).restrict U.2.fromSpec).IsFinitePresentation :=
    isFinitePresentation_of_iso e.symm
  exact isFinitePresentation_of_iso ((restrictFunctorIsoPullback U.2.fromSpec).app (F ⊗ G))

end AlgebraicGeometry.Scheme.Modules
