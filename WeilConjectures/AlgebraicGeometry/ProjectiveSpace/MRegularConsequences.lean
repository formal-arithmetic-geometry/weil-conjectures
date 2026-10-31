/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldGlobalSections
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.RingTheory.FiniteType

/-!
# Consequences of Castelnuovo–Mumford regularity

Source: Stacks Project, Varieties, Tags 08A3 and 08A6–08A8
(blueprint: lem-sfb-m-regular-coherent-sheaf-consequences).

The evaluation arrow is the composite of the tilde–sections counit over the base field
and the pullback–pushforward counit. Its source is precisely the extension of the vector
space of global sections to the structure sheaf. Section multiplication uses the canonical
tensor comparison for sections and the basis-normalized isomorphism of twisting sheaves.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

/-- Evaluation `Γ(X,F) ⊗_k O_X → F`, written as pullback of the associated module on
`Spec k`. Its two arrows are the tilde–sections and pullback–pushforward counits;
there is no choice of a generating family or of an evaluation map.
Source: Stacks Project, Varieties, Tag 08A8
(blueprint: lem-sfb-m-regular-coherent-sheaf-consequences). -/
def fieldEvaluation (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (F : X.Modules) :
    (Scheme.Modules.pullback p).obj
      (tilde ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj
        ((Scheme.Modules.pushforward p).obj F))) ⟶ F :=
  ((tilde.adjunction (R := CommRingCat.of k)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction p)).counit.app F

/-- The natural multiplication of sections of `F(b)` and `O(1)`, over `k`. The tensorator
of restriction of scalars sends `s ⊗_k t` to `s ⊗_Γ(O) t`; the tensor-of-sections map
and the canonical twist isomorphism then send it to the product section of `F(b+1)`.
Source: Stacks Project, Varieties, Tag 08A7
(blueprint: lem-sfb-m-regular-coherent-sheaf-consequences). -/
def regularityMultiplication (ι : Type u) (k : Type u) [Field k]
    (F : (ℙ(ι; Spec (.of k))).Modules) (b : ℤ) :
    fieldSections k (F ⊗ₘ twist ι (Spec (.of k)) b) ⊗
      fieldSections k (twist ι (Spec (.of k)) 1) ⟶
        fieldSections k (F ⊗ₘ twist ι (Spec (.of k)) (b + 1)) :=
  Functor.LaxMonoidal.μ
      (ModuleCat.restrictScalars
        (Scheme.globalSectionsRingHom k (X := ℙ(ι; Spec (.of k)))))
      ((SheafOfModules.evaluation _ (op ⊤)).obj (F ⊗ₘ twist ι (Spec (.of k)) b))
      ((SheafOfModules.evaluation _ (op ⊤)).obj (twist ι (Spec (.of k)) 1)) ≫
    (ModuleCat.restrictScalars
      (Scheme.globalSectionsRingHom k (X := ℙ(ι; Spec (.of k))))).map
      (ModuleCat.ofHom (Scheme.Modules.tensorSectionsMap
        (F ⊗ₘ twist ι (Spec (.of k)) b) (twist ι (Spec (.of k)) 1) ⊤)) ≫
    (ModuleCat.restrictScalars
      (Scheme.globalSectionsRingHom k (X := ℙ(ι; Spec (.of k))))).map
      ((SheafOfModules.evaluation _ (op ⊤)).map
        ((α_ F (twist ι (Spec (.of k)) b) (twist ι (Spec (.of k)) 1)).hom ≫
          F ◁ (twistTensorIso ι (Spec (.of k)) b 1).hom))

/-- An `a`-regular coherent module on projective `n`-space remains regular in every
larger degree, has no positive cohomology after twisting by `d ≥ a`, and has surjective
evaluation and linear multiplication in every degree `b ≥ a`.

Source: Stacks Project, Varieties, Tags 08A6–08A8, with the definition in Tag 08A3
(blueprint: lem-sfb-m-regular-coherent-sheaf-consequences).

Proof:
1. Induct simultaneously on the dimension, over all fields and all regularity indices,
   for one-step regularity and linear multiplication. In dimension zero the unique chart
   is Spec k, all twists have their standard basis, and higher cohomology vanishes by
   lem-pc-projective-space-cohomology-bound.
2. Under extension of the base field, pullback preserves quasi-coherence by
   lem-weil-pbc-module-pullback-quasi-coherent and preserves finite local generators.
   The chart rings are Noetherian by lem-weil-pbc-finite-type-algebra-noetherian, so
   pqf-lem-coherent-ft-locnoeth gives coherence of pullbacks and twists.
3. Apply lem-pc-flat-base-change-cohom to the structure morphism and a field extension.
   The finite standard affine cover proves qcqs; the field extension is flat. The twist
   bases and lem-weil-pbc-module-pullback-tensor identify pulled-back twists and products.
   The degree-zero comparison respects section multiplication. Faithful scalar extension
   detects vanishing and surjectivity. Thus extend to the infinite field k(t).
4. Apply lem-sfb-coherent-hyperplane-restriction-sequence. The adjacent vanishings of
   H^j(F(m-j)) and H^{j+1}(F(m-j-1)) make the hyperplane restriction m-regular.
5. By dimension induction it is (m+1)-regular. The hyperplane long exact sequence, with
   lem-pc-projective-space-cohomology-bound for the top degree, makes F (m+1)-regular.
   Descend to k and iterate b-a times.
6. Restrict a section of F(m+1) to the hyperplane and express it as a sum of products
   by induction. Lift the F(m) factors using H^1(F(m-1))=0 and the linear factors using
   the surjective restriction in the hyperplane node. Subtract these lifted products.
   Exactness expresses the remainder as s times a section of F(m). Twist compatibility
   identifies these as the required products. Descend and apply this at every b ≥ a.
7. For 1 ≤ j ≤ n apply regularity at b=d+j. For j>n use the cohomology bound.
8. By lem-pc-projective-space-twist-quotient and lem-pc-twist-tensor, high twists of F
   are generated by images of the coordinate monomials in nonnegative twists.
9. Iterate multiplication from b to such a d. On D_+(x_i), divide each product by
   x_i^(d-b); its coefficients are regular functions and its F(b) factors are global
   sections. Hence these sections generate F(b) on the standard cover, which says the
   canonical evaluation is epic. Empty products for d=b equal one; a zero quotient
   already gives F=0. -/
theorem mRegular_coherent_consequences (ι : Type u) [Fintype ι]
    (k : Type u) [Field k] (n : ℕ) (hι : Fintype.card ι = n + 1)
    (F : (ℙ(ι; Spec (.of k))).Modules)
    (hF : RingedSpace.IsCoherent (ℙ(ι; Spec (.of k))).toRingedSpace F)
    (a : ℤ)
    (hregular : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      Subsingleton ((RingedSpace.moduleCohomology
        (ℙ(ι; Spec (.of k))).toRingedSpace j).obj
          (F ⊗ₘ twist ι (Spec (.of k)) (a - (j : ℤ))))) :
    (∀ b : ℤ, a ≤ b → ∀ j : ℕ, 1 ≤ j → j ≤ n →
      Subsingleton ((RingedSpace.moduleCohomology
        (ℙ(ι; Spec (.of k))).toRingedSpace j).obj
          (F ⊗ₘ twist ι (Spec (.of k)) (b - (j : ℤ))))) ∧
    (∀ d : ℤ, a ≤ d → ∀ j : ℕ, 0 < j →
      Subsingleton ((RingedSpace.moduleCohomology
        (ℙ(ι; Spec (.of k))).toRingedSpace j).obj
          (F ⊗ₘ twist ι (Spec (.of k)) d))) ∧
    (∀ b : ℤ, a ≤ b →
      Epi (fieldEvaluation k (ℙ(ι; Spec (.of k)) ↘ Spec (.of k))
        (F ⊗ₘ twist ι (Spec (.of k)) b))) ∧
    (∀ b : ℤ, a ≤ b → Function.Surjective (regularityMultiplication ι k F b)) := by
  sorry

end

end AlgebraicGeometry.ProjectiveSpace
