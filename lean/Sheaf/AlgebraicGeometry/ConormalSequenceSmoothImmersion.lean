/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.Thickening
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Conormal fibre sequence for a smooth closed subscheme

Source: Stacks Project, Morphisms, Tags 06AA and 02G1
(blueprint: lem-pur-conormal-sequence-smooth-immersion).

The two arrows are characterized on generators by their differential formulas. The conormal
fibre is written as `κ ⊗[R] I.Cotangent`: since `R → S` is surjective and `I` annihilates
`I.Cotangent`, this is canonically `κ ⊗[S] (I/I²)`. Tensor factors are in Mathlib's
extension-of-scalars order.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

/-- The conormal fibre at a point of a closed immersion, using the actual stalk kernel.
Source: Stacks Project, Tag 06AA; the quotient is Mathlib's `Ideal.Cotangent`.
The `R`-balanced tensor equals the `S`-balanced tensor because `S = R/I`.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def conormalStalkFibre {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    ModuleCat (Z.residueField z) :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  ModuleCat.of _ ((Z.residueField z) ⊗[X.presheaf.stalk (i z)]
    (RingHom.ker (i.stalkMap z).hom).Cotangent)

/-- The class of a stalk-kernel element, tensored with one in the residue field.
Source: Stacks Project, Tag 06AA, first arrow of the conormal sequence.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def conormalStalkFibreClass {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z)
    (a : RingHom.ker (i.stalkMap z).hom) : conormalStalkFibre i z :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  1 ⊗ₜ[X.presheaf.stalk (i z)] (RingHom.ker (i.stalkMap z).hom).toCotangent a

/-- The fibre of the existing relative differential sheaf at `i z`, extended to `κ(z)`.
Source: Stacks Project, Tags 01UM and 06AA; stalks use the canonical module structure.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def relativeDifferentialsStalkFibre {X Z B : Scheme.{u}}
    (f : X ⟶ B) (i : Z ⟶ X) (z : Z) : ModuleCat (Z.residueField z) :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  ModuleCat.of _ ((Z.residueField z) ⊗[X.presheaf.stalk (i z)]
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i z)).obj f.relativeDifferentials))

/-- The germ of the differential of a section, tensored with one in the residue field.
Source: Stacks Project, Tags 01UM and 06AA; the derivation is the existing universal derivation.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def relativeDifferentialsStalkFibreGerm {X Z B : Scheme.{u}}
    (f : X ⟶ B) (i : Z ⟶ X) (z : Z) (U : X.Opens) (hz : i z ∈ U)
    (a : Γ(X, U)) : relativeDifferentialsStalkFibre f i z :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  1 ⊗ₜ[X.presheaf.stalk (i z)]
    (TopCat.Presheaf.germ f.relativeDifferentials.val.presheaf U (i z) hz
      (f.relativeDifferentialsDerivation.d (X := op U) a))

/-- The canonical conormal fibre sequence of a closed immersion with smooth source is short
exact. Both arrows are specified on generators: the first sends `[a] ⊗ 1` to `da ⊗ 1`,
and the second sends `da ⊗ 1` to `d(i(a)) ⊗ 1`.

Source: Stacks Project, Morphisms, Tag 06AA, with Tag 02G1 for passage to residue fields.
(blueprint: lem-pur-conormal-sequence-smooth-immersion).

Proof for stage 3, following the eight steps of the DAG node:
1. Choose an affine neighborhood `U = Spec A` of `i z`. The closed-immersion affine
   criterion (lem-weil-pbc-closed-immersion-affine-cover-criterion) identifies its preimage
   with `Spec B`, for a surjection `A → B = A/J`. Set `N = J/J²`,
   `M = B ⊗[A] Ω[A⁄k]`, and `P = Ω[B⁄k]` (def-weil-affine-spectrum,
   def-weil-pbc-kahler-differentials). The action of `B` on `N` is independent of lifts
   because changing a lift adds a product of two elements of `J`.
2. The square-zero kernel of `C = A/J² → B` defines an affine first-order thickening
   (def-sbc-first-order-thickening). Smoothness of `Z` over `k` lifts `Spec B → Z` to
   `Spec C → Z` (def-sbc-smooth-morphisms, Stacks Tag 02H0). Every prime of `C` contains
   the square-zero kernel, so this lift lands in the open `Spec B` of `Z`. Factoring
   through that open (def-weil-open-immersion) and the affine spectrum correspondence
   (def-weil-affine-spectrum) gives a `k`-algebra section `σ : B → C` of the quotient.
3. The quotient differential sequence gives `δ : N → M`, `[j] ↦ 1 ⊗ dj`, and a
   surjection `w : M → P`, `b ⊗ da ↦ b d(a mod J)`, with `ker w = im δ`
   (lem-weil-pbc-jacobi-zariski-differential-maps, Stacks Tag 00RU).
4. Define `D(a) = (a mod J²) - σ(a mod J)` in the square-zero kernel `N`. This vanishes
   on `k` and satisfies Leibniz because the kernel has square zero. Universality of
   differentials and extension of scalars give `τ : M → N`, `b ⊗ da ↦ b D(a)`
   (def-weil-pbc-kahler-differentials, def-weil-module-base-change, Tag 02HP).
   For `j ∈ J`, `D(j) = [j]`, hence `τ δ = id`.
5. For `p ∈ P`, choose a lift `m` under `w` and set `s(p) = m - δ(τ(m))`. Another lift
   differs by `δ(n)`, so `τ δ = id` proves independence and linearity. Then `w s = id`,
   `τ s = 0`, and `δ τ + s w = id`. Thus `M` is the direct sum of `N` and `P`.
6. Tensor these splitting identities with `κ(z)` over `B` (def-weil-module-base-change).
   They imply injectivity, surjectivity and middle exactness after base change: an
   element killed by the second arrow equals `δ τ` of itself. No flatness of `κ` is used.
7. The affine stalk and Spec-map formulas identify `R = Aₚ`, `S = B_q`, and the stalk
   map with the localized quotient (lem-weil-pbc-affine-open-stalk-localization,
   lem-weil-pbc-spec-map-stalk-localization). Quotient localization gives `I = JR`,
   `S = R/I`, and `I² = J²R` (lem-weil-pbc-localization-at-prime-of-quotient).
   Clearing denominators identifies the localization of `J/J²` with `I/I²`.
   Since denominators act invertibly on `κ`, balancing identifies its fibre with
   `κ ⊗[R] I.Cotangent` (def-weil-module-base-change), the first displayed module.
8. Affine agreement of the relative differential sheaf and localization of tilde stalks
   identify the other two fibres (def-sc-relative-differential-sheaf,
   lem-weil-pbc-spec-tilde-stalk-localization). For `f = j/t ∈ I`, Leibniz gives
   `d(j/t) = t⁻¹ dj - jt⁻² dt`; the second term vanishes in the fibre. Thus the first
   arrow is exactly `[f] ⊗ 1 ↦ df ⊗ 1`. The second sends `da` to `d(a mod J)` and
   obeys the same denominator rule, so it is induced by the local-ring map `R → S`.
   Cotangent classes and differential germs generate the respective fibres, so the two
   formulas in the statement determine the canonical arrows. No smoothness of `X` is used.
Source for these expansions: Stacks Tags 06AA, 00RU, 02HP and 06A8; Tag 02G1 also gives
an alternative passage to residue fields by local freeness of the final differential stalk. -/
theorem conormalStalkFibre_shortExact_of_smooth
    {k : Type u} [Field k] {X Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]
    [Smooth (Z ↘ Spec (.of k))] (z : Z) :
    ∃ (α : conormalStalkFibre i z →ₗ[Z.residueField z]
        relativeDifferentialsStalkFibre (X ↘ Spec (.of k)) i z)
      (β : relativeDifferentialsStalkFibre (X ↘ Spec (.of k)) i z →ₗ[Z.residueField z]
        relativeDifferentialsStalkFibre (Z ↘ Spec (.of k)) (𝟙 Z) z),
      Function.Injective α ∧ Function.Exact α β ∧ Function.Surjective β ∧
      (∀ (U : X.Opens) (hz : i z ∈ U) (a : Γ(X, U))
        (ha : (i.stalkMap z) (X.presheaf.germ U (i z) hz a) = 0),
        α (conormalStalkFibreClass i z ⟨X.presheaf.germ U (i z) hz a, ha⟩) =
          relativeDifferentialsStalkFibreGerm (X ↘ Spec (.of k)) i z U hz a) ∧
      (∀ (U : X.Opens) (hz : i z ∈ U) (a : Γ(X, U)),
        β (relativeDifferentialsStalkFibreGerm (X ↘ Spec (.of k)) i z U hz a) =
          relativeDifferentialsStalkFibreGerm (Z ↘ Spec (.of k)) (𝟙 Z) z
            (i ⁻¹ᵁ U) hz (i.app U a)) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
