/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-!
# Finite free coordinates for internal scalar extension

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).

The formulas are equalities of morphisms involving the canonical coequalizer projection.
They consequently specify the formulas on local elementary tensors without identifying
sections of a tensor sheaf with objectwise tensors. Finite products represent the finite
powers and, in an additive category, also the finite direct sums.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.Mod

/-- The finite-free coordinate assertion, including existence of the coequalizers and
preservation properties needed to form scalar extension. The quantification over their
instances merely allows the statement to use these consequences; it is independent of
proof choices. The finite-power functor is the constant-diagram functor followed by limit.
The chosen free module and its basis inclusions use `Mod.finiteFree` and `biproduct.ι`.

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).
-/
def FiniteFreeScalarCoordinates
    {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
    [Abelian H] : Prop :=
  Nonempty (MonoidalPreadditive H) ∧
  HasCoequalizers H ∧
  (∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X) ∧
    PreservesColimitsOfSize.{0, 0} (tensorRight X)) ∧
  ∀ [MonoidalPreadditive H] [HasCoequalizers H]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (R B : H) [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
    (φ : R ⟶ B) [IsMonHom φ] (n : ℕ)
    (θ : finiteFree R n ≅ (comap φ).obj (regular B)),
    ∃ Φ : extendScalars φ ⋙ comap φ ≅
        Functor.const (Discrete (Fin n)) ⋙ lim,
      ∀ M : Mod H R,
        (∀ i : Fin n,
          extendπ φ M ≫ (Φ.hom.app M).hom ≫
              (Pi.π (fun _ : Fin n ↦ M) i).hom =
            (θ.inv ≫ biproduct.π (fun _ : Fin n ↦ regular R) i).hom ▷ M.X ≫ γ[R,M.X]) ∧
        (Φ.inv.app M).hom =
          ∑ i : Fin n,
            (Pi.π (fun _ : Fin n ↦ M) i).hom ≫ (λ_ M.X).inv ≫
              (η[R] ≫ (biproduct.ι (fun _ : Fin n ↦ regular R) i ≫ θ.hom).hom) ▷ M.X ≫
              extendπ φ M

/-- A chosen finite free basis of a commutative ring sheaf gives a natural coordinate
isomorphism `Res (B ⊗_R -) ≅ (-)^n`, with both specified local formulas.

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).

Proof:
1. Put `e_i = θ ι_i` and `q_i = π_i θ⁻¹`. The inverse identities give
`q_i e_j = δ_ij` and `∑ e_i q_i = id`. Set `b_i = e_i(1)`. These maps commute with
restrictions, and linearity gives `e_i(r) = φ(r)b_i`. Finite powers have the componentwise
module action and sheaf gluing, as realized by the module-category finite product.
2. The bilinear rule `(s,m) ↦ q_i(s)m` induces a map from the sheafified tensor by
`sk-def-sfb-sheaf-tensor`. It equalizes the two relative-tensor arrows since
`q_i(s φ(r))m = q_i(s)(rm)`. The coequalizer of `sk-def-sfb-change-of-scalars` gives the
coordinate map. It is R-linear; assemble the coordinates into `Φ_M`.
3. Tensor the map `η_R ≫ e_i` with M after the inverse left unitor, then compose with
`extendπ`. This sends m to `b_i ⊗ m` and is R-linear by balancing and commutativity.
Sum these maps after the projections to obtain the displayed inverse tuple formula.
4. The i-th coordinate of the first composite is `∑ q_i(b_j)m_j = m_i`, so it is the
identity on each test object, hence as a module-sheaf morphism.
5. Precompose the other composite with `extendπ`. Balancing gives
`∑ b_i ⊗ q_i(s)m = ∑ b_i φ(q_i(s)) ⊗ m = s ⊗ m`.
The objectwise bilinear universal property, sheafification and coequalizer uniqueness
then give equality of sheaf morphisms, without a sectionwise tensor assertion.
6. For an R-linear f, `q_i(s)f(m) = f(q_i(s)m)` proves naturality by the same universal
properties; the inverse is natural as well. At n = 0 the basis identity is `id_B = 0`
and both sides are zero, so the empty-sum formulas apply. The sheaf tensor dependency
supplies the coequalizers and tensor-colimit preservation used in the assertion.
-/
theorem sheaf_finiteFreeScalarCoordinates
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    @FiniteFreeScalarCoordinates (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory
      (@sheafIsAbelian C _ Ab.{w} _ _ J
        (hasSheafifyEssentiallySmallSite J Ab.{w})) := by
  sorry

end CategoryTheory.Mod
