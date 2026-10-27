module

public import Sheaf.Paper.AdicNormalizedFibrePullback
public import Sheaf.Paper.PerAdicNormalizedFibreComparisons
import Sheaf.Paper.ScalarFibreComponents
import Sheaf.Paper.ScalarFibreNaturality
import Sheaf.Paper.ScalarFibreCoherence

/-! # Normalized geometric fibres and finite ramified scalar extension

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Remark 6.8.15
(blueprint: lem-per-adic-normalized-fibre-scalar).

Only the definitions of the combined-comparison module are used. Its theorem is
not a premise. Its future proof import of this module must be omitted to avoid
an import cycle (stages/2-statements.md, section 3.7).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- Scalar comparisons with the specified reduction-cone normalization and raw
associators, on the same fibres and pullbacks as the pullback assertion.
Source: BS 6.8.4(1),(4), 6.8.15
(blueprint: lem-per-adic-normalized-fibre-scalar). -/
structure NormalizedScalar (ω : Fibres (k := k) l R)
    (α : NormalizedPullback l R ω) where
  scalar : ∀ (A B : Type u) [Field A] [Field B]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    heartScalar l A B i X ⋙ ((ω B X).point κ x).functor ≅
      ((ω A X).point κ x).functor ⋙ ModuleCat.extendScalars i.toRingHom
  scalar_id : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : FiniteTypeBase k),
    ∃ e : heartScalar l A A (AlgHom.id ℚ_[l] A) X ≅ 𝟭 _,
      (∀ F, HEq (e.hom.app F).hom
        ((pbcRationalScalarUnit l A X.scheme (base l X).dimension
          (base l X).prime_unit).hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        (scalar A A (AlgHom.id ℚ_[l] A) X κ x).hom.app F ≫
          (ModuleCat.extendScalarsId.{u, u + 1} A).hom.app
            (((ω A X).point κ x).functor.obj F) =
          ((ω A X).point κ x).functor.map (e.hom.app F)
  scalar_comp : ∀ (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    [FiniteDimensional ℚ_[l] C] (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C)
    (X : FiniteTypeBase k),
    ∃ e : heartScalar l A B i X ⋙ heartScalar l B C j X ≅
      heartScalar l A C (j.comp i) X,
      (∀ F, HEq (e.hom.app F).hom
        (pbcRationalScalarCompComponent l A B C i j X.scheme
          (base l X).dimension (base l X).prime_unit F.obj).hom) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        ((ω C X).point κ x).functor.map (e.hom.app F) ≫
          (scalar A C (j.comp i) X κ x).hom.app F ≫
            (ModuleCat.extendScalarsComp.{u, u + 1} i.toRingHom j.toRingHom).hom.app
              (((ω A X).point κ x).functor.obj F) =
          (scalar B C j X κ x).hom.app ((heartScalar l A B i X).obj F) ≫
            (ModuleCat.extendScalars.{u, u, u + 1} j.toRingHom).map
              ((scalar A B i X κ x).hom.app F)
  mixed : ∀ (A B : Type u) [Field A] [Field B]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme),
    ∃ e : heartScalar l A B i X ⋙ heartPull l B R g ≅
      heartPull l A R g ⋙ heartScalar l A B i Y,
      (∀ F, HEq (e.hom.app F).hom
        ((R.mixed A B i (X := base l Y) (Y := base l X) g).raw.hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        ((ω B Y).point κ y).functor.map (e.hom.app F) ≫
          (scalar A B i Y κ y).hom.app ((heartPull l A R g).obj F) ≫
            (ModuleCat.extendScalars i.toRingHom).map ((α.pull A g κ y).hom.app F) =
          (α.pull B g κ y).hom.app ((heartScalar l A B i X).obj F) ≫
            (scalar A B i X κ (y ≫ g)).hom.app F

  unit_normalization : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l A (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme A))
    (e : (R.realization A (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M),
    ∃ e' : (R.realization B (base l X)).J.obj ((heartScalar l A B i X).obj F).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((pbcExtend (R.fieldChange A B i (base l X)).coefficient).obj M),
      e'.hom = scalarModelMap l R A B i X F M e ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (U : X.scheme.ProEt)
        (q : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange x).obj U)
        (m : M.val.obj (op U)),
        ∀ b : B,
        (presentedFibre l R B ω X ((heartScalar l A B i X).obj F) _ e' κ x).hom
          (((scalar A B i X κ x).inv.app F)
            (b ⊗ₜ[A, i.toRingHom] (presentedFibre l R A ω X F M e κ x).inv
              (germ l A M κ x U q m))) =
          b • germ l B _ κ x U q
            (pbcTensorSection (R.fieldChange A B i (base l X)).coefficient M (op U) 1 m)

  local_normalization :
    ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
      (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
      (F : NormalizedFibre.Heart l A (base l X)) (C : NormalizedFibre.Chart l (base l X))
      (hA : C.Adapted l A (R.realization A (base l X)) F)
      (N : NormalizedFibre.Lattice l A C.scheme)
      (φ : (C.restrict l A (R.realization A (base l X))).obj F ≅ N.rational l A),
      ∃ (hB : C.Adapted l B (R.realization B (base l X))
        ((heartScalar l A B i X).obj F))
        (M : NormalizedFibre.Lattice l B C.scheme)
        (ψ : (C.restrict l B (R.realization B (base l X))).obj
          ((heartScalar l A B i X).obj F) ≅ M.rational l B)
        (r : rationalCoefficientSheaf l C.scheme A ⟶ rationalCoefficientSheaf l C.scheme B)
        (q : (C.restrict l B (R.realization B (base l X))).obj
          ((heartScalar l A B i X).obj F) ≅
            (pbcExtend r).obj ((C.restrict l A (R.realization A (base l X))).obj F))
        (η : (pbcExtend r).obj (N.rational l A) ≅ M.rational l B)
        (τ : ∀ n : ℕ, finiteScalarLevel l A B i C.scheme (N.system.obj (op n)) n ≅
          M.system.obj (op n)),
        IsScalarChartMap l R A B i X F C r q ∧ IsScalarLattice l A B i C.scheme N M r η τ ∧
        ψ.hom = q.hom ≫ (pbcExtend r).map φ.hom ≫ η.hom ∧
        ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
        ∃ (e : scalarQuotients l A B i (N.fiber l A κ t) ≅
          M.system ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber
            (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l B)))
          (a : (ModuleCat.extendScalars.{u, u, u + 1}
            (WeilConjectures.integralScalarIntegerInclusion l A B i)).obj
              (N.fiber l A κ t) ≅ M.fiber l B κ t),
          (∀ (n : ℕ) (w : N.fiber l A κ t) (b : Padic.coefficientExtensionIntegers l B)
            (U : C.scheme.Etale) (x : (pointSmallEtale t).ulift.{u + 1}.fiber.obj U)
            (m : (N.system.obj (op n)).obj.obj (op U)),
            limit.π (N.system ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber
              (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A))) (op n) w =
                (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber U x
                  (N.system.obj (op n)).obj m →
            (e.hom.app (op n))
              ((Padic.coefficientExtensionIdeal l B 1 ^ (n + 1) • ⊤ :
                Submodule (Padic.coefficientExtensionIntegers l B)
                  ((ModuleCat.extendScalars.{u, u, u + 1}
                    (WeilConjectures.integralScalarIntegerInclusion l A B i)).obj
                      (N.fiber l A κ t))).mkQ
                (b ⊗ₜ[Padic.coefficientExtensionIntegers l A,
                  WeilConjectures.integralScalarIntegerInclusion l A B i] w)) =
              b • (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber U x
                (M.system.obj (op n)).obj
                  ((τ n).hom.hom.app (op U)
                    ((finiteScalarUnit l A B i C.scheme (N.system.obj (op n)) n).hom.app
                      (op U) m))) ∧
          a.hom ≫ limMap (J := ℕᵒᵖ)
              (C := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l B)) e.inv =
            scalarCompletionMap l A B i (N.fiber l A κ t) ∧
          ∀ (b : B) (a₀ : A) (n : N.fiber l A κ t),
            ((ω B X).normalization C ((heartScalar l A B i X).obj F) hB M ψ κ t).hom
              (((scalar A B i X κ (t ≫ C.map)).inv.app F)
                (b ⊗ₜ[A, i.toRingHom]
                  ((ω A X).normalization C F hA N φ κ t).inv
                    (a₀ ⊗ₜ[Padic.coefficientExtensionIntegers l A,
                      (Padic.coefficientExtensionIntegers l A).subtype] n))) =
              (b * i a₀) •
                ((1 : B) ⊗ₜ[Padic.coefficientExtensionIntegers l B,
                  (Padic.coefficientExtensionIntegers l B).subtype]
                  (a.hom ((1 : Padic.coefficientExtensionIntegers l B) ⊗ₜ[
                    Padic.coefficientExtensionIntegers l A,
                    WeilConjectures.integralScalarIntegerInclusion l A B i] n)))

/-- Normalized geometric fibres commute with finite ramified coefficient extension.
The algebraic closure only labels finite stages; the assertion is invariant under
coefficient-field isomorphisms and hence quantifies all finite Q_l-fields and embeddings.
There is no rank-locus or common-stage descent assertion here.

Source: BS 6.8.4(1),(4), 6.8.15
(blueprint: lem-per-adic-normalized-fibre-scalar).

Proof plan (the seven node steps):
1. Use lem-per-lisse-completed-system-comparison and def-pod-lisse-l-adic-sheaves
on an arbitrary adapted affine etale chart. The actual scalar lattice is the ordinary
finite-free completed tensor. The comparison of
lem-per-rational-realization-scalar-coherence identifies it with the specified raw T.
2. By lem-pod-adic-tower-reconstruction, M/t^n M is the nth stalk. At target exponent
m, t^ceil(m/e) vanishes modulo v^m. Apply lem-pod-etale-stalk-tensor-scalar to this
possibly non-flat quotient map. Its tensor-of-germ formula gives M tensor_A D/v^m.
The cofinal exponent m used by finiteScalarLevel gives the same quotient and unit.
3. By lem-per-adic-normalized-fibre-exactness, M is finite free. The actual reduction
cone on D tensor_A M is coordinatewise D^r to lim (D/v^m)^r. Completeness of L and
the DVR valuation (lem-weil-l-adic-extension-complete and
lem-weil-l-adic-extension-integers-dvr) make it bijective, also when r=0. Projection
compatibility fixes its map independently of the basis and proves integral naturality.
4. Invert this reduction-cone isomorphism and invert v. Since t is a unit times v^e,
both sides become L tensor_A M. Balancing gives beta in the stated direction. The
local_normalization equation specifies its inverse on every pure tensor.
5. Integral naturality from the finite germ formula extends to u/t^a by multiplying
both sides by t^(-a). Equal fractions differ by a uniformizer-power-annihilated map,
which becomes zero. Full faithfulness in the completed-system comparison and common
refinements identify all chart, lattice and adapted-stratification choices by conjugacy.
6. For E to L to P, both balanced maps send the nested pure tensor to the product
of its coefficients; the identity inserts one. The finite stalk-scalar theorem and
realization scalar coherence identify these with the specified scalar associators.
They commute with quotient projections, so the equations pass to limits and localization.
7. For g:Y to X, the inverse-image germ theorem sends a pulled germ to its original
germ. Apply the scalar germ formula to see equality of the two mixed composites on
generators, including non-flat quotients. Pass through projections, limits and the inverse
completion map. The normalized pullback theorem fixes alpha and supplies its identity
and scheme-composition equations; scalar_id, scalar_comp and mixed supply the rest. -/
theorem adic_normalized_fibre_scalar :
    ∃ (ω : Fibres (k := k) l R) (α : NormalizedPullback l R ω),
      Nonempty (NormalizedScalar l R ω α) := by
  obtain ⟨ω, α, ⟨d⟩⟩ := scalar_fibre_components (k := k) l R
  have h := scalar_fibre_coherence l R ω α d
  let β (A B : Type u) [Field A] [Field B]
      [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
      (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme) :
      heartScalar l A B i X ⋙ ((ω B X).point κ x).functor ≅
        ((ω A X).point κ x).functor ⋙ ModuleCat.extendScalars i.toRingHom :=
    NatIso.ofComponents (d.component A B i X κ x)
      (fun f ↦ scalar_fibre_naturality l R ω d A B i X κ x _ _ f)
  refine ⟨ω, α, ⟨{
    scalar := β
    scalar_id := ?_
    scalar_comp := ?_
    mixed := ?_
    unit_normalization := d.unit_normalization
    local_normalization := d.local_normalization }⟩⟩
  · intro A _ _ _ X
    exact ⟨scalarHeartUnit l A X, fun _ ↦ HEq.rfl, h.scalar_id A X⟩
  · intro A B C _ _ _ _ _ _ _ _ _ i j X
    refine ⟨scalarHeartComp l A B C i j X, ?_, h.scalar_comp A B C i j X⟩
    intro F
    unfold scalarHeartComp pbcRationalScalarComp
    exact HEq.rfl
  · intro A B _ _ _ _ _ _ i X Y g
    exact ⟨scalarHeartMixed l R A B i X Y g, fun _ ↦ HEq.rfl,
      h.mixed A B i X Y g⟩

end AlgebraicGeometry.Scheme.AdicFibreComparison
