/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemScalarProjectionData
import WeilConjectures.AlgebraicGeometry.SystemScalarTensorConstituents
import WeilConjectures.AlgebraicGeometry.SystemScalarBasisDistributivity
import WeilConjectures.AlgebraicGeometry.SystemScalarRefinementRestriction

/-! # Scalar mates and projection maps on whole coefficient systems

Source: proof of lem-coef-system-scalar-projection-identification, Steps 1--7.
(blueprint: lem-coef-system-scalar-projection-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.leftAdjoint
  HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open WeilConjectures.SemilinearSections WeilConjectures.FiniteFreeSystemRestriction
namespace WeilConjectures.SystemScalarProjection

universe c₀ v₀ r₀ u₀ v₁ w₀ x₀
open CategoryTheory.Preadditive

private theorem inverseOnDomain_eq_inv {C : Type*} [Category C] [HasZeroMorphisms C]
    {P Q : C} (a : P ⟶ Q) [IsIso a] :
    SystemProjectionFormula.inverseOnDomain a = inv a := by
  simp only [SystemProjectionFormula.inverseOnDomain, dif_pos (inferInstance : IsIso a)]

private theorem theta_isIso (C : ℕ → CommRingCat.{u + 1})
    (t : ∀ n, C (n + 1) ⟶ C n) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (M : Derived C t X)
    [IsIso (refinementGamma C t r M)] : IsIso (theta C t r M) := by
  unfold theta
  rw [inverseOnDomain_eq_inv]
  infer_instance

private theorem restriction_reflects_iso
    {C : Type c₀} [Category.{v₀} C] [EssentiallySmall.{r₀} C]
    {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r₀}}
    (φ : R ⟶ S) :
    (resD.{c₀, v₀, r₀} φ).ReflectsIsomorphisms := by
  let U := res.{c₀, v₀, r₀} φ
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ SheafOfModules.toSheaf (ring.{c₀, v₀, r₀} J R)).ReflectsIsomorphisms :=
      inferInstanceAs (SheafOfModules.toSheaf (ring.{c₀, v₀, r₀} J S)).ReflectsIsomorphisms
    exact reflectsIsomorphisms_of_comp U (SheafOfModules.toSheaf (ring.{c₀, v₀, r₀} J R))
  refine ⟨fun {P Q} a _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (U.map ((DerivedCategory.homologyFunctor _ n).map a)) :=
    (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso n) a).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ U

private theorem finite_sum_iso {C : Type u₀} [Category.{v₁} C] [Preadditive C]
    {D : Type w₀} [Category.{x₀} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {n : ℕ} {M Q : C} {P : D}
    (ι : Fin n → (M ⟶ Q)) (π : Fin n → (Q ⟶ M))
    (j : Fin n → (F.obj M ⟶ P)) (p : Fin n → (P ⟶ F.obj M))
    (hι : ∀ a b, ι a ≫ π b = if a = b then 𝟙 M else 0)
    (hπ : ∑ a, π a ≫ ι a = 𝟙 Q)
    (hp : ∑ a, p a ≫ j a = 𝟙 P)
    (q : P ⟶ F.obj Q) (hq : ∀ a, j a ≫ q = F.map (ι a)) : IsIso q := by
  classical
  let t : F.obj Q ⟶ P := ∑ a, F.map (π a) ≫ j a
  have hjt (a : Fin n) : F.map (ι a) ≫ t = j a := by
    simp [t, Preadditive.comp_sum, ← F.map_comp_assoc, hι, apply_ite, ite_comp]
  have hqt (a : Fin n) : j a ≫ q ≫ t = j a := by
    rw [← Category.assoc, hq, hjt]
  have ht : q ≫ t = 𝟙 P := by
    calc
      q ≫ t = (∑ a, p a ≫ j a) ≫ q ≫ t := by rw [hp]; simp
      _ = ∑ a, p a ≫ j a := by
        simp only [Preadditive.sum_comp, Category.assoc, hqt]
      _ = 𝟙 P := hp
  have th : t ≫ q = 𝟙 (F.obj Q) := by
    simp only [t, Preadditive.sum_comp, Category.assoc, hq, ← F.map_comp, ← F.map_sum, hπ,
      F.map_id]
  exact ⟨⟨t, ht, th⟩⟩

private theorem iso_transport_square {C : Type u₀} [Category.{v₁} C]
    {A B D E : C} (e : A ≅ B) (e' : D ≅ E)
    (f : A ⟶ D) (g : B ⟶ E) (h : f ≫ e'.hom = e.hom ≫ g) :
    e.inv ≫ f = g ≫ e'.inv := by
  apply (cancel_mono e'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, e.inv_hom_id_assoc]

private theorem span_square {C : Type u₀} [Category.{v₁} C]
    {D : Type w₀} [Category.{x₀} D] (F : C ⥤ D)
    {A A₁ A₂ : C} {B B₁ B₂ : D}
    (a : A ⟶ A₁) (b : A ⟶ A₂) [IsIso a]
    (a' : B ⟶ B₁) (b' : B ⟶ B₂) [IsIso a']
    (e : F.obj A ⟶ B) (e₁ : F.obj A₁ ⟶ B₁) (e₂ : F.obj A₂ ⟶ B₂)
    (ha : e ≫ a' = F.map a ≫ e₁) (hb : e ≫ b' = F.map b ≫ e₂) :
    e₁ ≫ inv a' ≫ b' = F.map (inv a ≫ b) ≫ e₂ := by
  apply (cancel_epi (F.map a)).1
  calc
    F.map a ≫ e₁ ≫ inv a' ≫ b' = e ≫ b' := by
      rw [← Category.assoc, ← ha]
      simp
    _ = F.map b ≫ e₂ := hb
    _ = F.map a ≫ F.map (inv a ≫ b) ≫ e₂ := by
      simp


variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L) {K : FiniteFieldDatum.{u}} {d : ℕ}
  {b : Fin d → Padic.coefficientExtensionIntegers l L} {ramification : ℕ}
  (s : Assertions l E L i K d b ramification)

private theorem comparison_isIso_from_basis (z : BasisCoordinates l E L i s)
    (X Y : Spaces K) {f : X.val.left ⟶ Y.val.left} (c : Compactification f)
    (M : Derived (A l E) (aTransition l E) X.val.left)
    (hz : z.Distributivity l E L i s X Y c M) :
    IsIso (comparison l E L i s X Y c M) := by
  let F := compact (A l E) (aTransition l E) c.i c.g
  have : F.Additive := by
    dsimp only [F, compact, J, R]
    infer_instance
  have hq : IsIso ((U l E L i Y.val.left).map (comparison l E L i s X Y c M) ≫
      (s.geometry.compactIso l E L i X (ambient Y c) Y c.i c.g).hom.app
        ((T l E L i s X).obj M)) :=
    finite_sum_iso F
      (fun a ↦ (z.inclusion X a).app M) (fun a ↦ (z.coordinate X a).app M)
      (fun a ↦ (z.inclusion Y a).app (F.obj M))
      (fun a ↦ (z.coordinate Y a).app (F.obj M))
      (z.orthogonal X M) (z.total X M) (z.total Y (F.obj M)) _ hz
  have : IsIso ((U l E L i Y.val.left).map (comparison l E L i s X Y c M)) :=
    IsIso.of_isIso_comp_right _
      ((s.geometry.compactIso l E L i X (ambient Y c) Y c.i c.g).hom.app
        ((T l E L i s X).obj M))
  have : (U l E L i Y.val.left).ReflectsIsomorphisms :=
    restriction_reflects_iso (systemInclusion l E L i Y.val.left)
  exact isIso_of_reflects_iso _ (U l E L i Y.val.left)

private theorem refinement_square_from_mates
    (X Y : Spaces K) {f : X.val.left ⟶ Y.val.left} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : Derived (A l E) (aTransition l E) X.val.left)
    (h₁ : ((s.scalars Y).scalar.adjunction.homEquiv _ _)
        (comparison l E L i s X Y c₁ M) =
      (compact (A l E) (aTransition l E) c₁.i c₁.g).map
          ((s.scalars X).scalar.adjunction.unit.app M) ≫
        (s.geometry.compactIso l E L i X (ambient Y c₁) Y c₁.i c₁.g).inv.app
          ((T l E L i s X).obj M))
    (h₂ : ((s.scalars Y).scalar.adjunction.homEquiv _ _)
        (comparison l E L i s X Y c₂ M) =
      (compact (A l E) (aTransition l E) c₂.i c₂.g).map
          ((s.scalars X).scalar.adjunction.unit.app M) ≫
        (s.geometry.compactIso l E L i X (ambient Y c₂) Y c₂.i c₂.g).inv.app
          ((T l E L i s X).obj M))
    (hr : (U l E L i Y.val.left).map
          (theta (B l E L i) (bTransition l E L i) r ((T l E L i s X).obj M)) ≫
        (s.geometry.compactIso l E L i X (ambient Y c₂) Y c₂.i c₂.g).hom.app
          ((T l E L i s X).obj M) =
      (s.geometry.compactIso l E L i X (ambient Y c₁) Y c₁.i c₁.g).hom.app
          ((T l E L i s X).obj M) ≫
        theta (A l E) (aTransition l E) r
          ((U l E L i X.val.left).obj ((T l E L i s X).obj M)))
    (hn : (compact (A l E) (aTransition l E) c₁.i c₁.g).map
          ((s.scalars X).scalar.adjunction.unit.app M) ≫
        theta (A l E) (aTransition l E) r
          ((U l E L i X.val.left).obj ((T l E L i s X).obj M)) =
      theta (A l E) (aTransition l E) r M ≫
        (compact (A l E) (aTransition l E) c₂.i c₂.g).map
          ((s.scalars X).scalar.adjunction.unit.app M)) :
    comparison l E L i s X Y c₁ M ≫
        theta (B l E L i) (bTransition l E L i) r ((T l E L i s X).obj M) =
      (T l E L i s Y).map (theta (A l E) (aTransition l E) r M) ≫
        comparison l E L i s X Y c₂ M := by
  have hr' :
      (s.geometry.compactIso l E L i X (ambient Y c₁) Y c₁.i c₁.g).inv.app
          ((T l E L i s X).obj M) ≫
        (U l E L i Y.val.left).map
          (theta (B l E L i) (bTransition l E L i) r ((T l E L i s X).obj M)) =
      theta (A l E) (aTransition l E) r
          ((U l E L i X.val.left).obj ((T l E L i s X).obj M)) ≫
        (s.geometry.compactIso l E L i X (ambient Y c₂) Y c₂.i c₂.g).inv.app
          ((T l E L i s X).obj M) := by
    exact iso_transport_square
      ((s.geometry.compactIso l E L i X (ambient Y c₁) Y c₁.i c₁.g).app
        ((T l E L i s X).obj M))
      ((s.geometry.compactIso l E L i X (ambient Y c₂) Y c₂.i c₂.g).app
        ((T l E L i s X).obj M)) _ _ hr
  apply ((s.scalars Y).scalar.adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left, h₁, h₂]
  simp only [Category.assoc]
  rw [hr', ← Category.assoc, hn]
  simp only [Category.assoc]

/-- Restriction of scalar mates equals the specified strict-system projection and is
normalized under every proper refinement, including ramified coefficient towers.

Source: blueprint finite-free compact-support coefficient comparison;
agent-formulated obligation, proof Steps 1--7
(blueprint: lem-coef-system-scalar-projection-identification).

Proof:
1. Reduce the one integral basis at all levels. The coordinate maps identify U T
   with a finite sum already on complexes of systems and commute with transitions.
   Localize this identification, with no cohomological bound.
2. Restriction preserves geometric units and counits by
   lem-coef-finite-free-system-restriction. The transpose of U(a_p) is therefore
   the pinned geometric tensorator followed by counit tensor identity and the
   specified coefficient pullback. TensorNormalization fixes this comparison on
   ordinary pure sections and total K-flat representatives, so properProjection agrees.
3. On the open, tensor balancing is identity on x tensor b and is zero off the
   open (lem-sf-open-tensor-normalization). Its inverse is openTensorInv by the
   open adjunction, independently of the scalar comparison. The finite word uses
   the published finite adjunctions and levelTensorPullback with this same open
   normalization. Compose the proper and open identities to obtain projection_eq
   in the system category, before evaluation. Semilinear derived sections identifies
   evaluation of each adjunction transpose with its finite coefficient transpose.
4. Transpose the composite by T adjoint U. The proper part is counit naturality
   with insertion of 1, and the open part inserts the same 1. This gives scalar_mate;
   no faithfulness of restriction on derived morphisms is asserted.
5. In the fixed reduced basis each constituent is finite-sum distributivity.
   Right adjoints preserve finite products, which here equal finite sums; open
   extension preserves finite sums. Thus U(c) is invertible. Exact restriction
   reflects zero cohomology, hence reflects invertibility by the cone criterion.
6. The refinement is R_p of the inverse proper/open mate followed by the specified
   compositor. Restriction preserves both factors and their inverses. For B at T M,
   invertibility of the mate follows after restriction from the A theorem applied
   to U T M, a finite sum of M. Transpose the desired square by the scalar adjunction;
   scalar_mate, the restriction refinement equation and naturality give identical
   transposes. This proves the B-system equation, not merely its restriction.
7. The A refinement laws come from lem-pur-system-compactification-pf-substitution.
   Solve the square for the B refinement using the invertible c. Cancellation then
   proves its identity, composition, common-refinement independence and cocycle.
-/
theorem system_scalar_projection_identification (_hl : l ≠ K.p)
    (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left)
    [f.IsOver (Spec (.of K.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (M : Derived (A l E) (aTransition l E) X.val.left) (_hM : domain l E L i s X M) :
    (∃ (ω : TensorPresentation l E L i s) (g : GeometryFamily l E L i s),
      (∀ c : Compactification f, Identification l E L i s ω g X Y c M) ∧
      (∀ (c : Compactification f) (n : ℕ),
        ∃ z : LevelData l E L i s X Y c n, z.Equation l E L i s g M)) ∧
    (∃ z : BasisCoordinates l E L i s,
      ∀ c : Compactification f, z.Distributivity l E L i s X Y c M) ∧
    (∀ {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂),
      IsIso (refinementGamma (A l E) (aTransition l E) r M) ∧
      IsIso (refinementGamma (B l E L i) (bTransition l E L i) r
        ((T l E L i s X).obj M)) ∧
      comparison l E L i s X Y c₁ M ≫
          theta (B l E L i) (bTransition l E L i) r ((T l E L i s X).obj M) =
        (T l E L i s Y).map (theta (A l E) (aTransition l E) r M) ≫
          comparison l E L i s X Y c₂ M) ∧
    RefinementCoherence (A l E) (aTransition l E) (f := f) M ∧
    RefinementCoherence (B l E L i) (bTransition l E L i) (f := f)
      ((T l E L i s X).obj M) := by
  obtain ⟨ω, g, hsys, hlevel⟩ :=
    normalized_scalar_tensor_constituents l E L i s _hl X Y f M _hM
  obtain ⟨z, hz⟩ := scalar_basis_distributivity l E L i s X Y f
  obtain ⟨hA, hr⟩ := scalar_refinement_restriction l E L i s _hl X Y f M _hM
  have hc (c : Compactification f) : IsIso (comparison l E L i s X Y c M) :=
    comparison_isIso_from_basis l E L i s z X Y c M (hz c M)
  have hs {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) :
      comparison l E L i s X Y c₁ M ≫
          theta (B l E L i) (bTransition l E L i) r ((T l E L i s X).obj M) =
        (T l E L i s Y).map (theta (A l E) (aTransition l E) r M) ≫
          comparison l E L i s X Y c₂ M :=
    refinement_square_from_mates l E L i s X Y r M
      (hsys c₁).2.1 (hsys c₂).2.1 (hr r).2.2.1 (hr r).2.2.2
  refine ⟨⟨ω, g, ?_, hlevel⟩, ⟨z, fun c ↦ hz c M⟩,
    (fun r ↦ ⟨(hr r).1, (hr r).2.1, hs r⟩), hA, ?_⟩
  · intro c
    exact ⟨(hsys c).1, (hsys c).2.1, hc c, (hsys c).2.2⟩
  · have hta {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) :
        IsIso (theta (A l E) (aTransition l E) r M) := by
      have := (hr r).1
      exact theta_isIso _ _ r M
    have htb {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) :
        IsIso (theta (B l E L i) (bTransition l E L i) r
          ((T l E L i s X).obj M)) := by
      have := (hr r).2.1
      exact theta_isIso _ _ r _
    have hspan {c₁ c₂ a : Compactification f}
        (r : a.Refinement c₁) (z : a.Refinement c₂) :
        comparison l E L i s X Y c₁ M ≫
            commonComparison (B l E L i) (bTransition l E L i) r z
              ((T l E L i s X).obj M) =
          (T l E L i s Y).map (commonComparison (A l E) (aTransition l E) r z M) ≫
            comparison l E L i s X Y c₂ M := by
      have := hta r
      have := htb r
      simp only [commonComparison, inverseOnDomain_eq_inv]
      exact span_square (T l E L i s Y) _ _ _ _ _ _ _ (hs r) (hs z)
    constructor
    · intro c
      have := hc c
      apply (cancel_epi (comparison l E L i s X Y c M)).1
      rw [hs, hA.identity, CategoryTheory.Functor.map_id]
      simp
    · intro c₁ c₂ c₃ r z
      have := hc c₁
      apply (cancel_epi (comparison l E L i s X Y c₁ M)).1
      rw [hs, hA.composition, Functor.map_comp]
      simp only [Category.assoc]
      rw [← hs z, ← Category.assoc, ← hs r]
      rw [Category.assoc]
    · intro c₁ c₂ a a' r z r' z'
      have := hc c₁
      apply (cancel_epi (comparison l E L i s X Y c₁ M)).1
      rw [hspan r z, hspan r' z', hA.independent r z r' z']
    · intro c₁ c₂ c₃ a a' a'' r z r' z' r'' z''
      have := hc c₁
      apply (cancel_epi (comparison l E L i s X Y c₁ M)).1
      rw [← Category.assoc, hspan r z, Category.assoc, hspan r' z',
        ← Category.assoc, ← Functor.map_comp, hA.cocycle r z r' z' r'' z'',
        hspan r'' z'']

end WeilConjectures.SystemScalarProjection
