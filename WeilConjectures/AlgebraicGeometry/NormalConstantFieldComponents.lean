/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.AlgebraicClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldBasic
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentCore
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentsTail

/-! # Constant fields and geometric components of normal finite-field schemes

Source: Stacks Project, varieties.tex, Tags 04PZ, 054Q and 0C3M; fields.tex,
Tag 037J; the cyclic labels are the embeddings of the finite constant field.
(blueprint: lem-dl-a1-normal-constant-field-components).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The constant field of a connected normal finite-type finite-field scheme is finite,
extends to global sections, and labels the clopen geometric components cyclically.
The existential instances are conclusions, not assumptions: integrality first supplies
its function field, and the algebra structure is fixed by the structure morphism's generic
map. The equality with `algebraicClosure` fixes L as the actual subfield of that function
field. The Cartesian square and the two projection equations specify C and its canonical
map j up to unique isomorphism. The lift of eta fixes the embedding of constants in k.
All translates have domain C, so the connected, normal and Noetherian assertions about C
apply to every translated component. The last three projection identities specify the
restriction of Phi^d to C as id times Spec of inverse q^d-power Frobenius.

Source: Stacks Project, varieties.tex, Tags 04PZ (proof of
lemma-image-connected-component), 054Q (lemma-geometrically-irreducible-function-field),
0C3M (lemma-base-change-normal-by-separable); fields.tex, Tag 037J.
(blueprint: lem-dl-a1-normal-constant-field-components).

Proof, in the three steps of the node:
1. Finite type over the field makes U0 locally Noetherian. A connected locally Noetherian
   scheme with domain stalks is irreducible (`irreducibleSpace_of_isDomain_stalk`); domain
   stalks make it reduced, so U0 is integral.
2. lem-dl-a1-normal-constant-field-basic constructs the canonical function-field algebra,
   L, the global-section inclusion e, the geometrically connected factorization g and d.
3. For a geometric generic point, lem-dl-a1-normal-constant-field-component-core gives
   sigma, C, p, s, j with the clopen-component, connectedness, Noetherian and normality
   clauses; lem-dl-a1-normal-constant-field-components-tail, applied to the same witnesses,
   gives the Frobenius orbit, covering, successor and return clauses. -/
theorem normal_constant_field_components
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom]
    (hN : ∀ x : U₀.left, IsDomain (U₀.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk x)) :
    ∃ (_ : IsIntegral U₀.left) (_ : Algebra D.k₀ U₀.left.functionField),
      algebraMap D.k₀ U₀.left.functionField =
        ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ U₀.hom.appTop ≫
          (@Scheme.germToFunctionField U₀.left inferInstance ⊤
            ⟨⟨Classical.choice inferInstance, trivial⟩⟩)).hom ∧
      ∃ (L : IntermediateField D.k₀ U₀.left.functionField),
        L = algebraicClosure D.k₀ U₀.left.functionField ∧ Module.Finite D.k₀ L ∧
        ∃ (e : L →+* Γ(U₀.left, ⊤)) (g : U₀.left ⟶ Spec (CommRingCat.of L)),
          ((@Scheme.germToFunctionField U₀.left inferInstance ⊤
            ⟨⟨Classical.choice inferInstance, trivial⟩⟩)).hom.comp e = L.subtype ∧
          g = U₀.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e) ∧
          g ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ L)) = U₀.hom ∧
          GeometricallyConnected g ∧
          ∃ d : ℕ, d = Module.finrank D.k₀ L ∧ 1 ≤ d ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (η : Spec (CommRingCat.of Ω) ⟶ (D.geometricFiber U₀).left),
            (∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
              IsGenericPoint
                ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 Z) →
            ∃ (σ : L →ₐ[D.k₀] D.k) (C : Scheme.{u})
              (p : C ⟶ U₀.left) (s : C ⟶ Spec (CommRingCat.of D.k))
              (j : C ⟶ (D.geometricFiber U₀).left),
              IsPullback p s g (Spec.map (CommRingCat.ofHom σ.toRingHom)) ∧
              j ≫ pullback.fst U₀.hom
                (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = p ∧
              j ≫ pullback.snd U₀.hom
                (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = s ∧
              (∃ ηC : Spec (CommRingCat.of Ω) ⟶ C, ηC ≫ j = η) ∧
              IsOpenImmersion j ∧ IsClosedImmersion j ∧
              Set.range j = connectedComponent
                ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 ∧
              ConnectedSpace C ∧ IsNoetherian C ∧
              (∀ x : C, IsDomain (C.presheaf.stalk x) ∧
                IsIntegrallyClosed (C.presheaf.stalk x)) ∧
              (∀ i : Fin d,
                IsOpenImmersion (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom) ∧
                IsClosedImmersion (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)) ∧
              (∀ x : (D.geometricFiber U₀).left, ∃ i : Fin d,
                connectedComponent x =
                  Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)) ∧
              (Pairwise fun i i' : Fin d ↦
                Disjoint (Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom))
                  (Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i' : ℕ)).hom))) ∧
              (⋃ i : Fin d, Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)) =
                Set.univ ∧
              (∀ i : Fin d,
                (D.geometricFrobenius U₀).hom ''
                    Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom) =
                  Set.range (j ≫ (D.geometricFrobenius U₀ ^ (((i : ℕ) + 1) % d)).hom)) ∧
              ∃ r : C ≅ C,
                r.hom ≫ j = j ≫ (D.geometricFrobenius U₀ ^ d).hom ∧
                r.hom ≫ p = p ∧
                r.hom ≫ s = s ≫ Spec.map (CommRingCat.ofHom
                  ((@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _
                    (Fintype.ofFinite D.k₀) D.k _ _ _).symm ^ d).toRingHom) := by
  classical
  have hdom : ∀ x : U₀.left, IsDomain (U₀.left.presheaf.stalk x) := fun x ↦ (hN x).1
  have : IsLocallyNoetherian U₀.left := LocallyOfFiniteType.isLocallyNoetherian U₀.hom
  have : IrreducibleSpace U₀.left := irreducibleSpace_of_isDomain_stalk U₀.left hdom
  have : IsReduced U₀.left := by
    apply isReduced_of_isReduced_stalk
  have hInt : IsIntegral U₀.left := isIntegral_of_irreducibleSpace_of_isReduced U₀.left
  obtain ⟨algebra, ⟨b⟩⟩ := exists_normal_constant_field_basic D U₀ hN
  refine ⟨hInt, algebra, b.algebraMap_eq, b.L, b.L_eq, b.finite, ?_⟩
  refine ⟨b.e, b.g, b.germ_e, b.g_eq, b.factor, b.geometricallyConnected, b.d,
    b.d_eq, b.d_pos, ?_⟩
  intro Ω _ _ η hη
  obtain ⟨σ, C, p, s, j, hpb, hp, hs, hηC, ho, hc, hrange, hconn, hnoeth, hnormal⟩ :=
    normal_constant_field_component_core D U₀ hN b Ω η hη
  have horbit := normal_constant_field_components_tail D U₀ b σ C p s j hpb hp hs ho hc
  exact ⟨σ, C, p, s, j, hpb, hp, hs, hηC, ho, hc, hrange, hconn, hnoeth, hnormal,
    horbit⟩

end AlgebraicGeometry
