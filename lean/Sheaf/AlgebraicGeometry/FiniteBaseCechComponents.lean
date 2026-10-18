module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Finite-base Čech component comparison

Source: Orgogozo, *Modifications et cycles proches sur une base générale*, Lemma 2.6.1,
printed p. 5 (blueprint: lem-trf-finite-base-cech-components).
-/

universe u

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A finite Čech stage of a morphism `p : Z ⟶ S`, carrying its structure map to `S`.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-base-cech-components). -/
structure CechStage (S : Scheme.{u}) where
  carrier : Scheme.{u}
  map : carrier ⟶ S

/-- The `q`-fold finite Čech fibre product of `p`, with `q = 0` equal to `Z`.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-base-cech-components). -/
noncomputable def cechStage {Z S : Scheme.{u}} (p : Z ⟶ S) : ℕ → CechStage S
  | 0 => ⟨Z, p⟩
  | q + 1 =>
      let prev := cechStage p q
      ⟨pullback prev.map p, pullback.fst prev.map p ≫ prev.map⟩

/-- Projection from the fibre of the base-changed morphism to the original fibre.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-base-cech-components). -/
noncomputable def finiteBaseFiberProjection {Z S U : Scheme.{u}}
    (p : Z ⟶ S) (h : U ⟶ S) {Ω : Type u} [Field Ω]
    (b_U : Spec (.of Ω) ⟶ U) :
    pullback (pullback.fst h p) b_U ⟶ pullback p (b_U ≫ h) :=
  pullback.map (pullback.fst h p) b_U p (b_U ≫ h)
    (pullback.snd h p) (𝟙 _) h (pullback.condition) (Category.id_comp _).symm

/--
For a finite morphism, base change along a geometric point preserves the connected
components of the geometric fibre, and the same holds for every finite Čech stage.

Source: Orgogozo, *Modifications et cycles proches sur une base générale*, Lemma 2.6.1,
printed p. 5 (blueprint: lem-trf-finite-base-cech-components).

Proof: The fibre of `U ×_S Z → U` at `b_U` is canonically identified with the fibre of
`Z → S` at `b_U ≫ h` by the universal property of the fibre product, and the induced
map is `finiteBaseFiberProjection`. Connected components are therefore in bijection.
For the iterated clause, finite morphisms are preserved by base change and composition,
so induction gives finiteness of every Čech stage, after which the same comparison applies.
-/
theorem finite_base_cech_components {Z S U : Scheme.{u}} (p : Z ⟶ S)
    [IsFinite p] (h : U ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (b_U : Spec (.of Ω) ⟶ U) :
    Function.Bijective
      (finiteBaseFiberProjection p h b_U).continuous.connectedComponentsMap ∧
      ∀ q : ℕ,
        Function.Bijective
          (Continuous.connectedComponentsMap
            (finiteBaseFiberProjection (cechStage p q).map h b_U).continuous) := by
  sorry

end AlgebraicGeometry

end
