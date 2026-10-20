/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
import WeilConjectures.CategoryTheory.Monoidal.TensorInverse
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-!
# Scalar endomorphisms of a shifted Tate line

Source: blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-finite-dualizing, affine-space Tate rank-one reduction; extracted scalar argument
(blueprint: lem-coef-connected-tate-line-endomorphisms).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The tensor-power finite Tate sheaf, placed in degree zero and shifted by `d`.
Source: blueprint, lem-coef-finite-dualizing, affine-space Tate rank-one reduction
(blueprint: lem-coef-connected-tate-line-endomorphisms).
The existing `finiteEtaleTateSheaf` restricts on nonnegative integers to the tensor powers;
no new Tate-twist construction is introduced here. -/
def shiftedFiniteEtaleTateLine (B : Type (u + 1)) [CommRing B] (N : ℕ)
    (Y : Scheme.{u}) (hB : (N : B) = 0) (r : ℕ) (d : ℤ) :
    Etale.DerivedCategoryModule B Y :=
  (shiftFunctor (Etale.DerivedCategoryModule B Y) d).obj
    ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf B N Y hB (r : ℤ)))

private theorem scalar_bijective_module (B : Type (u + 1)) [CommRing B] :
    Function.Bijective (fun b : B => b • 𝟙 (ModuleCat.of B B)) := by
  constructor
  · intro a b h
    have hh := congrArg (fun f : ModuleCat.of B B ⟶ ModuleCat.of B B => f 1) h
    simpa using hh
  · intro f
    refine ⟨f 1, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    simp

private theorem scalar_bijective_map
    {B : Type*} [CommRing B] {C D : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear B C] [Category D] [Preadditive D]
    [CategoryTheory.Linear B D] (F : C ⥤ D) [F.Linear B] [F.Full] [F.Faithful]
    (X : C) (h : Function.Bijective (fun b : B => b • 𝟙 X)) :
    Function.Bijective (fun b : B => b • 𝟙 (F.obj X)) := by
  have he : (fun b : B => b • 𝟙 (F.obj X)) = F.map ∘ (fun b : B => b • 𝟙 X) := by
    funext b
    simp
  rw [he]
  exact (show Function.Bijective F.map from ⟨F.map_injective, F.map_surjective⟩).comp h

private theorem scalar_bijective_iso
    {B : Type*} [CommRing B] {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear B C] {X Y : C} (e : X ≅ Y)
    (h : Function.Bijective (fun b : B => b • 𝟙 X)) :
    Function.Bijective (fun b : B => b • 𝟙 Y) := by
  have he : (fun b : B => b • 𝟙 Y) =
      (fun f : X ⟶ X => e.inv ≫ f ≫ e.hom) ∘ (fun b : B => b • 𝟙 X) := by
    funext b
    simp
  rw [he]
  exact (Iso.homCongr e e).bijective.comp h

private theorem scalar_bijective_constant (B : Type (u + 1)) [CommRing B]
    (Y : Scheme.{u}) [ConnectedSpace Y] :
    Function.Bijective (fun b : B => b • 𝟙
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B))) :=
  scalar_bijective_map
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
    (ModuleCat.of B B) (scalar_bijective_module B)

private theorem scalar_bijective_complex (B : Type (u + 1)) [CommRing B]
    (Y : Scheme.{u}) [ConnectedSpace Y] :
    Function.Bijective (fun b : B ↦ b • 𝟙 (Etale.constantComplex B Y)) :=
  scalar_bijective_iso (Etale.singleFunctorObjUnitIso (ModuleCat B) Y)
    (scalar_bijective_map (DerivedCategory.singleFunctor _ 0) _
      (scalar_bijective_constant B Y))

private theorem reflects_iso_of_scalar_bijective
    {B : Type*} [CommRing B] {C D : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear B C] [Category D] [Preadditive D]
    [CategoryTheory.Linear B D] (G : C ⥤ D) [G.Linear B] (X : C)
    (hX : Function.Bijective (fun b : B ↦ b • 𝟙 X))
    (hGX : Function.Bijective (fun b : B ↦ b • 𝟙 (G.obj X)))
    (v : X ⟶ X) [IsIso (G.map v)] : IsIso v := by
  have hinj : Function.Injective (G.map (X := X) (Y := X)) := by
    intro f g hfg
    obtain ⟨a, rfl⟩ := hX.surjective f
    obtain ⟨b, rfl⟩ := hX.surjective g
    have hab : a = b := hGX.injective (by simpa using hfg)
    exact congrArg (fun c : B ↦ c • 𝟙 X) hab
  obtain ⟨b, hb⟩ := hGX.surjective (inv (G.map v))
  let w := b • 𝟙 X
  have hw : G.map w = inv (G.map v) := by simpa [w] using hb
  refine ⟨⟨w, ?_, ?_⟩⟩
  · apply hinj
    rw [G.map_id, G.map_comp, hw, IsIso.hom_inv_id]
  · apply hinj
    rw [G.map_id, G.map_comp, hw, IsIso.inv_hom_id]

attribute [local irreducible] shiftedFiniteEtaleTateLine in
/-- Scalars give every endomorphism of the shifted Tate line, uniquely. A `B`-linear
functor carrying this line to the constant coefficient complex detects its invertible
endomorphisms.

Source: blueprint, lem-coef-finite-dualizing, affine-space Tate rank-one reduction,
extracted agent-written scalar argument; Stacks, Tags 06XS and 03P5
(blueprint: lem-coef-connected-tate-line-endomorphisms).

Proof:
1. By lem-asd-etale-finite-twist-pullback the Tate sheaf is locally free of rank one.
Cancel the shifts using def-weil-abstract-derived-category; shift linearity is supplied by
lem-weil-linear-abelian-derived-category. By lem-weil-pbc-derived-single-fully-faithful its
unshifted derived endomorphisms are precisely module-sheaf endomorphisms. In local bases
write f(e_i) = a_i e_i. On overlaps e_j = u_ij e_i with u_ij a unit, so linearity and
commutativity give a_j u_ij = u_ij a_i and hence a_j = a_i. Glue by the sheaf axiom. This
identifies endomorphisms with sections of B_Y, respecting addition, multiplication and one.
2. Apply lem-weil-pbc-constant-sheaf-sections-connected to the additive group of B: because
Y is nonempty and connected, its constant sections are exactly B, via the constant-section
map. The local calculation identifies that map with b mapping to b times the identity.
3. Write v = b times the identity. By def-weil-linear-category and the linearity of G,
G(v) is the same scalar on G(L). Transport along the given isomorphism to the coefficient
complex on Spec k. Apply the first two steps to Spec k. An inverse to this scalar map
corresponds to c in B, with bc = cb = 1, so b is a unit.
4. The endomorphism c times the identity on L is a two-sided inverse to v. Thus G detects
invertibility on these endomorphisms. The argument also applies to B = 0 and r = 0. -/
theorem connected_tate_line_endomorphisms
    (k : Type u) [Field k] [IsAlgClosed k]
    (N : ℕ) (hN : 0 < N) (hInvertible : IsUnit (N : k))
    (B : Type (u + 1)) [CommRing B] (hB : (N : B) = 0)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] [ConnectedSpace Y] (r : ℕ) (d : ℤ) :
    Function.Bijective
      (fun b : B => b • 𝟙 (shiftedFiniteEtaleTateLine B N Y hB r d)) ∧
    (∀ (G : Etale.DerivedCategoryModule B Y ⥤
        Etale.DerivedCategoryModule B (Spec (.of k))) [G.Linear B],
      Nonempty (G.obj (shiftedFiniteEtaleTateLine B N Y hB r d) ≅
        Etale.constantComplex B (Spec (.of k))) →
      ∀ v : shiftedFiniteEtaleTateLine B N Y hB r d ⟶
          shiftedFiniteEtaleTateLine B N Y hB r d,
        IsIso (G.map v) → IsIso v) := by
  classical
  have hY : IsUnit (N : Γ(Y, ⊤)) := by
    let f : k →+* Γ(Y, ⊤) :=
      ((Y ↘ Spec (.of k)).appTop).hom.comp (ΓSpecIso (.of k)).inv.hom
    simpa using hInvertible.map f
  let p := (finiteEtaleTwistPullbackData B N hN hB).p
  let F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) :=
    finiteEtaleTateSheaf B N Y hB (r : ℤ)
  let M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) :=
    finiteEtaleTateSheaf B N Y hB (-(r : ℤ))
  let e : MonoidalCategory.TensorInverse F :=
    { obj := M
      rightIso := p Y hY (r : ℤ) (-(r : ℤ)) ≪≫ eqToIso (by
        simp only [add_neg_cancel]
        rfl)
      leftIso := p Y hY (-(r : ℤ)) (r : ℤ) ≪≫ eqToIso (by
        simp only [neg_add_cancel]
        rfl) }
  have := e.fullyFaithfulTensorLeft.full
  have := e.fullyFaithfulTensorLeft.faithful
  have hF : Function.Bijective (fun b : B => b • 𝟙 F) :=
    scalar_bijective_iso (MonoidalCategory.rightUnitor F)
      (scalar_bijective_map (MonoidalCategory.tensorLeft F) _
        (scalar_bijective_constant B Y))
  have hL : Function.Bijective
      (fun b : B => b • 𝟙 (shiftedFiniteEtaleTateLine B N Y hB r d)) := by
    unfold shiftedFiniteEtaleTateLine
    exact scalar_bijective_map (shiftFunctor _ d) _
      (scalar_bijective_map (DerivedCategory.singleFunctor _ 0) F hF)
  refine ⟨hL, ?_⟩
  intro G _ he v hv
  obtain ⟨he⟩ := he
  exact reflects_iso_of_scalar_bijective G _ hL
    (scalar_bijective_iso he.symm (scalar_bijective_complex B (Spec (.of k)))) v

end AlgebraicGeometry.Scheme
