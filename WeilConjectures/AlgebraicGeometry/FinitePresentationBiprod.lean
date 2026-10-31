/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietorisSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite presentation of a binary direct sum of module sheaves

Source: Stacks Project, Properties, Lemma 01PJ, proof, and Modules, Definition 01BN
(blueprint: lem-weil-pbc-module-finite-presentation-direct-sum).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSpace

private theorem finite_biprod_presentation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (P : M.Presentation) (Q : N.Presentation)
    [P.IsFinite] [Q.IsFinite] :
    ∃ T : (M ⊞ N).Presentation, T.IsFinite := by
  classical
  let A : ULift.{u} WalkingPair → SheafOfModules.{u} R :=
    pairFunction M N ∘ ULift.down
  let T : ∀ i, (A i).Presentation
    | ⟨.left⟩ => P
    | ⟨.right⟩ => Q
  have : ∀ i, (T i).IsFinite := by
    rintro ⟨_ | _⟩ <;> dsimp [T] <;> infer_instance
  let e : (∐ A) ≅ M ⊞ N :=
    Sigma.reindex Equiv.ulift (pairFunction M N) ≪≫ (biprod.isoCoprod M N).symm
  exact ⟨(SheafOfModules.Presentation.sigma A T).ofIsIso e.hom, inferInstance⟩

/-- The binary biproduct of two finitely presented module sheaves is finitely presented.
Source: Stacks Project, Properties, Lemma 01PJ, proof; Modules, Definition 01BN
(blueprint: lem-weil-pbc-module-finite-presentation-direct-sum).

Proof (the node's agent-written expansion of the assertion in 01PJ):
1. The free module sheaf of rank `n` is the coproduct of `n` copies of the structure
   sheaf: maps out of it correspond uniquely to the images of the basis sections
   (def-weil-pbc-module-finite-type-presentation, def-weil-pbc-category-colimit).
2. At each point choose finite presentations of `G` and `H` on neighbourhoods `U₁`
   and `U₂`, and pass to their intersection `U` (def-weil-pbc-module-finite-type-presentation).
3. Restriction preserves colimits (lem-weil-pbc-ringed-space-colimit-restriction), hence
   finite free coproducts and cokernels. Restrict both presentations to `U`; transport
   the presentation maps along the canonical isomorphisms of the restricted free modules.
4. A biproduct in an additive category is a coproduct, so restriction also identifies
   `(G ⊞ H)|U` with `G|U ⊞ H|U` (def-weil-additive-category,
   def-weil-sheaf-of-modules-category, def-weil-pbc-category-colimit,
   lem-weil-pbc-ringed-space-colimit-restriction).
5. The block diagonal map of the two presentation maps has as its cokernel the
   biproduct of their cokernels: a map killing the block map factors uniquely through
   each cokernel, and then uniquely through their biproduct (def-weil-additive-category).
6. Combine the two finite free domains and the two finite free codomains using the
   coproduct universal property, obtaining ranks `m₁ + m₂` and `n₁ + n₂`.
   Transporting the block map along these isomorphisms preserves its cokernel
   (def-weil-additive-category, def-weil-pbc-module-finite-type-presentation).
7. The resulting finite presentation has cokernel `(G ⊞ H)|U`. Since the point was
   arbitrary, the biproduct is finitely presented (def-weil-sheaf-of-modules-category,
   def-weil-pbc-module-finite-type-presentation).
-/
theorem isFinitePresentation_biprod (X : RingedSpace.{u})
    (G H : SheafOfModules.{u} (moduleRings X))
    [G.IsFinitePresentation] [H.IsFinitePresentation] :
    (G ⊞ H).IsFinitePresentation := by
  classical
  obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData G
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData H
  let U : p.I × q.I → TopologicalSpace.Opens X := fun i ↦ p.X i.1 ⊓ q.X i.2
  have hU : (Opens.grothendieckTopology X).CoversTop U := by
    apply (Opens.coversTop_iff _ _).2
    apply TopologicalSpace.IsOpenCover.mk
    apply top_unique
    intro x hx
    obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).1 p.coversTop).exists_mem x
    obtain ⟨j, hj⟩ := ((Opens.coversTop_iff _ _).1 q.coversTop).exists_mem x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  have hlocal (i : p.I × q.I) : ((G ⊞ H).over (U i)).IsFinitePresentation := by
    let f : U i ⟶ p.X i.1 := homOfLE inf_le_left
    let g : U i ⟶ q.X i.2 := homOfLE inf_le_right
    let F := SheafOfModules.overMap (moduleRings X) f
    let K := SheafOfModules.overMap (moduleRings X) g
    let P := ((p.presentation i.1).map F (SheafOfModules.overMapUnitIso f).symm).ofIsIso
      ((SheafOfModules.overFunctorMap (moduleRings X) f).app G).hom
    let Q := ((q.presentation i.2).map K (SheafOfModules.overMapUnitIso g).symm).ofIsIso
      ((SheafOfModules.overFunctorMap (moduleRings X) g).app H).hom
    have : (p.presentation i.1).IsFinite := hp.isFinite_presentation i.1
    have : (q.presentation i.2).IsFinite := hq.isFinite_presentation i.2
    have : P.IsFinite := by dsimp [P]; infer_instance
    have : Q.IsFinite := by dsimp [Q]; infer_instance
    obtain ⟨T, hT⟩ := finite_biprod_presentation P Q
    have hfp : (G.over (U i) ⊞ H.over (U i)).IsFinitePresentation :=
      T.isFinitePresentation
    let : PreservesBinaryBiproduct G H
        (SheafOfModules.overFunctor (moduleRings X) (U i)) :=
      preservesBinaryBiproduct_of_preservesBinaryCoproduct _
    exact (SheafOfModules.isFinitePresentation ((moduleRings X).over (U i))).prop_of_iso
      (Functor.mapBiprod (SheafOfModules.overFunctor (moduleRings X) (U i)) G H).symm
      hfp
  exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
    (G ⊞ H) (p.I × q.I) U hU hlocal

end AlgebraicGeometry.RingedSpace
