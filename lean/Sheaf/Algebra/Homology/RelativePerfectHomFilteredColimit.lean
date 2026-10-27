module

public import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalSystem
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation

import WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.Grp.AB

/-! # Derived Hom continuity for relatively perfect coefficients

Source: Stacks Project, More on Algebra, Tag 0DHX (2), with the model of Tag 0E1U.
(blueprint: lem-sfb-relative-perfect-hom-filtered-colimit).

The auxiliary constructions give the actual scalar-extension maps. The theorem packages
these maps into a diagram using objectwise identifications and asserts that its canonical
colimit comparison is an isomorphism. These identifications allow the functor laws to be
asserted inside the theorem, without postponing proofs inside a definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The base algebra associated to a ring under R.
Source: Stacks 0DHX (blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
abbrev relativePerfectBaseAlgebra {R : Type u} [CommRing R]
    (T : Under (CommRingCat.of R)) : CommAlgCat.{u} R :=
  (commAlgCatEquivUnder (CommRingCat.of R)).inverse.obj T

/-- Derived base change from A to A tensor_R T, using the recorded K-flat construction.
Source: Stacks 0DHX (blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
def relativePerfectExtension {R : Type u} [CommRing R] (A : CommAlgCat.{u} R)
    (T : Under (CommRingCat.of R)) :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (A ⊗[R] relativePerfectBaseAlgebra T)) :=
  relativeDualizingDerivedExtension
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] relativePerfectBaseAlgebra T).toRingHom

/-- The actual homomorphism of tensor algebras induced by a map of base rings under R.
Source: Stacks 0DHX (blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
def relativePerfectTensorMap {R : Type u} [CommRing R] (A : CommAlgCat.{u} R)
    {T U : Under (CommRingCat.of R)} (f : T ⟶ U) :
    (A ⊗[R] relativePerfectBaseAlgebra T) →+*
      (A ⊗[R] relativePerfectBaseAlgebra U) :=
  (Algebra.TensorProduct.map (AlgHom.id R A)
    ((commAlgCatEquivUnder (CommRingCat.of R)).inverse.map f).hom).toRingHom

/-- The canonical iterated derived-base-change identification, normalized by the
scalar-extension/restriction adjunction, rather than an unspecified isomorphism.
Source: Stacks 08DW and 0DHX
(blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
def relativePerfectExtensionComp {R : Type u} [CommRing R] (A : CommAlgCat.{u} R)
    {T U : Under (CommRingCat.of R)} (f : T ⟶ U) :
    relativePerfectExtension A T ⋙
        relativeDualizingDerivedExtension (relativePerfectTensorMap A f) ≅
      relativePerfectExtension A U :=
  koszulDiagonalExtensionComp _ _ _ (by ext x; simp [relativePerfectTensorMap])

/-- The abelian group of morphisms between the two derived base changes.
Source: Stacks 0DHX (2)
(blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
def relativePerfectHomGroup {R : Type u} [CommRing R] (A : CommAlgCat.{u} R)
    (K L : DerivedCategory (ModuleCat.{u} A)) (T : Under (CommRingCat.of R)) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of ((relativePerfectExtension A T).obj K ⟶
    (relativePerfectExtension A T).obj L)

/-- Extend a derived morphism and transport along the canonical iterated-tensor
identifications of its source and target. This defines both transitions and colimit legs.
Source: Stacks 0DHX (2), 08DW
(blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
def relativePerfectHomMap {R : Type u} [CommRing R] (A : CommAlgCat.{u} R)
    (K L : DerivedCategory (ModuleCat.{u} A))
    {T U : Under (CommRingCat.of R)} (f : T ⟶ U) :
    relativePerfectHomGroup A K L T →+ relativePerfectHomGroup A K L U :=
  letI := (koszulDiagonalExtensionAdjunction (relativePerfectTensorMap A f)).left_adjoint_additive
  (Preadditive.rightComp _ ((relativePerfectExtensionComp A f).hom.app L)).comp
    ((Preadditive.leftComp _ ((relativePerfectExtensionComp A f).inv.app K)).comp
      (relativeDualizingDerivedExtension (relativePerfectTensorMap A f)).mapAddHom)

/-- A ring in the tail i ≥ i₀, with its specified structure map from R_i₀.
Source: Stacks 0DHX (blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
abbrev relativePerfectRingAt {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u})
    (i₀ : I) (i : Set.Ici i₀) : Under (F.obj i₀) :=
  Under.mk (F.map (homOfLE i.property))

/-- A transition in the tail, retaining the specified base-ring map.
Source: Stacks 0DHX (blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
def relativePerfectRingTransition {I : Type u} [Preorder I]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I) {i j : Set.Ici i₀} (h : i ≤ j) :
    relativePerfectRingAt F i₀ i ⟶ relativePerfectRingAt F i₀ j :=
  Under.homMk (F.map (homOfLE h)) (by
    simpa [relativePerfectRingAt] using (F.map_comp (homOfLE i.property) (homOfLE h)).symm)

/-- The colimit ring with its structure map from the chosen initial stage.
Source: Stacks 0DHX (blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
abbrev relativePerfectRingLimit {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u})
    (i₀ : I) : Under (F.obj i₀) :=
  Under.mk (colimit.ι F i₀)

/-- The specified colimit leg in rings under R_i₀.
Source: Stacks 0DHX (blueprint: lem-sfb-relative-perfect-hom-filtered-colimit). -/
def relativePerfectRingToLimit {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u})
    (i₀ : I) (i : Set.Ici i₀) :
    relativePerfectRingAt F i₀ i ⟶ relativePerfectRingLimit F i₀ :=
  Under.homMk (colimit.ι F i.val) (by
    exact colimit.w F (homOfLE i.property))

/-- Derived Hom continuity under directed colimits of base rings. The objectwise
isomorphisms e identify H with exactly the stated Hom groups; the transition equation
identifies its maps with derived scalar extension. The final equation characterizes the
isomorphism out of colimit H on every colimit leg, hence fixes the canonical comparison.
No transition-flatness, Noetherianity, or perfectness hypothesis is imposed.

Source: Stacks Project, More on Algebra, Tag 0DHX (2)
(blueprint: lem-sfb-relative-perfect-hom-filtered-colimit).
Proof:
1. By lem-sfb-relative-rhom-flat-base-change-model (Stacks 0E1U), choose a bounded-above
finite-free model P of K and a bounded R_i₀-flat model Q of L. Their total Hom E computes
derived Hom after every base change, including nonflat ones, naturally in the base ring.
2. The tail i ≥ i₀ is nonempty and directed and has the same ring colimit. By
lem-weil-pbc-filtered-colimit-algebras-underlying-module, this colimit is also the
colimit of the underlying R_i₀-modules.
3. Apply lem-pc-module-filtered-colimits-tensor on the one-object site to identify
the termwise colimit of E tensor R_i with E tensor R. The comparison sends x tensor r_i
to x tensor its image in R and commutes with differentials. The forgetful-colimit
comparison lem-weil-pbc-module-sheaves-colimits-forgetful identifies the underlying
abelian-group colimit.
4. Exact filtered colimits of abelian groups commute with kernels, images, and their
quotients, so H⁰ of this termwise colimit is the colimit of H⁰(E tensor R_i).
5. The natural model comparisons from step 1 identify all transition maps and all legs
with relativePerfectHomMap. The resulting isomorphism therefore has the displayed
normalization, which uniquely characterizes the canonical colimit comparison. -/
theorem relativePerfectHom_filtered_colimit
    {I : Type u} [PartialOrder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I) (A : CommAlgCat.{u} (F.obj i₀))
    [Module.Flat (F.obj i₀) A] [Algebra.FinitePresentation (F.obj i₀) A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (hK : DerivedCategory.IsPseudoCoherent K)
    (hL : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u} (F.obj i₀))
      a b ((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A)).mapDerivedCategory.obj L)) :
    ∃ (H : Set.Ici i₀ ⥤ AddCommGrpCat.{u})
      (e : ∀ i : Set.Ici i₀, H.obj i ≅
        relativePerfectHomGroup A K L (relativePerfectRingAt F i₀ i)),
      (∀ (i j : Set.Ici i₀) (f : i ⟶ j) (m : H.obj i),
        (e j).hom (H.map f m) =
          relativePerfectHomMap A K L (relativePerfectRingTransition F i₀ (leOfHom f))
            ((e i).hom m)) ∧
      ∃ c : colimit H ≅ relativePerfectHomGroup A K L (relativePerfectRingLimit F i₀),
        ∀ (i : Set.Ici i₀) (m : H.obj i),
          c.hom (colimit.ι H i m) =
            relativePerfectHomMap A K L (relativePerfectRingToLimit F i₀ i) ((e i).hom m) := by
  sorry

end AlgebraicGeometry
