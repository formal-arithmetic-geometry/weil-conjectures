/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerGeometricFiniteWords
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerGeometricOpenWords

/-! # Coherent geometric compactification operations on coefficient towers

The open comparison is supplied separately from the étale sum adjunction, so that
normalizing the latter is an actual isomorphism composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Comparisons from arbitrary compactifications of an open immersion to its
recorded exact open extension. This is a family of natural isomorphisms, with no
chosen existential witness or derived morphism reconstructed from evaluations.
Source: Stacks 0F7J, open normalization of compact support
(blueprint: def-sp-open-compactification-comparisons). -/
abbrev OpenCompactificationComparisons
    (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b) :=
    ∀ {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (a : Compactification j),
    inclusion l E b q U ⋙ F l E b o q a ≅
      inclusion l E b q U ⋙ openExtension l E b o q j

/-- Restrict native open comparisons along the inclusion, before specializing
any concrete derived comparison. The standard whiskering component formula and
ObjectProperty.ι_obj identify the two boundary equations. -/
private theorem coherent_of_native_operations
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (finiteData : FiniteNormalization l E k b o q z)
    (opsData : CompositionOperations l E k b o q z)
    (nativeOpen : ∀ {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (a : Compactification j), F l E b o q a ≅ openExtension l E b o q j)
    (hcoherence : ∀ h : Preservation l E k b o q,
      CompositionCoherence l E k b o q z h finiteData opsData)
    (hopen :
      ∀ {U X Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a : Compactification j) (c : Compactification f) (K : C l E b q U),
    (opsData.composition j f (j ≫ f) rfl a c (c.precomp j)).hom.app K =
      (F l E b o q c).map
        ((nativeOpen j a).hom.app K.obj) ≫
        (openComposition l E b o q j c).hom.app K.obj) :
    ∃ ops : CompositionOperations l E k b o q z,
    ∃ v : OpenCompactificationComparisons l E k b o q,
    ∀ h : Preservation l E k b o q,
      Nonempty (CompositionCoherence l E k b o q z h finiteData ops) ∧
      ∀ {U X Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a : Compactification j) (c : Compactification f) (K : C l E b q U),
    (ops.composition j f (j ≫ f) rfl a c (c.precomp j)).hom.app K =
      (F l E b o q c).map
        ((v j a).hom.app K) ≫
        (openComposition l E b o q j c).hom.app K.obj := by
  let v : OpenCompactificationComparisons l E k b o q := by
    intro U X _ _ _ _ _ _ _ _ j _ _ _ a
    exact Functor.isoWhiskerLeft (inclusion l E b q U) (nativeOpen j a)
  refine ⟨opsData, v, ?_⟩
  intro h
  refine ⟨⟨hcoherence h⟩, ?_⟩
  intro U X Y _ _ _ _ _ _ _ _ _ _ _ _ j _ _ _ f _ _ _ _ a c K
  simpa only [v, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ObjectProperty.ι_obj] using (hopen j f a c K)

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
