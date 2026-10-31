/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.CoefficientTowerGeometricFiniteWords
import WeilConjectures.AlgebraicGeometry.CoefficientTowerGeometricOpenWords

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

/-- The geometric part of the coefficient-tower calculus, including compatibility
with the canonical open compositor, before choosing an étale sum adjunction.
Source: Stacks 0F7J/0F7K, common-tower construction; blueprint Local pairs and Levels.

Proof: use the section-pinned graph coordinates to realize the supplied functors
in the actual varying-ring calculus. The finite-ring open-support theorem makes
its gamma invertible on the full unbounded categories. Noetherian compactification
geometry, common refinements and staircases then construct coherent native words.
Restrict those already constructed words to C, before choosing any preservation
witness. The finite-word normalization theorem identifies their two finite
boundaries; the geometric assembly proves every other coherence field, including
ambient triangulatedness. Construct the open comparison by comparison with the
trivial open compactification and its proper unitor. The open-word normalization
theorem gives its canonical ordinary open-composition boundary. Thus the two
remaining normalization steps concern maps of explicit constructions, and the
existential witnesses do not depend on either of those steps or on preservation.
(blueprint: lem-route-geometric-calculus-coherent-operations). -/
theorem geometric_coherent_operations
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (finiteData : FiniteNormalization l E k b o q z) :
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
  obtain ⟨g⟩ := GeometricCoordinates.nonempty_graphCoordinates l E b o
  refine coherent_of_native_operations l E k b o q z finiteData
    (GeometricCoordinates.operations l E k b o q z g) (by
      intro U X _ _ _ _ _ _ _ _ j _ _ _ a
      exact GeometricCoordinates.openComparison l E b o q g
        (GeometricCoordinates.ambient_field k U) (GeometricCoordinates.ambient_field k X) j a)
    ?_ ?_
  · intro h
    exact GeometricCoordinates.operations_coherence l E k b o q z g finiteData
      (GeometricCoordinates.finite_words l E pchar hp hne k b o x laws q z g finiteData) h
  · exact GeometricCoordinates.open_words l E pchar hp hne k b o x laws q z g

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
