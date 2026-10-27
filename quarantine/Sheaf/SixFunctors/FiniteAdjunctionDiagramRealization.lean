/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.SixFunctors.FiniteAdjunctionSystemData
public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.SixFunctors.FiniteAdjunctionDiagramData
import Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus
import Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization
import Sheaf.SixFunctors.FiniteAdjunctionSystemDuality
import Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched

/-! Finite exceptional operations and enriched adjunction on coherent systems. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
variable {l E D hl f c}

variable (l E D hl f c)

/-- Functorial realization of finite exceptional operations, duality and enriched
adjunction on normalized derived coefficient systems, with no common level bound.
All displayed structures are conclusions; none is an additional hypothesis.

Source: current blueprint main-20261015, finite exceptional lemma and the first two
paragraphs of prop-coef-integral-exceptional-adjoint; Stacks 06YS, 0A95, 0941, 079P
(blueprint: lem-coef-finite-adjunction-diagram-realization).

Proof: work first with strict systems on the etale sequence site. Simultaneous
K-flat and K-injective resolutions give the ordinary unbounded derived system
category and exact evaluations. Exact open extension and proper total direct
image define compact support on systems. The open-unit tensor transpose is the
identity comparison on the open slice and is invertible; on the complementary
slice both terms vanish. The two quotient restrictions have the same canonical
quotient ring map on constant sections, hence agree after sheafification and
exact localization. These give the Support and QuotientRestriction proof fields.
Proper coproduct preservation at each
finite coefficient and componentwise coproducts make this functor coproduct
preserving. Grothendieck-derived Brown representability gives its actual right
adjoint. The derived evaluation left adjoints and the proper/open projection
comparison identify its evaluated adjoints, units, counits and quotient mates.
Transfer through the unbounded etale/pro-etale system comparison, using etale
origin separately at each constructible level. Restrict both functors to the full
normalized finite-Tor subcategories. Finite preservation gives the level conditions;
invertibility of the finite mate b gives normalization, without a common bound.
Reduction, compact support and total limit identify the already defined integral
compact-support FUNCTOR; the scalar-adjunction units give exactly its projections.
Apply the same system construction to the structure maps and coefficient unit.
The finite dualizing comparison identifies the resulting tower and its transitions;
the normalized tower's Roos presentation identifies its limit with the prescribed
dualizing construction, retaining the actual projections. Finite duality and
quotient tensor-Hom compatibility show that system internal dual preserves the
normalized finite-Tor domain. Form the relative trace by the absolute structural
counit and compact-support composition. On simultaneous system resolutions the
proper projection, open tensor, signed symmetry and evaluation give the displayed
pairing. Tensor-Hom transposition defines the dual-formula map; finite duality and
joint conservativity make it an isomorphism. The pairing is an equality of system
maps, so also preserves normalization and the finite evaluation pairings. Finally
form enrichedMap by projection, geometric counit, evaluation and exceptional
counit, BEFORE evaluating. Its finite values are the etale enriched-adjunction
transposes transported by canonical site comparison. Conservativity makes this
map invertible. Derived global sections of its inverse and the ordinary
section/direct-image comparison give globalMap, hence the natural isomorphism
iso. Universal derived units prove its representative normalization and the finite
evaluation square. The finite Hom identification is precisely the already fixed
finite adjunction. All inverses and triangle and transpose identities hold in the
ordinary derived system categories before taking any total inverse limit. -/
theorem finiteAdjunctionDiagramRealization :
    ∃ (SX : CoefficientDerivedSystemCalculus l E X)
      (SZ : CoefficientDerivedSystemCalculus l E c.Z)
      (SY : CoefficientDerivedSystemCalculus l E Y)
      (SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))),
      Nonempty (CoefficientDerivedSystemCoherence l E X SX) ∧
      Nonempty (CoefficientDerivedSystemCoherence l E c.Z SZ) ∧
      Nonempty (CoefficientDerivedSystemCoherence l E Y SY) ∧
      Nonempty (CoefficientDerivedSystemCoherence l E (Spec (.of D.k)) SS) ∧
      ∃ (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
        (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
        (r : Realization l E D hl f c SX SZ SY)
        (g : Geometry l E f SX SY) (s : SectionsPush g)
        (aX : DualizingOperation (D := D) (hl := hl) X SX SS)
        (aY : DualizingOperation (D := D) (hl := hl) Y SY SS),
        Nonempty (RingedDerivedTensorCoherence.{u+1, u, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X) SX.systemClosed SX.systemTensorModel βX) ∧
        Nonempty (RingedDerivedTensorCoherence.{u+1, u, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) SY.systemClosed SY.systemTensorModel βY) ∧
        Nonempty (Enriched r g s βX βY) ∧ Nonempty (Duality r aX aY βY g) ∧
        Nonempty (IntegralSupport r) := by
  classical
  obtain ⟨SX, ⟨hX⟩, βX, ⟨tX⟩⟩ := coefficientSystemSymmetricCalculus (l := l) (E := E) X
  obtain ⟨SZ, ⟨hZ⟩, βZ, ⟨tZ⟩⟩ := coefficientSystemSymmetricCalculus (l := l) (E := E) c.Z
  obtain ⟨SY, ⟨hY⟩, βY, ⟨tY⟩⟩ := coefficientSystemSymmetricCalculus (l := l) (E := E) Y
  obtain ⟨SS, ⟨hS⟩, βS, ⟨tS⟩⟩ :=
    coefficientSystemSymmetricCalculus (l := l) (E := E) (Spec (.of D.k))
  obtain ⟨r, g, s, aX, aY, hI⟩ :=
    finiteAdjunctionGeometricRealization l E D hl f c SX SZ SY SS
      hX hZ hY hS βX βY tX tY
  have hD := finiteAdjunctionSystemDuality l E D hl f c SX SZ SY SS
    hX hZ hY hS βX βY tX tY r g aX aY
  have hA := finiteAdjunctionSystemEnriched l E D hl f c SX SZ SY SS
    hX hZ hY hS βX βY tX tY r g s
  exact ⟨SX, SZ, SY, SS, ⟨hX⟩, ⟨hZ⟩, ⟨hY⟩, ⟨hS⟩,
    βX, βY, r, g, s, aX, aY, ⟨tX⟩, ⟨tY⟩, hA, hD, hI⟩


end WeilConjectures.FiniteAdjunctionDiagram
