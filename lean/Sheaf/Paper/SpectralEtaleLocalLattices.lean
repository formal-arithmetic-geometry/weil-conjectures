/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousLocallyFreePullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Paper.ContinuousEtaleLocalLattices
import Sheaf.Paper.ContinuousCoefficientModuleEncoding

/-! # Spectral integral coefficient lattices

Source: Bhatt--Scholze, Section 6.8, and blueprint main-20261015.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Local lattice existence with fixed condensed coefficients. -/
private def EtaleCoefficientLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) : Prop :=
  ∃ (U : Scheme.{u}) (f : U ⟶ X), Etale f ∧ Surjective f ∧
    CompactSpace U ∧ QuasiSeparatedSpace U ∧
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U),
      LocallyFree (condensedRingObj A U) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj P)

/-- Transport lattice existence along an equality of coefficient maps. -/
private theorem etaleCoefficientLattice_congr
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a b : A ⟶ B) [IsMonHom a] [IsMonHom b] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (h : a = b) (hP : EtaleCoefficientLattice A B a X P) :
    EtaleCoefficientLattice A B b X P := by
  cases h
  exact hP

/-- Local lattice existence as a predicate of the actual subring. -/
private def EtaleLatticeOverSubring {E : Type} [NontriviallyNormedField E] (A : Subring E)
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) : Prop :=
  EtaleCoefficientLattice (Profinite.continuousMapRingObj A) (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap A.subtype continuous_subtype_val)) X P

/-- Transport the existing local lattice along the equality of valuation subrings. -/
private theorem normedLisse_etale_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : LocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    EtaleLatticeOverSubring (Padic.coefficientExtensionIntegers l E) X P := by
  have h0 : EtaleCoefficientLattice (integralCoeff l E) (Profinite.continuousMapRingObj E)
      (integralScalarMap l E) X P := continuousLisse_etale_lattice l E X P hP
  have h : EtaleLatticeOverSubring (continuousIntegers l E) X P :=
    etaleCoefficientLattice_congr (integralCoeff l E) (Profinite.continuousMapRingObj E)
      (integralScalarMap l E)
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (continuousIntegers l E).subtype continuous_subtype_val)) X P rfl h0
  exact Eq.mp (congrArg (fun A ↦ EtaleLatticeOverSubring A X P)
    (continuousIntegers_eq l E)) h

/-- Topological ring structure transported to an equal field structure. -/
private theorem normedField_topologicalRing (E : Type) (nE : NontriviallyNormedField E)
    (F : Field E) (h : nE.toField = F) :
    letI := nE
    letI : Field E := F
    IsTopologicalRing E := by
  cases h
  let := nE
  infer_instance

/-- The coefficient rings together with their inclusion. -/
private structure CoefficientDiagram where
  integral : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  rational : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  map : integral ⟶ rational

/-- Package actual coefficient rings and their map. -/
private def coefficientDiagramOfMap
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] : CoefficientDiagram.{u} :=
  ⟨CommMon.mk A, CommMon.mk B, CommMon.homMk (Mon.ofHom a)⟩

/-- Local lattice existence depending on a bundled coefficient diagram. -/
private def DiagramLocalLattice (D : CoefficientDiagram.{u}) (X : Scheme.{u}) : Prop :=
  ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj D.rational.X X),
    LocallyFree (condensedRingObj D.rational.X X) P →
    EtaleCoefficientLattice D.integral.X D.rational.X D.map.hom.hom X P

/-- Package a local-lattice proof without changing its coefficients. -/
private theorem diagramLocalLattice_pack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) P → EtaleCoefficientLattice A B a X P) :
    DiagramLocalLattice (coefficientDiagramOfMap A B a) X := h

/-- Unpack local-lattice existence with exactly the given coefficient map. -/
private theorem diagramLocalLattice_unpack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : DiagramLocalLattice (coefficientDiagramOfMap A B a) X) :
    ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) P → EtaleCoefficientLattice A B a X P := h

/-- The coefficient diagram in the given normed structure. -/
private def normedCoefficientDiagram
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : CoefficientDiagram.{u} :=
  coefficientDiagramOfMap
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))

/-- The same diagram with the original field and algebra retained explicitly. -/
private def originalCoefficientDiagram
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E) (hFieldEq : nE.toField = hField) :
    CoefficientDiagram.{u} := by
  let := nE
  let : Field E := hField
  let : Algebra ℚ_[l] E := hAlg
  let : IsTopologicalRing E := normedField_topologicalRing E nE hField hFieldEq
  exact coefficientDiagramOfMap
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))

/-- Finite dimensionality transported to coherent normed algebra data. -/
private theorem normedFiniteDimensional_of_coherent
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [hFin : FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E)
    (nAlg : letI := nE; NormedAlgebra ℚ_[l] E)
    (hFieldEq : nE.toField = hField) (hAlgEq : HEq nAlg.toAlgebra hAlg) :
    letI := nE
    letI : Field E := nE.toField
    letI : Algebra ℚ_[l] E := nAlg.toAlgebra
    FiniteDimensional ℚ_[l] E := by
  cases hFieldEq
  cases eq_of_heq hAlgEq
  exact hFin

/-- Equality of algebraic structures gives equality of the coefficient diagrams. -/
private theorem coefficientDiagram_coherence
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E)
    (nAlg : letI := nE; NormedAlgebra ℚ_[l] E)
    (hFieldEq : nE.toField = hField) (hAlgEq : HEq nAlg.toAlgebra hAlg) :
    @normedCoefficientDiagram.{u} l _ E nE nAlg
      (normedFiniteDimensional_of_coherent l E
        (hField := hField) (hAlg := hAlg) nE nAlg hFieldEq hAlgEq) =
      originalCoefficientDiagram l E nE hFieldEq := by
  cases hFieldEq
  cases eq_of_heq hAlgEq
  rfl

/-- The normed local-lattice result as a property of its coefficient diagram. -/
private theorem normedDiagram_localLattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    DiagramLocalLattice (normedCoefficientDiagram l E) X := by
  apply diagramLocalLattice_pack
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)) X
  intro P hP
  exact normedLisse_etale_lattice l E X P hP

/-- A lisse spectral-coefficient module admits an integral lattice on a qcqs etale cover.
Source: Bhatt--Scholze, Proposition 6.8.4(6) and Lemma 6.8.13, first paragraph;
blueprint main-20261015, sk-lem-stratified-lattice, "Sheaf of lattices".
(blueprint: lem-sfb-spectral-etale-local-lattice).

Proof. Equip E with its spectral norm and its original field and algebra structures.
The spectral norm extends the p-adic norm. The norm-at-most-one subring is the recorded
valuation ring, by the integer-ring characterization in extension_integers_dvr.
Apply continuousLisse_etale_lattice to get a qcqs etale surjection and a locally free
integral module with its scalar-extension comparison. Transport the two coefficient
rings and their inclusion along the preceding equality, preserving the module action,
its free cover, and its rationalization. These are the same continuous-function rings
with their subspace topology. The existing etale-local proof chooses finitely many
pointed affine etale lattice neighbourhoods using Noetherian compactness and takes
their coproduct; its coproduct is affine, hence qcqs. Empty schemes give the empty
coproduct, and zero ranks remain zero. No global descent or stratification is asserted. -/
theorem spectralLisse_etale_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [hFin : FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) L →
      ∃ (U : Scheme.{u}) (f : U ⟶ X), Etale f ∧ Surjective f ∧
        CompactSpace U ∧ QuasiSeparatedSpace U ∧
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U),
          LocallyFree (condensedRingObj A U) M ∧
          Nonempty ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj L) := by
  let nE := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : Field E := hField
  let : Algebra ℚ_[l] E := hAlg
  let nAlg : NormedAlgebra ℚ_[l] E :=
    { spectralNorm.normedAlgebra ℚ_[l] E with toAlgebra := hAlg }
  have h : DiagramLocalLattice (originalCoefficientDiagram l E nE rfl) X :=
    Eq.mp (congrArg (fun D ↦ DiagramLocalLattice D X)
      (coefficientDiagram_coherence l E nE nAlg rfl (HEq.refl _)))
      (normedDiagram_localLattice l E X)
  intro A B a
  exact diagramLocalLattice_unpack A B a X h

end AlgebraicGeometry.ProEtale.CondensedRing
