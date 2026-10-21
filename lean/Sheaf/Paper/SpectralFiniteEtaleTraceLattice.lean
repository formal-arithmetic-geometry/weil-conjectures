/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousLocallyFreePullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.Paper.ContinuousFiniteEtaleTraceLattice
import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import Sheaf.Paper.ContinuousIntegralScalarExact
import Sheaf.Paper.ContinuousIntegralLocalizationCounit
import Sheaf.Paper.ContinuousIntegralUnderivedPushComparison

/-! # Spectral integral coefficient lattices

Source: Bhatt--Scholze, Section 6.8, and blueprint main-20261015.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 2000] HasImages.has_image

/-- Lattice existence for a fixed coefficient inclusion. -/
private def HasCoefficientLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) : Prop :=
  ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X),
    LocallyFree (condensedRingObj A X) N ∧
    ∃ ι : N ⟶ (Mod.comap (coefficientMap a X)).obj P,
      Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
        (coefficientMap a X)).homEquiv N P).symm ι)

/-- Rationalization of the image of a surjective trace is the rational module.
Source: blueprint main-20261015, stratified lattice proof, final paragraph.
(blueprint: lem-sfb-spectral-finite-etale-trace-lattice).
Proof. Exact scalar extension preserves the monic image inclusion. It sends the pushed
lattice map to an isomorphism; the rational counit is invertible. Composing with the
surjective trace makes the scalar extension of the image inclusion epi too, hence iso. -/
private theorem continuousTraceImage_rationalization_isIso
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {U : Scheme.{u}} (p : U ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P) [Epi τ] :
    let g := latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
      (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ
    IsIso (((Mod.extendRestrictAdjunction
      (coefficientMap (integralScalarMap l E) X)).homEquiv (image g) P).symm (image.ι g)) := by
  dsimp only
  let a := coefficientMap (integralScalarMap l E) X
  let F := Mod.extendScalars a
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) a
  let adj := Mod.extendRestrictAdjunction a
  let b := latticePushedEmbedding (integralScalarMap l E) X P p M e
  let g := b ≫ G.map τ
  have := integralScalarCounit_isIso l E X P
  have := integralScalarCounit_isIso l E X
    ((lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P))
  have := integralScalarUnderivedPushHom_isIso l E p M
  have := latticePushedEmbedding_map_isIso (integralScalarMap l E) X P p M e
  have hfac : F.map g ≫ adj.counit.app P = F.map b ≫ adj.counit.app _ ≫ τ := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun z ↦ F.map b ≫ z) (adj.counit.naturality τ)
  have : Epi (F.map g ≫ adj.counit.app P) := by
    rw [hfac]
    infer_instance
  have : Epi (F.map g) :=
    (epi_comp_iff_of_isIso (F.map g) (adj.counit.app P)).mp inferInstance
  have : Epi (F.map (factorThruImage g) ≫ F.map (image.ι g)) := by
    rw [← F.map_comp, image.fac]
    infer_instance
  have : Epi (F.map (image.ι g)) :=
    epi_of_epi (F.map (factorThruImage g)) (F.map (image.ι g))
  have : IsIso (F.map (image.ι g)) := isIso_of_mono_of_epi _
  change IsIso (F.map (image.ι g) ≫ adj.counit.app P)
  infer_instance


/-- Rationalization of the image of a surjective trace is the rational module.
Source: blueprint main-20261015, stratified lattice proof, final paragraph.
(blueprint: lem-sfb-spectral-finite-etale-trace-lattice).
Proof. Exact scalar extension preserves the monic image inclusion. It sends the pushed
lattice map to an isomorphism; the rational counit is invertible. Composing with the
surjective trace makes the scalar extension of the image inclusion epi too, hence iso. -/
private theorem continuousTraceImage_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {U : Scheme.{u}} (p : U ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P) [Epi τ]
    (hI : LocallyFree (condensedRingObj (integralCoeff l E) X)
      (image (latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
        (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ))) :
    HasCoefficientLattice (integralCoeff l E) (Profinite.continuousMapRingObj E)
      (integralScalarMap l E) X P := by
  change ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff l E) X),
      LocallyFree (condensedRingObj (integralCoeff l E) X) N ∧
      ∃ ι : N ⟶ (Mod.comap (coefficientMap (integralScalarMap l E) X)).obj P,
        Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
          (coefficientMap (integralScalarMap l E) X)).homEquiv N P).symm ι)
  let g := latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
    (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ
  exact ⟨image g, hI, image.ι g, inferInstance,
    continuousTraceImage_rationalization_isIso l E X P p M e τ⟩

/-- Finite-cover lattice descent for a fixed coefficient map. -/
private def FiniteEtaleCoefficientLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u}) : Prop :=
  ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
    LocallyFree (condensedRingObj B X) P →
    ∀ {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
      (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U)),
      LocallyFree (condensedRingObj A U) M →
      ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B p).obj P) →
      HasCoefficientLattice A B a X P

/-- Transport finite-cover descent along an equality of coefficient maps. -/
private theorem finiteEtaleCoefficientLattice_congr
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a b : A ⟶ B) [IsMonHom a] [IsMonHom b] (X : Scheme.{u})
    (h : a = b) (hP : FiniteEtaleCoefficientLattice A B a X) :
    FiniteEtaleCoefficientLattice A B b X := by
  cases h
  exact hP

/-- Finite-cover lattice descent, as a predicate of the coefficient subring. -/
private def FiniteEtaleLatticeOverSubring {E : Type} [NontriviallyNormedField E]
    (A : Subring E) (X : Scheme.{u}) : Prop :=
  FiniteEtaleCoefficientLattice (Profinite.continuousMapRingObj A)
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap A.subtype continuous_subtype_val)) X

/-- Rationalize the locally free trace image and change the integral subring. -/
private theorem normedFiniteEtaleTrace_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    FiniteEtaleLatticeOverSubring (Padic.coefficientExtensionIntegers l E) X := by
  have h0 : FiniteEtaleCoefficientLattice (integralCoeff l E)
      (Profinite.continuousMapRingObj E) (integralScalarMap l E) X := by
    intro P hP U p _ _ _ M hM e
    obtain ⟨τ, hτ, hI⟩ := continuousFiniteEtaleTrace_lattice l E X P hP p M hM e
    have := hτ
    exact continuousTraceImage_lattice l E X P p M e τ hI
  have h : FiniteEtaleLatticeOverSubring (continuousIntegers l E) X :=
    finiteEtaleCoefficientLattice_congr (integralCoeff l E) (Profinite.continuousMapRingObj E)
      (integralScalarMap l E)
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (continuousIntegers l E).subtype continuous_subtype_val)) X rfl h0
  exact Eq.mp (congrArg (fun A ↦ FiniteEtaleLatticeOverSubring A X)
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

/-- Finite-cover lattice descent depending on a bundled coefficient diagram. -/
private def DiagramFiniteLattice (D : CoefficientDiagram.{u}) (X : Scheme.{u}) : Prop :=
  FiniteEtaleCoefficientLattice D.integral.X D.rational.X D.map.hom.hom X

/-- Package a finite-cover descent proof with its actual coefficients. -/
private theorem diagramFiniteLattice_pack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : FiniteEtaleCoefficientLattice A B a X) :
    DiagramFiniteLattice (coefficientDiagramOfMap A B a) X := h

/-- Unpack finite-cover descent with exactly the given coefficient map. -/
private theorem diagramFiniteLattice_unpack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : DiagramFiniteLattice (coefficientDiagramOfMap A B a) X) :
    FiniteEtaleCoefficientLattice A B a X := h

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

/-- The trace-image rationalization proof as a property of its coefficient diagram. -/
private theorem normedDiagram_finiteLattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    DiagramFiniteLattice (normedCoefficientDiagram l E) X := by
  apply diagramFiniteLattice_pack
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)) X
  exact normedFiniteEtaleTrace_lattice l E X

/-- Finite etale trace descent gives an integral lattice over spectral coefficients.
Source: blueprint main-20261015, sk-lem-stratified-lattice, "Pushing down by the trace";
Bhatt--Scholze, Section 6.8.
(blueprint: lem-sfb-spectral-finite-etale-trace-lattice).

Proof. Split the finite etale surjection etale locally. Sum the sheet counits to define
p_*p*P → P; invariance under permutations glues these maps. On a nonempty chart there
is a sheet, and insertion into that sheet makes the trace epic. Take the categorical
image of p_*M → Res(P) induced by e and trace. Trivialize P pro-etale locally.
Local constancy of the lattice-class sheaf makes the finitely many sheet lattices
constant on a common refinement. Their sum is a finite free lattice over the valuation
ring. A lifted basis supplies a continuous linear section of the sheet sum, so the
image on continuous functions is the continuous-function sheaf of that sum lattice.
Thus the image is locally free. Its image inclusion is monic. Integral localization
is exact; the pushed lattice comparison rationalizes to an isomorphism and trace is
epic, so the rationalized image inclusion is epic and monic, hence invertible.
The scalar-extension adjunction identifies that map with the adjoint of the actual
image inclusion. Transport along continuousIntegers_eq identifies the norm ball
with the spectral valuation ring; the topology is the subspace topology throughout.
No degree is divided out. Empty bases and zero ranks yield zero modules. -/
theorem spectralFiniteEtaleTrace_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [hFin : FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)),
      LocallyFree (condensedRingObj B X) P →
      ∀ {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
        (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U)),
      LocallyFree (condensedRingObj A U) M →
      ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B p).obj P) →
      ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X),
        LocallyFree (condensedRingObj A X) N ∧
        ∃ ι : N ⟶ (Mod.comap (coefficientMap a X)).obj P,
          Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
            (coefficientMap a X)).homEquiv N P).symm ι) := by
  let nE := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : Field E := hField
  let : Algebra ℚ_[l] E := hAlg
  let nAlg : NormedAlgebra ℚ_[l] E :=
    { spectralNorm.normedAlgebra ℚ_[l] E with toAlgebra := hAlg }
  have h : DiagramFiniteLattice (originalCoefficientDiagram l E nE rfl) X :=
    Eq.mp (congrArg (fun D ↦ DiagramFiniteLattice D X)
      (coefficientDiagram_coherence l E nE nAlg rfl (HEq.refl _)))
      (normedDiagram_finiteLattice l E X)
  intro A B a
  exact diagramFiniteLattice_unpack A B a X h

end AlgebraicGeometry.ProEtale.CondensedRing
