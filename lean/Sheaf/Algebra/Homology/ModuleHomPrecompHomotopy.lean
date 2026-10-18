/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Single

/-! # Precomposition and homotopies on module-valued total Hom complexes

Source: blueprint main-20261015, sec-trace-formula/sk-p-trace, final two sentences
of sk-p-trace.proof.md; Stacks Project, Tag 0A8H, total Hom differential.
(blueprint: lem-trf-hom-dual-preserves-homotopies).

The precomposition components have actual linear-map data. The homotopy statement
specifies every degree-minus-one component by the signed precomposition formula.

## Main definitions

* `moduleHomPrecompComponent`: the linear map φ ↦ φf in each degree.
* `moduleHomPrecomp`: the corresponding chain map on the recorded total Hom complexes.

## Main statements

* `moduleHomPrecomp_id_comp`: identity and contravariant composition.
* `moduleHomPrecomp_preserves_homotopies`: the homotopy with S_h(φ) = (-1)^j φh.
* `moduleHomDual_preserves_homotopies`: specialization to the ring in degree zero.
* `moduleHomDual_preserves_homotopy_inverses`: the specified dual maps are homotopy inverses.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

variable {A : Type u} [CommRing A]
variable {P R L : CochainComplex (ModuleCat.{u} A) ℤ}

/-- Precomposition on homogeneous cochains, retaining the A-linear structure.
Source: blueprint sk-p-trace.proof.md, final two sentences; Stacks, Tag 0A8H.
(blueprint: lem-trf-hom-dual-preserves-homotopies). -/
noncomputable def moduleHomPrecompComponent
    (T : CochainComplex (ModuleCat.{u} A) ℤ) (f : P ⟶ R) (j : ℤ) :
    (moduleHomComplex R T).X j ⟶ (moduleHomComplex P T).X j :=
  ModuleCat.ofHom
    { toFun := fun φ ↦ (HomComplex.Cochain.ofHom f).comp φ (zero_add j)
      map_add' := fun φ ψ ↦ HomComplex.Cochain.comp_add _ φ ψ _
      map_smul' := fun a φ ↦ HomComplex.Cochain.comp_smul _ a φ _ }

/-- Precomposition commutes with the total Hom differential.
Source: blueprint sk-p-trace.proof.md, final two sentences; Stacks, Tag 0A8H.
(blueprint: lem-trf-hom-dual-preserves-homotopies).
Proof: expand D(φf) = d_T φf - (-1)^j φf d_P. Since f is a chain map,
f d_P = d_R f, this is (d_T φ - (-1)^j φ d_R)f = (Dφ)f.
This is also Mathlib's δ_ofHom_comp applied to the existing linear cochains. -/
theorem moduleHomPrecomp_comm
    (T : CochainComplex (ModuleCat.{u} A) ℤ) (f : P ⟶ R) (j k : ℤ) :
    moduleHomPrecompComponent T f j ≫ (moduleHomComplex P T).d j k =
      (moduleHomComplex R T).d j k ≫ moduleHomPrecompComponent T f k := by
  sorry

/-- The chain map on total Hom complexes given by precomposition with f.
Source: blueprint sk-p-trace.proof.md, final two sentences; Stacks, Tag 0A8H.
(blueprint: lem-trf-hom-dual-preserves-homotopies). -/
noncomputable def moduleHomPrecomp
    (T : CochainComplex (ModuleCat.{u} A) ℤ) (f : P ⟶ R) :
    moduleHomComplex R T ⟶ moduleHomComplex P T where
  f j := moduleHomPrecompComponent T f j
  comm' j k _ := moduleHomPrecomp_comm T f j k

/-- Precomposition preserves identities and reverses composition.
Source: blueprint sk-p-trace.proof.md, final two sentences.
(blueprint: lem-trf-hom-dual-preserves-homotopies).
Proof: on each homogeneous cochain, φ 1 = φ and (φ g)f = φ(gf).
Use identity and associativity of component maps, then extensionality. -/
theorem moduleHomPrecomp_id_comp
    (T : CochainComplex (ModuleCat.{u} A) ℤ) :
    (∀ Q : CochainComplex (ModuleCat.{u} A) ℤ,
      moduleHomPrecomp T (𝟙 Q) = 𝟙 (moduleHomComplex Q T)) ∧
    (∀ (f : P ⟶ R) (g : R ⟶ L),
      moduleHomPrecomp T (f ≫ g) = moduleHomPrecomp T g ≫ moduleHomPrecomp T f) := by
  sorry

/-- The signed precomposition homotopy, with all its degree-minus-one components specified.
Source: blueprint sk-p-trace.proof.md, final two sentences; Stacks, Tag 0A8H.
(blueprint: lem-trf-hom-dual-preserves-homotopies).
Proof: (1) the chain-map calculation D(φf) = (Dφ)f defines precomposition above.
Use the recorded total Hom differential (def-sc-module-total-hom-complex) and ordinary
cochain complexes and chain maps (def-weil-abstract-derived-category).
(2) Identity and composition are pointwise identity and associativity.
(3) Set S_h(φ) = (-1)^j φh in degree j. Expanding DS_h + S_hD gives
(-1)^j d_T φh + φh d_P + (-1)^(j+1) d_T φh + φd_R h.
The d_T terms cancel; the remainder is φ(hd_P + d_R h) = φ(f-f').
Thus the homotopy identity is f* - f'* = DS_h + S_hD.
(4) Specialize to T = A[0] for dualization.
(5) Applying this to gf homotopic to 1 and fg homotopic to 1, and using (2),
shows that the specified dual maps of homotopy inverses are homotopy inverses. -/
theorem moduleHomPrecomp_preserves_homotopies
    (T : CochainComplex (ModuleCat.{u} A) ℤ) {f f' : P ⟶ R} (h : Homotopy f f') :
    ∃ H : Homotopy (moduleHomPrecomp T f) (moduleHomPrecomp T f'),
      ∀ (j : ℤ) (φ : HomComplex.Cochain R T j),
        H.hom j (j - 1) φ =
          j.negOnePow • (HomComplex.Cochain.ofHomotopy h).comp φ (by omega) := by
  sorry

/-- Dualization into A in degree zero sends homotopic maps to homotopic maps.
Source: blueprint sk-p-trace.proof.md, final two sentences.
(blueprint: lem-trf-hom-dual-preserves-homotopies).
Proof: apply the signed precomposition homotopy with the fixed target A[0].
No boundedness, projectivity or condition on the characteristic is needed. -/
theorem moduleHomDual_preserves_homotopies {f f' : P ⟶ R} (h : Homotopy f f') :
    Nonempty (Homotopy
      (moduleHomPrecomp
        ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)) f)
      (moduleHomPrecomp
        ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)) f')) := by
  sorry

/-- The specified dual maps of homotopy inverses are homotopy inverses.
Source: blueprint sk-p-trace.proof.md, final two sentences.
(blueprint: lem-trf-hom-dual-preserves-homotopies).
Proof: dualize the homotopies gf ≃ 1_P and fg ≃ 1_R. Contravariant
composition identifies the resulting composites with the two composites of the dual maps,
and precomposition with an identity is an identity. -/
theorem moduleHomDual_preserves_homotopy_inverses (f : P ⟶ R) (g : R ⟶ P)
    (hP : Homotopy (f ≫ g) (𝟙 P)) (hR : Homotopy (g ≫ f) (𝟙 R)) :
    ∃ e : HomotopyEquiv
        (moduleHomComplex R
          ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)))
        (moduleHomComplex P
          ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A))),
      e.hom = moduleHomPrecomp
        ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)) f ∧
      e.inv = moduleHomPrecomp
        ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)) g := by
  sorry

end CochainComplex
