/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
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
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact HomComplex.δ_ofHom_comp f φ k

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
  constructor
  · intro Q
    ext j φ : 3
    exact HomComplex.Cochain.id_comp φ
  · intro f g
    ext j φ : 3
    change (HomComplex.Cochain.ofHom (f ≫ g)).comp φ (zero_add j) = _
    rw [HomComplex.Cochain.ofHom_comp]
    exact HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
      (HomComplex.Cochain.ofHom f) (HomComplex.Cochain.ofHom g) φ (zero_add j)

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
  let s : HomComplex.Cochain (moduleHomComplex R T) (moduleHomComplex P T) (-1) :=
    HomComplex.Cochain.mk fun j k hjk ↦ ModuleCat.ofHom
      { toFun := fun φ ↦ j.negOnePow • (HomComplex.Cochain.ofHomotopy h).comp φ (by omega)
        map_add' := fun φ ψ ↦ by simp [smul_add]
        map_smul' := fun a φ ↦ by simp [smul_comm a j.negOnePow] }
  have hs : HomComplex.Cochain.ofHom (moduleHomPrecomp T f) =
      HomComplex.δ (-1) 0 s + HomComplex.Cochain.ofHom (moduleHomPrecomp T f') := by
    apply HomComplex.Cochain.ext₀
    intro j
    simp only [HomComplex.Cochain.add_v]
    rw [HomComplex.δ_v (-1) 0 (by omega) s j j (by omega) (j - 1) (j + 1)
      (by omega) (by omega)]
    simp only [HomComplex.Cochain.ofHom_v]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    dsimp [s, moduleHomPrecomp, moduleHomPrecompComponent, moduleHomComplex,
      HomComplex.δ_hom]
    simp only [one_smul]
    change (HomComplex.Cochain.ofHom f).comp φ (zero_add j) =
      HomComplex.δ (j - 1) j
        (j.negOnePow • (HomComplex.Cochain.ofHomotopy h).comp φ (by omega)) +
        (j + 1).negOnePow • (HomComplex.Cochain.ofHomotopy h).comp
          (HomComplex.δ j (j + 1) φ) (by omega) +
        (HomComplex.Cochain.ofHom f').comp φ (zero_add j)
    rw [HomComplex.δ_units_smul,
      HomComplex.δ_comp (HomComplex.Cochain.ofHomotopy h) φ (by omega)
        0 (j + 1) j (by omega) (by omega) rfl,
      HomComplex.δ_ofHomotopy]
    simp only [smul_add, smul_smul, Int.units_mul_self, one_smul,
      Int.negOnePow_succ, Units.neg_smul, HomComplex.Cochain.sub_comp]
    abel
  refine ⟨(HomComplex.Cochain.equivHomotopy _ _).symm ⟨s, hs⟩, ?_⟩
  intro j φ
  dsimp [HomComplex.Cochain.equivHomotopy]
  rw [dif_pos (show j + -1 = j - 1 by omega)]
  rfl

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
  obtain ⟨H, _⟩ := moduleHomPrecomp_preserves_homotopies
    ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)) h
  exact ⟨H⟩

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
  let T := (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)
  obtain ⟨HP, _⟩ := moduleHomPrecomp_preserves_homotopies T hP
  obtain ⟨HR, _⟩ := moduleHomPrecomp_preserves_homotopies T hR
  refine ⟨{ hom := moduleHomPrecomp T f
            inv := moduleHomPrecomp T g
            homotopyHomInvId := ?_
            homotopyInvHomId := ?_ }, rfl, rfl⟩
  · rw [(moduleHomPrecomp_id_comp T).2 g f,
      (moduleHomPrecomp_id_comp (P := P) (R := R) (L := P) T).1 R] at HR
    exact HR
  · rw [(moduleHomPrecomp_id_comp T).2 f g,
      (moduleHomPrecomp_id_comp (P := P) (R := R) (L := P) T).1 P] at HP
    exact HP

end CochainComplex
