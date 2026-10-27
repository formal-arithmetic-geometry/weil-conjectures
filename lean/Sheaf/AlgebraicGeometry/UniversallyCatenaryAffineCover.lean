/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.TraceFormula.CatenaryAffineOpenCover
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Universal catenarity on affine opens

Source: Stacks Project, Morphisms, Lemma 29.17.1, Tag 02J9 (blueprint:
lem-trf-universally-catenary-affine-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

private theorem catenary_equiv {R : Type u} {A : Type u}
    [CommRing R] [CommRing A] (e : R ≃+* A) (hR : IsCatenaryRing R) :
    IsCatenaryRing A := by
  let E := e.idealComapOrderIso
  have prime (p : Ideal A) (hp : p.IsPrime) : (E p).IsPrime := by
    exact hp.comap e.toRingHom
  have chain (p q : Ideal A) (n : ℕ) (c : Fin (n + 1) → Ideal A)
      (hc : IsPrimeChain A p q n c) :
      IsPrimeChain R (E p) (E q) n (fun i ↦ E (c i)) := by
    refine ⟨fun i ↦ prime _ (hc.1 i), congrArg E hc.2.1,
      congrArg E hc.2.2.1, fun i ↦ E.lt_iff_lt.mpr (hc.2.2.2 i)⟩
  have saturated (p q : Ideal A) (n : ℕ) (c : Fin (n + 1) → Ideal A)
      (hc : IsSaturatedPrimeChain A p q n c) :
      IsSaturatedPrimeChain R (E p) (E q) n (fun i ↦ E (c i)) := by
    refine ⟨chain p q n c hc.1, ?_⟩
    intro i
    rintro ⟨r, hr, hleft, hright⟩
    have : r.IsPrime := hr
    have hprime : (E.symm r).IsPrime := by
      change (r.map e).IsPrime
      exact Ideal.map_isPrime_of_equiv e
    apply hc.2 i
    refine ⟨E.symm r, hprime, ?_, ?_⟩
    · exact E.lt_iff_lt.mp (by simpa using hleft)
    · exact E.lt_iff_lt.mp (by simpa using hright)
  intro p q hp hq hpq
  have : (E p).IsPrime := prime p hp
  have : (E q).IsPrime := prime q hq
  obtain ⟨⟨N, hN⟩, hsat⟩ := hR (E p) (E q) (E.monotone hpq)
  refine ⟨⟨N, fun n c hc ↦ hN n _ (chain p q n c hc)⟩, ?_⟩
  intro n m c d hc hd
  exact hsat n m _ _ (saturated p q n c hc) (saturated p q m d hd)

/-- Universal catenarity passes from an affine open cover to every affine open.

Source: Stacks Project, Morphisms, Tag 02J9, implication (4) implies (3).
(blueprint: lem-trf-universally-catenary-affine-cover).

Proof: Fix an affine open `V` and a finite-type algebra over its ring of sections.
The associated affine morphism is locally of finite type. Refine its source by
affine opens mapping into the given cover; the affine-pair criterion gives finite
type coordinate maps, so universal catenarity of the cover rings gives catenarity
on the source charts. Apply the catenary affine-cover criterion
`lem-trf-catenary-affine-open-cover` to obtain catenarity of the arbitrary finite-type
algebra, and use the definition of universal catenarity. Local Noetherianity gives
Noetherianity of the ring of sections on `V`.
-/
theorem universallyCatenary_of_affineOpenCover
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    {I : Type u} (U : I → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hcat : ∀ i, IsUniversallyCatenary Γ(X, U i)) :
    ∀ V : X.Opens, IsAffineOpen V → IsUniversallyCatenary Γ(X, V) := by
  intro V hV
  refine ⟨IsLocallyNoetherian.component_noetherian ⟨V, hV⟩, ?_⟩
  intro A _ _ _
  let Y := Spec (CommRingCat.of A)
  let g := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A))
  have : LocallyOfFiniteType g :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  let f := CategoryTheory.CategoryStruct.comp g hV.fromSpec
  have : LocallyOfFiniteType f := inferInstance
  let J := {p : I × Y.affineOpens // (p.2 : Y.Opens) ≤ f ⁻¹ᵁ U p.1}
  let W : J → Y.Opens := fun j ↦ j.1.2
  have hW : iSup W = ⊤ := by
    apply top_unique
    intro y _
    have hy : f y ∈ iSup U := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    obtain ⟨T, hT, hyT, hTU⟩ := exists_isAffineOpen_mem_and_subset (X := Y)
      (U := f ⁻¹ᵁ U i) hi
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨i, ⟨T, hT⟩⟩, hTU⟩, hyT⟩
  have hcatW (j : J) : IsCatenaryRing Γ(Y, W j) := by
    let φ := f.appLE (U j.1.1) (W j) j.2
    let : Algebra Γ(X, U j.1.1) Γ(Y, W j) := φ.hom.toAlgebra
    have : Algebra.FiniteType Γ(X, U j.1.1) Γ(Y, W j) :=
      RingHom.finiteType_algebraMap.mp (f.finiteType_appLE (hU j.1.1) j.1.2.2 j.2)
    exact (hcat j.1.1).2 Γ(Y, W j)
  have hY : IsCatenaryRing Γ(Y, ⊤) :=
    isCatenaryRing_of_affine_openCover Y J W hW (fun j ↦ j.1.2.2) hcatW ⊤
      (isAffineOpen_top Y)
  exact catenary_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv hY

end AlgebraicGeometry
