/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import all WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient

/-! # Left exact functors and upper smart truncations

Source: Mathlib, upper smart truncation and preservation of kernel forks;
Stacks Project, Tag 015X, Remark 13.26.15.
(blueprint: lem-sp-left-exact-truncation-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
variable {B : Type u} [Category.{v} B] [Abelian B]
  {C : Type u'} [Category.{v'} C] [Abelian C]
  (T : B ⥤ C) [T.Additive] [PreservesFiniteLimits T]

set_option backward.isDefEq.respectTransparency false in
/-- An additive left exact functor commutes with upper smart truncation, by the
unique isomorphism compatible with the inclusion into the original complex.
Source: Mathlib's upper smart truncation, `HomologicalComplex.cyclesIsKernel`,
and preservation of kernel forks; Stacks Project, Tag 015X, Remark 13.26.15.
(blueprint: lem-sp-left-exact-truncation-iso).

Proof. Below the truncation degree identify both complexes with the original
complex. At the boundary identify both with cycles and use preservation of
its kernel fork by the left exact functor. Above the boundary both are zero.
These coordinate isomorphisms commute with the truncation inclusions. Cancel
the monic inclusion to verify the differential equation and assemble a complex
isomorphism. The same monic inclusion proves uniqueness. This applies to all
integer truncation degrees, including those below the support of the complex. -/
theorem leftExact_truncation_iso (K : CochainComplex B ℤ) (q : ℤ) :
    ∃! e : (T.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.truncLE K q) ≅
      CochainComplex.truncLE ((T.mapHomologicalComplex (.up ℤ)).obj K) q,
      e.hom ≫ CochainComplex.ιTruncLE _ q =
        (T.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE q) := by
  classical
  let M : CochainComplex C ℤ := (T.mapHomologicalComplex (.up ℤ)).obj K
  have hzero : T.map (K.iCycles q) ≫ (M.sc q).g = 0 := by
    simp [M, ← T.map_comp]
  let hker : IsLimit (KernelFork.ofι (T.map (K.iCycles q)) hzero) :=
    isLimitForkMapOfIsLimit' T (K.iCycles_d q ((ComplexShape.up ℤ).next q))
      (K.cyclesIsKernel q _ rfl)
  let c : T.obj (K.cycles q) ≅ M.cycles q := (M.sc q).isoCyclesOfIsLimit hker
  have hc : c.hom ≫ M.iCycles q = T.map (K.iCycles q) :=
    (M.sc q).isoCyclesOfIsLimit_hom_iCycles hker
  let e (p : ℤ) : T.obj ((CochainComplex.truncLE K q).X p) ≅ (CochainComplex.truncLE M q).X p :=
    if hp : p < q then
      T.mapIso (K.truncLEXIso q p hp) ≪≫ (M.truncLEXIso q p hp).symm
    else if he : p = q then by
      subst p
      exact T.mapIso (K.truncLEXIsoCycles q) ≪≫
        c ≪≫ (M.truncLEXIsoCycles q).symm
    else
      (T.map_isZero ((CochainComplex.truncLE K q).isZero_of_isStrictlyLE q p (by omega))).iso
        ((CochainComplex.truncLE M q).isZero_of_isStrictlyLE q p (by omega))
  have he (p : ℤ) : (e p).hom ≫ (M.ιTruncLE q).f p = T.map ((K.ιTruncLE q).f p) := by
    dsimp only [e]
    split_ifs with hp hq
    · rw [(CochainComplex.truncLE_inclusion_coordinates M q).2 p hp]
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      rw [(CochainComplex.truncLE_inclusion_coordinates K q).2 p hp]
    · subst p
      rw [← (CochainComplex.truncLE_inclusion_coordinates M q).1,
        ← (CochainComplex.truncLE_inclusion_coordinates K q).1, T.map_comp]
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
        Iso.inv_hom_id_assoc]
      rw [hc]
    · exact (T.map_isZero
        ((CochainComplex.truncLE K q).isZero_of_isStrictlyLE q p (by omega))).eq_of_src _ _
  let E : (T.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.truncLE K q) ≅
      CochainComplex.truncLE M q :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro i j hij
      have : Mono ((M.ιTruncLE q).f j) :=
        inferInstanceAs (Mono ((HomologicalComplex.ιTruncLE M
          (ComplexShape.embeddingUpIntLE q)).f j))
      apply (cancel_mono ((M.ιTruncLE q).f j)).1
      rw [Category.assoc, ← (M.ιTruncLE q).comm, ← Category.assoc, he, Category.assoc, he]
      change T.map ((K.ιTruncLE q).f i) ≫ T.map (K.d i j) =
        T.map ((CochainComplex.truncLE K q).d i j) ≫ T.map ((K.ιTruncLE q).f j)
      rw [← T.map_comp, ← T.map_comp, (K.ιTruncLE q).comm])
  have hE : E.hom ≫ CochainComplex.ιTruncLE M q =
      (T.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE q) := by
    apply HomologicalComplex.Hom.ext
    funext p
    exact he p
  refine ⟨E, hE, ?_⟩
  intro E' hE'
  apply Iso.ext
  have : Mono (CochainComplex.ιTruncLE M q) :=
    inferInstanceAs (Mono (HomologicalComplex.ιTruncLE M
      (ComplexShape.embeddingUpIntLE q)))
  apply (cancel_mono (CochainComplex.ιTruncLE M q)).1
  exact hE'.trans hE.symm

end CategoryTheory
