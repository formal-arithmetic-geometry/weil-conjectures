/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData
import Sheaf.AlgebraicGeometry.VectorProjectivePresentation
import Sheaf.AlgebraicGeometry.VectorProjectiveDehomogenization
import Sheaf.AlgebraicGeometry.VectorProjectiveFrameModel
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank

/-! # Projective completion of a vector bundle

Source: Stacks Tags 01OA, 01OB, 01OE, 01NG.
(blueprint: lem-amb-vector-projective-completion). -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise

noncomputable section

namespace AlgebraicGeometry.VectorProjectiveCompletion

private def inverseAffineCover {X S : Scheme.{u}} (p : X ⟶ S) : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun V : S.affineOpens ↦ p ⁻¹ᵁ V.1) (by
    change (⨆ V : S.affineOpens, p ⁻¹ᵁ V.1) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    rfl)
private instance inverseAffineCoverPreorder {X S : Scheme.{u}} (p : X ⟶ S) :
    Preorder (inverseAffineCover p).I₀ := inferInstanceAs (Preorder S.affineOpens)
private instance inverseAffineCoverDirected {X S : Scheme.{u}} (p : X ⟶ S) :
    (inverseAffineCover p).LocallyDirected where
  trans {V W} h := X.homOfLE (p.preimage_mono (leOfHom h))
  trans_id V := by
    apply (cancel_mono (p ⁻¹ᵁ V.1).ι).mp
    change _ = 𝟙 _ ≫ _
    simp
  trans_comp h k := by apply (cancel_mono (p ⁻¹ᵁ _).ι).mp; simp
  w h := by simp [inverseAffineCover]
  directed {V W} z := by
    let z₀ : X := (pullback.fst (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι ≫ (p ⁻¹ᵁ V.1).ι) z
    have hV : p z₀ ∈ V.1 := (pullback.fst (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι z).2
    have hW : p z₀ ∈ W.1 := by
      dsimp only [z₀]
      rw [pullback.condition]
      exact (pullback.snd (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι z).2
    obtain ⟨U, hUV, hUW, hzU⟩ :=
      Scheme.GradedAlgebraData.exists_affineOpens_le V W (p z₀) hV hW
    refine ⟨U, homOfLE hUV, homOfLE hUW, ⟨z₀, hzU⟩, ?_⟩
    apply (pullback.fst (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι ≫
      (p ⁻¹ᵁ V.1).ι).isOpenEmbedding.injective
    change (pullback.lift (X.homOfLE (p.preimage_mono hUV))
      (X.homOfLE (p.preimage_mono hUW)) _ ≫
      pullback.fst (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι ≫ (p ⁻¹ᵁ V.1).ι)
        ⟨z₀, hzU⟩ = z₀
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
    rfl
  property_trans h := by infer_instance

private theorem glue_affine_charts {X S Y : Scheme.{u}} (p : X ⟶ S) (r : Y ⟶ S)
    (f : ∀ V : S.affineOpens, (p ⁻¹ᵁ V.1).toScheme ⟶ Y)
    (hf : ∀ {U V : S.affineOpens} (h : U ≤ V),
      X.homOfLE (p.preimage_mono h) ≫ f V = f U)
    (hover : ∀ V : S.affineOpens, f V ≫ r = (p ⁻¹ᵁ V.1).ι ≫ p)
    (hopen : ∀ V : S.affineOpens, IsOpenImmersion (f V)) :
    ∃ j : X ⟶ Y, IsOpenImmersion j ∧ j ≫ r = p ∧
      (∀ V : S.affineOpens, (p ⁻¹ᵁ V.1).ι ≫ j = f V) ∧
      (∀ j' : X ⟶ Y, (∀ V : S.affineOpens, (p ⁻¹ᵁ V.1).ι ≫ j' = f V) → j' = j) := by
  let C := inverseAffineCover p
  let j := C.glueMorphismsOfLocallyDirected f (fun h ↦ hf (leOfHom h))
  have hj (V : S.affineOpens) : (p ⁻¹ᵁ V.1).ι ≫ j = f V :=
    C.map_glueMorphismsOfLocallyDirected f _ V
  have hjr : j ≫ r = p := by
    apply C.hom_ext
    intro V
    change (p ⁻¹ᵁ V.1).ι ≫ j ≫ r = (p ⁻¹ᵁ V.1).ι ≫ p
    rw [← Category.assoc, hj, hover]
  have hinj : Function.Injective j := by
    intro x y hxy
    have hbase : p x = p y := by
      rw [← hjr]
      simpa only [Scheme.Hom.comp_apply] using congrArg r hxy
    obtain ⟨V, hV⟩ := Scheme.GradedAlgebraData.exists_affineOpens_mem (p x)
    let xv : (p ⁻¹ᵁ V.1).toScheme := ⟨x, hV⟩
    let yv : (p ⁻¹ᵁ V.1).toScheme := ⟨y, by change p y ∈ V.1; rw [← hbase]; exact hV⟩
    have hfv : f V xv = f V yv := by
      rw [← hj]
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using hxy
    have := hopen V
    exact congrArg Subtype.val ((f V).isOpenEmbedding.injective hfv)
  refine ⟨j, IsOpenImmersion.of_openCover_source j C hinj ?_, hjr, hj, ?_⟩
  · intro V
    change IsOpenImmersion ((p ⁻¹ᵁ V.1).ι ≫ j)
    rw [hj]
    exact hopen V
  · intro j' hj'
    apply C.hom_ext
    intro V
    exact (hj' V).trans (hj V).symm

/-- The projective completion of a constant finite rank vector bundle has its canonical
frame-independent affine chart, is proper and Noetherian, and compactifies the bundle.
The algebraic chart clauses express x_i ↦ x_i/t on every affine frame, including all
restriction maps and changes of frame. The final clause identifies the rank-zero
compactification with the identity via its structural isomorphisms.
Source: Stacks Tags 01OA, 01OB, 01OE, 01NG; blueprint, vector-bundle purity, first proof
sentence (blueprint: lem-amb-vector-projective-completion).

Proof:
1. The proved presentation construction applies the existing projective-bundle realization
of O plus F. It transports its section equivalences to Sym(O(V) × F(V)), preserving
restriction and grading, and supplies properness and the rank-zero structural isomorphism.
2. The proved dehomogenization construction sends m to x(m)/t. Its inverse evaluates
(t,x) at (1,y). Symmetric-algebra induction proves one inverse identity; induction on
powers of the degree-one submodule proves the other. The equivalences fix scalars and
commute with restriction on every affine open, without choosing a free frame.
3. Separately, the proved frame construction transports the basis of F(V) to a basis of
O(V) × F(V), with distinguished first vector (1,0). The polynomial equivalence preserves
every homogeneous degree. The resulting inverse graded ring maps induce inverse Proj
maps and identify the structural morphism and the first standard open.
4. Compose the vector bundle affine charts with the dehomogenization charts. Their
restriction equation glues them on the locally directed cover by inverse images of
all affine base opens. Equality over S reduces injectivity to one chart, giving the
open immersion. Cover extensionality proves uniqueness. The local image formula gives
the precise global image; linearity gives the displayed change-of-frame equation.
5. Properness over the Noetherian base makes the completion Noetherian. The open source
is Noetherian, hence compact; standard morphism-property instances give finite type
and separatedness. Package the factorization as the recorded compactification. At
rank zero, the presentation projection is an isomorphism, and the vector bundle
projection is locally an affine space on the empty index set, hence also an isomorphism.
The factorization gives the required equation under these structural isomorphisms. -/
theorem exists_projective_completion (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    ∃ (P : Presentation S F)
      (ht : ∀ V : S.affineOpens, t P V ∈ P.algebra.grading V 1)
      (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (op V.1) ≃+*
        HomogeneousLocalization.Away (P.algebra.grading V) (t P V)),
      IsNoetherian P.algebra.relProj ∧ IsProper P.algebra.relProjHom ∧
      (∀ (V : S.affineOpens) (m : F.val.obj (op V.1)),
        (a V (SymmetricAlgebra.ι _ _ m)).val =
          algebraMap (P.algebra.obj V) (Localization.Away (t P V)) (x P V m) *
            IsLocalization.Away.invSelf (t P V)) ∧
      (∀ (V : S.affineOpens) (r : Γ(S, V.1)),
        (a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r)).val =
          algebraMap (P.algebra.obj V) (Localization.Away (t P V))
            (algebraMap Γ(S, V.1) (P.algebra.obj V) r)) ∧
      (∀ (V : S.affineOpens) (e : VectorBundleZeroSection.Trivialization S d F V.1),
        ∃ q : MvPolynomial (Fin (d + 1)) Γ(S, V.1) ≃ₐ[Γ(S, V.1)] P.algebra.obj V,
          q (MvPolynomial.X 0) = t P V ∧
          (∀ i : Fin d, q (MvPolynomial.X i.succ) =
            x P V (VectorBundleZeroSection.frameSection S d F V.1 e i)) ∧
          (∀ (n : ℕ) (f : MvPolynomial (Fin (d + 1)) Γ(S, V.1)),
            q f ∈ P.algebra.grading V n ↔
              f ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) Γ(S, V.1) n) ∧
          ∃ (g : (RelativeProjectiveSpace.algebra V.1.toScheme d).sectionGrade
                (affineTop V) →+*ᵍ P.algebra.grading V) (hg : Function.Bijective g)
              (b : Proj (P.algebra.grading V) ≅ RelativeProjectiveSpace.scheme V.1.toScheme d),
            (∀ r : Γ(V.1.toScheme, ⊤),
              g ((RelativeProjectiveSpace.algebra V.1.toScheme d).algebra.obj.hom.hom.app
                (op ⊤) r) = algebraMap Γ(S, V.1) (P.algebra.obj V) (V.1.topIso.hom r)) ∧
            (∀ i : Fin (d + 1),
              g (RelativeProjectiveSpace.coordinate V.1.toScheme d (affineTop V) i) =
                q (MvPolynomial.X i)) ∧
            b.hom = Proj.map g (GradedRingHom.irrelevant_le_map_of_surjective hg.surjective) ≫
              projectiveChart V d ∧
            b.hom ≫ RelativeProjectiveSpace.π V.1.toScheme d = P.algebra.toOpen V ∧
            b.hom ⁻¹ᵁ RelativeProjectiveSpace.standardOpen V.1.toScheme d 0 =
              Proj.basicOpen (P.algebra.grading V) (t P V)) ∧
      (∀ (U V : S.affineOpens) (h : U.1 ≤ V.1),
        Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.restriction F (homOfLE h).op)) ≫
          chartMap P ht a V = chartMap P ht a U) ∧
      (∀ (V : S.affineOpens) (e e' : VectorBundleZeroSection.Trivialization S d F V.1)
          (G : Matrix (Fin d) (Fin d) Γ(S, V.1)),
        (∀ j : Fin d, VectorBundleZeroSection.frameSection S d F V.1 e' j =
          ∑ i : Fin d, G i j • VectorBundleZeroSection.frameSection S d F V.1 e i) →
        ∀ j : Fin d,
          a V (SymmetricAlgebra.ι _ _ (VectorBundleZeroSection.frameSection S d F V.1 e' j)) =
            ∑ i : Fin d,
              a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) (G i j)) *
                a V (SymmetricAlgebra.ι _ _
                  (VectorBundleZeroSection.frameSection S d F V.1 e i))) ∧
      IsSeparated (VectorBundleZeroSection.π S d F) ∧
      LocallyOfFiniteType (VectorBundleZeroSection.π S d F) ∧
      QuasiCompact (VectorBundleZeroSection.π S d F) ∧
      IsNoetherian (VectorBundleZeroSection.scheme S d F) ∧
      ∃ c : Compactification (VectorBundleZeroSection.π S d F),
        ∃ hZ : c.Z = P.algebra.relProj,
          c.g = eqToHom hZ ≫ P.algebra.relProjHom ∧
          (c.i ≫ eqToHom hZ).opensRange = chartOpen P ∧
          (∀ V : S.affineOpens,
            VectorBundleZeroSection.affineChart S d F V ≫ chartMap P ht a V =
              ((VectorBundleZeroSection.π S d F) ⁻¹ᵁ V.1).ι ≫ c.i ≫ eqToHom hZ) ∧
          (∀ j : VectorBundleZeroSection.scheme S d F ⟶ P.algebra.relProj,
            (∀ V : S.affineOpens,
              VectorBundleZeroSection.affineChart S d F V ≫ chartMap P ht a V =
                ((VectorBundleZeroSection.π S d F) ⁻¹ᵁ V.1).ι ≫ j) →
            j = c.i ≫ eqToHom hZ) ∧
          (d = 0 → ∃ (eE : VectorBundleZeroSection.scheme S d F ≅ S)
              (eP : P.algebra.relProj ≅ S),
            eE.hom = VectorBundleZeroSection.π S d F ∧
            eP.hom = P.algebra.relProjHom ∧
            c.i ≫ eqToHom hZ = eE.hom ≫ eP.inv) := by
  classical
  obtain ⟨P, hproper, hzero⟩ := exists_projectivePresentation S d F
  obtain ⟨ht, a, hgen, hcoeff, hrest⟩ := exists_affineDehomogenization S F P
  have hframe := exists_frameModel S d F P
  have hscalar (V : S.affineOpens) (r : Γ(S, V.1)) :
      (a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r)).val =
        algebraMap (P.algebra.obj V) (Localization.Away (t P V))
          (algebraMap Γ(S, V.1) (P.algebra.obj V) r) := by
    rw [hcoeff, HomogeneousLocalization.val_algebraMap,
      Localization.mk_one_eq_algebraMap]
  have : IsProper P.algebra.relProjHom := hproper
  have : IsLocallyNoetherian P.algebra.relProj :=
    LocallyOfFiniteType.isLocallyNoetherian P.algebra.relProjHom
  have : CompactSpace P.algebra.relProj :=
    QuasiCompact.compactSpace_of_compactSpace P.algebra.relProjHom
  have : IsNoetherian P.algebra.relProj := ⟨⟩
  have hascalar (V : S.affineOpens) (r : Γ(S, V.1)) :
      a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r) =
        algebraMap Γ(S, V.1)
          (HomogeneousLocalization.Away (P.algebra.grading V) (t P V)) r := by
    apply HomogeneousLocalization.val_injective
    rw [hscalar, HomogeneousLocalization.val_algebraMap,
      Localization.mk_one_eq_algebraMap]
  have hchartIso (V : S.affineOpens) : IsIso
      (Spec.map (CommRingCat.ofHom (a V).symm.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (a V).symm.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (a V).symm.bijective
    infer_instance
  have hchartOpen (V : S.affineOpens) : IsOpenImmersion (chartMap P ht a V) := by
    have := hchartIso V
    unfold chartMap
    infer_instance
  have hchartOver (V : S.affineOpens) : chartMap P ht a V ≫ P.algebra.relProjHom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1)
        (SymmetricAlgebraSheaf.sections F (op V.1)))) ≫ V.2.isoSpec.inv ≫ V.1.ι := by
    simp only [chartMap, Category.assoc, P.algebra.relProjι_relProjHom]
    change Spec.map _ ≫ Proj.awayι _ _ _ _ ≫
      (Proj.toSpecOfAlgebra (P.algebra.grading V) ≫ V.2.isoSpec.inv) ≫ V.1.ι = _
    rw [Category.assoc, Proj.awayι_toSpecOfAlgebra_assoc, ← Spec.map_comp_assoc]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (a V).symm_apply_eq.mpr (hascalar V r).symm
  let p := VectorBundleZeroSection.π S d F
  let X := VectorBundleZeroSection.scheme S d F
  let localMap (V : S.affineOpens) : (p ⁻¹ᵁ V.1).toScheme ⟶ P.algebra.relProj :=
    VectorBundleZeroSection.affineChart S d F V ≫ chartMap P ht a V
  have hlocal (V : S.affineOpens) : IsOpenImmersion (localMap V) := by
    have := hchartOpen V
    have := (VectorBundleZeroSection.affineChart_spec S d F V).1
    dsimp only [localMap]
    infer_instance
  have hover (V : S.affineOpens) : localMap V ≫ P.algebra.relProjHom =
      (p ⁻¹ᵁ V.1).ι ≫ p := by
    dsimp only [localMap]
    rw [Category.assoc, hchartOver]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ V.1.ι)
        (VectorBundleZeroSection.affineChart_spec S d F V).2.1 |>.trans
          (morphismRestrict_ι p V.1)
  have hcompat {U V : S.affineOpens} (h : U ≤ V) :
      X.homOfLE (p.preimage_mono h) ≫ localMap V = localMap U := by
    have he := VectorBundleZeroSection.affineChart_naturality S d F U V h
    simp only [Scheme.Hom.resLE_id] at he
    dsimp only [localMap]
    rw [← Category.assoc, he, Category.assoc, hrest U V h]
  obtain ⟨j, hjopen, hjover, hj, hjunique⟩ :=
    glue_affine_charts p P.algebra.relProjHom localMap hcompat hover hlocal
  have : IsOpenImmersion j := hjopen
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
  have : TopologicalSpace.NoetherianSpace X :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace X := inferInstance
  have : IsNoetherian X := ⟨⟩
  have : IsSeparated p := by rw [← hjover]; infer_instance
  have : LocallyOfFiniteType p := by rw [← hjover]; infer_instance
  have : QuasiCompact p := inferInstance
  have hchange (V : S.affineOpens)
      (e e' : VectorBundleZeroSection.Trivialization S d F V.1)
      (G : Matrix (Fin d) (Fin d) Γ(S, V.1))
      (he : ∀ j : Fin d, VectorBundleZeroSection.frameSection S d F V.1 e' j =
        ∑ i : Fin d, G i j • VectorBundleZeroSection.frameSection S d F V.1 e i)
      (j : Fin d) :
      a V (SymmetricAlgebra.ι _ _ (VectorBundleZeroSection.frameSection S d F V.1 e' j)) =
        ∑ i : Fin d,
          a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) (G i j)) *
            a V (SymmetricAlgebra.ι _ _
              (VectorBundleZeroSection.frameSection S d F V.1 e i)) := by
    rw [he, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, Algebra.smul_def, map_mul]
  let c : Compactification p :=
    { Z := P.algebra.relProj
      g := P.algebra.relProjHom
      i := j
      comm := hjover.symm
      isProper := hproper
      isOpenImmersion := hjopen }
  have hrange : j.opensRange = chartOpen P := by
    have hcover : (⨆ V : S.affineOpens, p ⁻¹ᵁ V.1) = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
      rfl
    rw [← j.image_top_eq_opensRange, ← hcover, j.image_iSup]
    unfold chartOpen
    apply iSup_congr
    intro V
    have := hchartIso V
    have := (VectorBundleZeroSection.affineChart_spec S d F V).1
    rw [← Scheme.Opens.opensRange_ι (p ⁻¹ᵁ V.1),
      ← Scheme.Hom.opensRange_comp]
    simp only [hj V]
    dsimp only [localMap, chartMap]
    rw [Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp,
      Proj.opensRange_awayι]
  refine ⟨P, ht, a, inferInstance, hproper, hgen, hscalar, hframe, hrest, hchange,
    inferInstance, inferInstance, inferInstance, inferInstance, c, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [c]
  · simpa [c] using hrange
  · intro V
    simpa [c, localMap] using (hj V).symm
  · intro j' hj'
    apply hjunique
    intro V
    exact (hj' V).symm
  · intro hd
    have : IsIso P.algebra.relProjHom := hzero hd
    have : IsIso p := by
      subst d
      obtain ⟨I, U, hU, e⟩ :=
        Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := 0)
      apply IsZariskiLocalAtTarget.of_iSup_eq_top
        (P := MorphismProperty.isomorphisms Scheme) U hU
      intro i
      obtain ⟨hi, ho, _⟩ := VectorBundleZeroSection.trivializationMap_spec S 0 F (U i)
        (e i).some
      have := hi
      rw [← ho]
      infer_instance
    refine ⟨asIso p, asIso P.algebra.relProjHom, rfl, rfl, ?_⟩
    change j ≫ 𝟙 _ = p ≫ inv P.algebra.relProjHom
    rw [Category.comp_id, ← hjover, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.VectorProjectiveCompletion
