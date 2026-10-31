/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FpqcCanonicalPullbackDatum
import WeilConjectures.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding

/-! # Finite affine refinement and the Cartesian local model

Source: Stacks Project, Descent, Tags 02W3, 023Y and 023X;
Topologies, Tags 021P and 021Q
(blueprint: lem-trf-fppf-affine-refinement-pullback-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem pullback_datum_over_base
    {T U A Z AU ZU : Scheme.{u}} (a : A ⟶ T) (q : Z ⟶ A)
    (D : Over.DescentDatum a (Over.mk q)) (u : U ⟶ T)
    (b : AU ⟶ A) (aU : AU ⟶ U) (hAU : b ≫ a = aU ≫ u)
    (z : ZU ⟶ Z) (v : ZU ⟶ AU) (hZU : IsPullback z v q b) :
    ∃ DU : Over.DescentDatum aU (Over.mk v),
      ∀ (H : Scheme.{u}) (r s : H ⟶ AU) (hrs : r ≫ aU = s ≫ aU)
        (x : Over.mk r ⟶ Over.mk v) (y : Over.mk (r ≫ b) ⟶ Over.mk q)
        (ht : (r ≫ b) ≫ a = (s ≫ b) ≫ a),
        y.left = x.left ≫ z →
        (DU.transport r s hrs x).left ≫ z =
          (D.transport (r ≫ b) (s ≫ b) ht y).left := by
  let point {H : Scheme.{u}} (r : H ⟶ AU) (x : Over.mk r ⟶ Over.mk v) :
      Over.mk (r ≫ b) ⟶ Over.mk q :=
    Over.homMk (x.left ≫ z) (by
      change (x.left ≫ z) ≫ q = r ≫ b
      rw [Category.assoc, hZU.w, ← Category.assoc]
      exact congrArg (fun k ↦ k ≫ b) (Over.w x))
  let tr {H : Scheme.{u}} (r s : H ⟶ AU) (hrs : r ≫ aU = s ≫ aU)
      (x : Over.mk r ⟶ Over.mk v) : Over.mk s ⟶ Over.mk v :=
    Over.homMk (hZU.lift
      (D.transport (r ≫ b) (s ≫ b)
        (by simpa only [Category.assoc, hAU] using congrArg (fun k ↦ k ≫ u) hrs) (point r x)).left s
      (Over.w _)) (hZU.lift_snd _ _ _)
  have hz {H : Scheme.{u}} (r s : H ⟶ AU) (hrs : r ≫ aU = s ≫ aU)
      (x : Over.mk r ⟶ Over.mk v) :
      point s (tr r s hrs x) = D.transport (r ≫ b) (s ≫ b)
        (by simpa only [Category.assoc, hAU] using congrArg (fun k ↦ k ≫ u) hrs) (point r x) := by
    ext : 1
    exact hZU.lift_fst _ _ _
  have hext {H : Scheme.{u}} (r : H ⟶ AU) (x y : Over.mk r ⟶ Over.mk v)
      (h : point r x = point r y) : x = y := by
    ext : 1
    apply hZU.hom_ext
    · exact congrArg (fun t ↦ t.left) h
    · exact (Over.w x).trans (Over.w y).symm
  refine ⟨{ transport := tr
            transport_homMk_comp := ?_
            transport_self := ?_
            transport_transport := ?_ }, ?_⟩
  · intro H H' k r s hrs x
    apply hext
    simp only [hz]
    ext : 1
    convert congrArg (fun t ↦ t.left)
      (D.transport_homMk_comp k (r ≫ b) (s ≫ b)
        (by simpa only [Category.assoc, hAU] using
          congrArg (fun k ↦ k ≫ u) hrs) (point r x)) using 1 <;>
      simp [point, tr, Category.assoc, hZU.lift_fst]
    congr 2
  · intro H r x
    apply hext
    simp only [hz, D.transport_self]
  · intro H r s t hrs hst x
    apply hext
    simp only [hz, D.transport_transport]
  · intro H r s hrs x y ht hy
    have he : y = point r x := Over.OverMorphism.ext hy
    subst y
    exact congrArg (fun t ↦ t.left) (hz r s hrs x)

/-- An affine open of the base admits a finite affine fppf refinement, and the pullback
of the singleton scheme descent datum is the coproduct of the local base changes.

Source: Stacks Project, Descent, Tags 02W3 (affine reduction), 023Y (pullback),
023X (family versus singleton); Topologies, Tags 021P and 021Q
(blueprint: lem-trf-fppf-affine-refinement-pullback-model).

The cofan hypotheses present exactly the coproducts A and Z in the statement; the
component equations specify their induced structure maps. The two IsPullback witnesses
present A_U and Z_U, so this formulation applies in particular to the chosen pullbacks.
The hypothesis hD identifies the singleton transport with the given family transitions,
using its specified representing bijections. Quantification over the point y and the
proof ht is independent of choices, since its underlying map is prescribed.

Proof:
1. Pull D back along b with fixed base T using
   lem-galois-fpqc-canonical-pullback-datum. Restrict its transport to pairs with the
   same image in U. The Cartesian equations make these pairs equal over T, and the
   inherited naturality and cocycle give D_U (def-pd-descent-datum). Projection to Z
   gives the displayed transport equation; this does not assume a variable-base
   conclusion from the fixed-base pullback lemma.
2. Base change the covering to U (lem-trf-fppf-covering-base-change), and apply
   lem-pc-fppf-affine-refinement to obtain finitely many affine opens W_j in T_i x_T U.
   Their maps to U are flat and locally of finite presentation and jointly surjective.
3. Form their coproduct C (lem-weil-pbc-scheme-coproduct-family). It is affine by
   lem-weil-pbc-affine-morphism-permanence. On each open component the stalk maps
   and affine neighborhoods give flatness and local finite presentation of p.
   Coverage gives surjectivity. Since C and U are affine, p is affine by
   lem-weil-pbc-morphism-affine-schemes-affine, hence quasi-compact and separated,
   and therefore quasi-separated. Together these are finite presentation in
   def-weil-pbc-scheme-conventions.
4. For every affine open of U its inverse image under p is affine, and surjects
   onto that open. This singleton affine open verifies def-weil-pbc-fpqc-covering;
   no replacement of fpqc by just flat surjective families is made.
5. The coproduct and pullback universal properties give h with the displayed
   component equations. Apply lem-galois-fpqc-canonical-pullback-datum over U to
   D_U and h, giving E and IsBaseChange. Its projection square is Cartesian.
6. Pull back the disjoint open components of C. By
   lem-weil-pbc-open-immersion-base-change these give disjoint open components of
   the pullback. The pullback universal property identifies each with
   Z x_A W_j and then V_i x_T_i W_j, since the inverse image of T_i in Z is V_i.
   Glue these comparisons and their inverses by lem-weil-pbc-scheme-morphism-gluing
   and the coproduct universal property. Componentwise identities prove they are
   inverse, and each preserves the projection to W_j, giving the equation over C.
7. For empty U choose m = 0. All schemes over U are empty; their unique maps
   give the transport and projection equations. Flatness and local finite
   presentation are vacuous, and the empty identity is affine and surjective.
   Conversely a family indexed by Fin 0 covers only an empty U. -/
theorem exists_fppf_affine_refinement_pullback_model
    {I : Type (u + 1)} {T : Scheme.{u}} {Ti : I → Scheme.{u}}
    (f : ∀ i, Ti i ⟶ T)
    (hcov : Presieve.ofArrows Ti f ∈ Scheme.fppfPrecoverage T)
    (F : SchemeCoverDescentDatum f)
    {A Z : Scheme.{u}} (inA : ∀ i, Ti i ⟶ A)
    (inZ : ∀ i, (F.localScheme i).left ⟶ Z)
    (hA : IsColimit (Cofan.mk A inA)) (hZ : IsColimit (Cofan.mk Z inZ))
    (a : A ⟶ T) (q : Z ⟶ A)
    (ha : ∀ i, inA i ≫ a = f i)
    (hq : ∀ i, inZ i ≫ q = (F.localScheme i).hom ≫ inA i)
    (D : Over.DescentDatum a (Over.mk q))
    (hD : ∀ (H : Scheme.{u}) (pH : H ⟶ T) (i k : I)
      (r : H ⟶ Ti i) (s : H ⟶ Ti k) (hr : r ≫ f i = pH) (hs : s ≫ f k = pH)
      (x : (F.data.obj i).obj.obj (op ((Over.map r).obj (Over.mk (𝟙 H)))))
      (y : Over.mk (r ≫ inA i) ⟶ Over.mk q)
      (ht : (r ≫ inA i) ≫ a = (s ≫ inA k) ≫ a),
      y.left = ((F.representation i).homEquiv.symm x).left ≫ inZ i →
      (D.transport (r ≫ inA i) (s ≫ inA k) ht y).left =
        ((F.representation k).homEquiv.symm
          ((F.data.hom pH r s hr hs).hom.app (op (Over.mk (𝟙 H))) x)).left ≫ inZ k)
    (U : T.Opens) (hU : IsAffineOpen U)
    {AU ZU : Scheme.{u}} (b : AU ⟶ A) (aU : AU ⟶ U.toScheme)
    (hAU : IsPullback b aU a U.ι)
    (z : ZU ⟶ Z) (v : ZU ⟶ AU) (hZU : IsPullback z v q b) :
    ∃ DU : Over.DescentDatum aU (Over.mk v),
      (∀ (H : Scheme.{u}) (r s : H ⟶ AU) (hrs : r ≫ aU = s ≫ aU)
        (x : Over.mk r ⟶ Over.mk v) (y : Over.mk (r ≫ b) ⟶ Over.mk q)
        (ht : (r ≫ b) ≫ a = (s ≫ b) ≫ a),
        y.left = x.left ≫ z →
        (DU.transport r s hrs x).left ≫ z = (D.transport (r ≫ b) (s ≫ b) ht y).left) ∧
      ∃ (m : ℕ) (i : Fin m → I)
        (W : ∀ j, (pullback (f (i j)) U.ι).Opens),
        (∀ j, IsAffineOpen (W j)) ∧
        (∀ j, Flat ((W j).ι ≫ pullback.snd (f (i j)) U.ι) ∧
          LocallyOfFinitePresentation ((W j).ι ≫ pullback.snd (f (i j)) U.ι)) ∧
        (∀ x : U.toScheme, ∃ j, x ∈ Set.range ((W j).ι ≫ pullback.snd (f (i j)) U.ι)) ∧
        ∃ (p : (∐ fun j ↦ (W j).toScheme) ⟶ U.toScheme),
          p = Sigma.desc (fun j ↦ (W j).ι ≫ pullback.snd (f (i j)) U.ι) ∧
          IsAffine (∐ fun j ↦ (W j).toScheme) ∧
          Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
          QuasiCompact p ∧ QuasiSeparated p ∧
          Presieve.singleton p ∈ Scheme.fpqcPrecoverage U.toScheme ∧
          ∃ (h : (∐ fun j ↦ (W j).toScheme) ⟶ AU) (hh : h ≫ aU = p),
            (∀ j, Sigma.ι (fun j ↦ (W j).toScheme) j ≫ h ≫ b =
              (W j).ι ≫ pullback.fst (f (i j)) U.ι ≫ inA (i j)) ∧
            ∃ E : Over.DescentDatum p (Over.mk (pullback.snd v h)),
              Over.DescentDatum.IsBaseChange hh (pullback.condition (f := v) (g := h))
                DU E ∧
              ∃ e : pullback v h ≅
                ∐ (fun j ↦ pullback (F.localScheme (i j)).hom
                  ((W j).ι ≫ pullback.fst (f (i j)) U.ι)),
                e.hom ≫ Sigma.desc (fun j ↦
                  pullback.snd (F.localScheme (i j)).hom
                    ((W j).ι ≫ pullback.fst (f (i j)) U.ι) ≫
                    Sigma.ι (fun j ↦ (W j).toScheme) j) = pullback.snd v h := by
  classical
  have _compatibility := hD
  obtain ⟨DU, hDU⟩ := pullback_datum_over_base a q D U.ι b aU hAU.w z v hZU
  refine ⟨DU, hDU, ?_⟩
  let : IsAffine U.toScheme := hU
  have hbc := Precoverage.mem_coverings_of_isPullback f hcov U.ι
    (fun i ↦ pullback.snd (f i) U.ι) (fun i ↦ pullback.fst (f i) U.ι)
    (fun i ↦ (IsPullback.of_hasPullback (f i) U.ι).flip)
  obtain ⟨m, i, W, hW, hcover⟩ := Scheme.exists_finite_fppf_affine_open_refinement
    (fun i ↦ pullback (f i) U.ι) (fun i ↦ pullback.snd (f i) U.ι) hbc
  have hprops := (Scheme.ofArrows_mem_precoverage_iff
    (@Flat ⊓ @LocallyOfFinitePresentation)).mp hcover
  let w (j : Fin m) := (W j).ι ≫ pullback.snd (f (i j)) U.ι
  let r (j : Fin m) := (W j).ι ≫ pullback.fst (f (i j)) U.ι
  let (j : Fin m) : IsAffine (W j).toScheme := hW j
  let (j : Fin m) : Flat (w j) := (hprops.2 j).1
  let (j : Fin m) : LocallyOfFinitePresentation (w j) := (hprops.2 j).2
  let p := Sigma.desc w
  let : Flat p := inferInstance
  let : LocallyOfFinitePresentation p :=
    IsZariskiLocalAtSource.sigmaDesc (fun j ↦ (hprops.2 j).2)
  let : Surjective p := ⟨fun x ↦ by
    obtain ⟨j, y, hy⟩ := hprops.1 x
    refine ⟨Sigma.ι (fun j ↦ (W j).toScheme) j y, ?_⟩
    change ((Sigma.ι (fun j ↦ (W j).toScheme) j) ≫ p) y = x
    rw [show Sigma.ι (fun j ↦ (W j).toScheme) j ≫ p = w j from Sigma.ι_desc _ _]
    exact hy⟩
  have hfpqc : Presieve.singleton p ∈ Scheme.fpqcPrecoverage U.toScheme :=
    ⟨Scheme.Hom.singleton_mem_qcPrecoverage p,
      (Scheme.singleton_mem_precoverage_iff _ p).mpr ⟨p.surjective, inferInstance⟩⟩
  let hj (j : Fin m) : (W j).toScheme ⟶ AU :=
    hAU.lift (r j ≫ inA (i j)) (w j) (by
      simp only [Category.assoc, ha, r, w]
      rw [pullback.condition])
  let h := Sigma.desc hj
  have hh : h ≫ aU = p := by
    apply Sigma.hom_ext
    intro j
    simp [h, p, hj]
  refine ⟨m, i, W, hW, hprops.2, hprops.1, p, rfl, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfpqc,
    h, hh, ?_, ?_⟩
  · intro j
    simp [h, hj, r, Category.assoc]
  · obtain ⟨E, hE⟩ := exists_canonical_pullback_descent_datum aU p h hh DU
    refine ⟨E, hE, ?_⟩
    let : HasCoproduct Ti := HasColimit.mk ⟨Cofan.mk A inA, hA⟩
    let : HasCoproduct (fun k ↦ (F.localScheme k).left) :=
      HasColimit.mk ⟨Cofan.mk Z inZ, hZ⟩
    let eA := (coproductIsCoproduct Ti).coconePointUniqueUpToIso hA
    let eZ := (coproductIsCoproduct (fun k ↦ (F.localScheme k).left)).coconePointUniqueUpToIso hZ
    have heA (k : I) : Sigma.ι Ti k ≫ eA.hom = inA k :=
      (coproductIsCoproduct Ti).comp_coconePointUniqueUpToIso_hom hA ⟨k⟩
    have heZ (k : I) : Sigma.ι (fun k ↦ (F.localScheme k).left) k ≫ eZ.hom = inZ k :=
      (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hZ ⟨k⟩
    have heq : (CategoryTheory.Limits.Sigma.map (fun k ↦ (F.localScheme k).hom)) ≫
        eA.hom = eZ.hom ≫ q := by
      apply Sigma.hom_ext
      intro k
      rw [← Category.assoc, Sigma.ι_map, Category.assoc, heA,
        ← Category.assoc, heZ, hq]
    obtain ⟨_, hcomp, _⟩ :=
      (fppf_family_coproduct_descent_encoding T Ti f hcov F).2.2.2.2.2.2.2
    have hcart (k : I) : IsPullback (inZ k) (F.localScheme k).hom q (inA k) := by
      apply (hcomp k).of_iso (Iso.refl _) eZ (Iso.refl _) eA
      · simpa using heZ k
      · simp
      · simpa [SchemeCoverDescentDatum.coproductScheme] using heq
      · simpa using heA k
    let Q (j : Fin m) := pullback (F.localScheme (i j)).hom (r j)
    let t (j : Fin m) : Q j ⟶ Z :=
      pullback.fst (F.localScheme (i j)).hom (r j) ≫ inZ (i j)
    let sj (j : Fin m) : Q j ⟶ (W j).toScheme :=
      pullback.snd (F.localScheme (i j)).hom (r j)
    have hcartQ (j : Fin m) : IsPullback (t j) (sj j) q (hj j ≫ b) := by
      simpa only [hj, hAU.lift_fst] using
        (IsPullback.of_hasPullback (F.localScheme (i j)).hom (r j)).paste_horiz (hcart (i j))
    let tj (j : Fin m) : Q j ⟶ ZU :=
      hZU.lift (t j) (sj j ≫ hj j) (hcartQ j).w
    have hcartU (j : Fin m) : IsPullback (tj j) (sj j) v (hj j) :=
      IsPullback.of_right' (hcartQ j) hZU
    have htotal : IsPullback (Sigma.desc tj)
        (Sigma.desc (fun j ↦ sj j ≫ Sigma.ι (fun j ↦ (W j).toScheme) j)) v h := by
      convert
        (FinitaryPreExtensive.isUniversal_finiteCoproducts
        (coproductIsCoproduct (fun j ↦ (W j).toScheme))).isPullback_of_isColimit_left
          hj h v tj sj hcartU (coproductIsCoproduct Q) (by simp [h]) using 1 <;> rfl
    refine ⟨(IsPullback.of_hasPullback v h).isoIsPullback _ _ htotal, ?_⟩
    exact (IsPullback.of_hasPullback v h).isoIsPullback_hom_snd _ _ htotal

end AlgebraicGeometry
