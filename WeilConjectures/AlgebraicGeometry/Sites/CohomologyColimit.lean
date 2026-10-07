/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Étale cohomology of a direct sum on a quasi-compact quasi-separated scheme

On a quasi-compact and quasi-separated scheme `X`, étale cohomology commutes with filtered
colimits of abelian sheaves ([Stacks 03Q6]), and hence with direct sums, a direct sum being the
filtered colimit of its finite partial sums. We record the consequence used for the divisor
sequence: a direct sum of sheaves without cohomology in degree `n` has no cohomology in degree
`n`.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_H_one_of_isColimit_cofan`: on a quasi-compact
  quasi-separated scheme, if `H¹(X, Fᵢ) = 0` for all `i`, then `H¹(X, ⨁ᵢ Fᵢ) = 0`.
- `AlgebraicGeometry.Scheme.subsingleton_H_of_isColimit_cofan`: the same in every degree. The
  proof is `sorry`.

## Implementation notes

In degree one we argue with lifts of global sections instead of filtered colimits. Let
`0 → ⨁ᵢ Fᵢ → E → Q → 0` be exact and `q` a global section of `Q`. It lifts to sections `e_a` of
`E` on a finite family of affine étale `X`-schemes `U_a` covering `X`. The differences of the
`e_a` on the quasi-compact overlaps `U_a ×_X U_b` are sections of `⨁ᵢ Fᵢ`, hence locally finite
sums, and finitely many indices `S` suffice for all of them. Modulo the finite sum
`G = ⨁_{i ∈ S} Fᵢ` the `e_a` glue, and as `H¹(G) = 0` the glued section lifts to `E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- On an étale `X`-scheme `W` with quasi-compact underlying space, every covering sieve
contains a finite jointly surjective family of étale `X`-schemes with affine underlying
schemes. -/
lemma exists_finite_affine_of_mem_smallEtaleTopology {W : X.Etale} [CompactSpace W.left]
    {R : Sieve W} (hR : R ∈ X.smallEtaleTopology W) :
    ∃ (n : ℕ) (U : Fin n → X.Etale) (g : ∀ a, U a ⟶ W), (∀ a, R (g a)) ∧
      (∀ a, IsAffine (U a).left) ∧ ⋃ a, Set.range (g a).left = Set.univ := by
  obtain ⟨𝒰, h𝒰, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hR
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun j ↦ (𝒰.f j).isOpenMap
  obtain ⟨n, f, V, hV, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    𝒰.toPreZeroHypercover (U := ⊤) isCompact_univ
  refine ⟨n, fun a ↦ Etale.ofOpens ((𝒰.X (f a)).asOverProp _ (p (f a))) (V a),
    fun a ↦ Etale.ofOpensι _ _ ≫ (𝒰.f (f a)).asOverProp _,
    fun a ↦ R.downward_closed (hle _ _ (Presieve.ofArrows.mk (f a))) _, fun a ↦ hV a, ?_⟩
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hx : x ∈ ⋃ i, 𝒰.f (f i) '' (V i) := by rw [hcov]; trivial
  obtain ⟨a, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨a, ⟨y, hy⟩, rfl⟩

/-- A jointly surjective family of morphisms of étale `X`-schemes is a covering family for
every abelian étale sheaf. -/
lemma isSheafFor_ofArrows (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {W : X.Etale}
    {κ : Type*} {U : κ → X.Etale} (g : ∀ a, U a ⟶ W)
    (hg : ⋃ a, Set.range (g a).left = Set.univ) :
    Presieve.IsSheafFor (F.obj ⋙ CategoryTheory.forget _) (Presieve.ofArrows U g) := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (CategoryTheory.forget AddCommGrpCat) F.property)
  rw [Presieve.isSheafFor_iff_generate]
  exact this _ ((ofArrows_mem_smallEtaleTopology_iff g).2 hg)

/-- **Sections of a direct sum are locally finite sums.** Let `c` be a coproduct of a family
`F` of abelian étale sheaves on `X`. Every section of `c.pt` over `W` is, on the members of a
covering sieve of `W`, a finite sum of sections coming from the `Fᵢ`. -/
lemma exists_mem_forall_eq_sum_of_isColimit_cofan {ι : Type u}
    {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cofan F} (hc : IsColimit c)
    {W : X.Etale} (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (T : Finset ι) (a : ∀ i, (F i).obj.obj (op V)),
        c.pt.obj.map f.op s = ∑ i ∈ T, (c.inj i).hom.app (op V) (a i) := by
  let P := ∐ fun i ↦ (F i).obj
  let φ : P ⟶ c.pt.obj := Sigma.desc fun i ↦ (c.inj i).hom
  -- `φ` factors through the sheafification of `P` by an epimorphism of sheaves
  let ψ : (presheafToSheaf _ _).obj P ⟶ c.pt :=
    ⟨sheafifyLift X.smallEtaleTopology φ c.pt.property⟩
  have hφ : φ = toSheafify X.smallEtaleTopology P ≫ ψ.hom :=
    (toSheafify_sheafifyLift _ _ _).symm
  have hψ : Epi ψ := by
    refine ⟨fun {Z} g h hgh ↦ Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_⟩
    have e : c.inj i = (⟨Sigma.ι (fun i ↦ (F i).obj) i ≫ toSheafify _ P⟩ :
        F i ⟶ (presheafToSheaf _ _).obj P) ≫ ψ := by
      ext1
      change _ = Sigma.ι (fun i ↦ (F i).obj) i ≫ toSheafify _ P ≫ ψ.hom
      rw [← hφ, Sigma.ι_desc]
    rw [e, Category.assoc, Category.assoc, hgh]
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) ψ).2 hψ
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology φ := by
    rw [hφ]
    infer_instance
  refine ⟨_, Presheaf.imageSieve_mem _ φ s, fun V f ⟨p, hp⟩ ↦ ?_⟩
  have hP := isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj (op V)) _
    (Sigma.ι fun i ↦ (F i).obj) (coproductIsCoproduct _)
  obtain ⟨T, a, rfl⟩ := AddCommGrpCat.exists_eq_sum_of_isColimit_cofan hP p
  refine ⟨T, a, hp.symm.trans ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change (Sigma.ι (fun i ↦ (F i).obj) i ≫ φ).app (op V) (a i) = _
  rw [Sigma.ι_desc]

variable (X) in
/-- **`H¹` commutes with direct sums on a qcqs scheme.** Let `X` be quasi-compact and
quasi-separated and let `c` be a coproduct of a family `F` of abelian étale sheaves on `X`. If
`H¹(X, Fᵢ) = 0` for all `i`, then `H¹(X, c.pt) = 0`.

A global section `q` of the cokernel `Q` of an embedding `c.pt ⟶ E` lifts to sections `e_a` of
`E` on finitely many affine étale `X`-schemes `U_a` covering `X`. On the quasi-compact overlaps
`U_a ×_X U_b` the differences of the `e_a` are sections of `c.pt`, hence locally finite sums
(`AlgebraicGeometry.Scheme.exists_mem_forall_eq_sum_of_isColimit_cofan`), and finitely many
indices `S` suffice. So the `e_a` glue modulo the finite sum `G = ⨁_{i ∈ S} Fᵢ`, and the glued
section lifts to `E` since `H¹(G) = ⨁_{i ∈ S} H¹(Fᵢ) = 0`. This is the case of degree one of
[Stacks 03Q6]. -/
theorem subsingleton_H_one_of_isColimit_cofan [CompactSpace X] [QuasiSeparatedSpace X]
    {ι : Type u} {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cofan F}
    (hc : IsColimit c) (hF : ∀ i, Subsingleton (Sheaf.H (F i) 1)) :
    Subsingleton (Sheaf.H c.pt 1) := by
  classical
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  refine Sheaf.subsingleton_H_one_of_surjective _ hT fun E Q ι' π w hS q ↦ ?_
  have := hS.mono_f
  have (U : X.Etaleᵒᵖ) : PreservesLimits
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj U) :=
    inferInstanceAs (PreservesLimits (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U))
  have hexact (U) (x : E.obj.obj U) (hx : π.hom.app U x = 0) : ∃ g, ι'.hom.app U g = x :=
    (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj U) hS.mono_f
      inferInstance) x hx
  have := hS.epi_g
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) π).2 inferInstance
  -- Step 1: `q` lifts on finitely many affine étale `X`-schemes covering `X`
  have : CompactSpace T.left := ‹CompactSpace X›
  obtain ⟨n, U, g, hR, hU, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology
    (Presheaf.imageSieve_mem X.smallEtaleTopology π.hom (U := op T) q)
  choose e he using hR
  -- Step 2: the differences on the overlaps are sections of `c.pt`
  have hW (a b : Fin n) : CompactSpace (pullback (g a) (g b)).left := by
    let iso := PreservesPullback.iso (Etale.forget X ⋙ Over.forget X) (g a) (g b)
    have : IsAffine (U a).left := hU a
    have : IsAffine (U b).left := hU b
    have : QuasiCompact (g b).left :=
      @quasiCompact_of_compactSpace _ _ (g b).left inferInstance ‹QuasiSeparatedSpace X›
    have : CompactSpace ↥(Limits.pullback (C := Scheme.{u}) (g a).left (g b).left) :=
      inferInstance
    exact @Homeomorph.compactSpace _ _ _ _ this
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso iso).symm)
  have hd (a b : Fin n) : π.hom.app _ (E.obj.map (pullback.fst (g a) (g b)).op (e a) -
      E.obj.map (pullback.snd (g a) (g b)).op (e b)) = 0 := by
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, he, he,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition, sub_self]
  choose γ hγ using fun a b ↦ hexact _ _ (hd a b)
  -- Step 3: locally on the overlaps, these are finite sums
  have hfin (a b : Fin n) : ∃ (S : Finset ι) (m : ℕ) (V : Fin m → X.Etale)
      (h : ∀ k, V k ⟶ pullback (g a) (g b)), (⋃ k, Set.range (h k).left = Set.univ) ∧
      ∀ k, ∃ x : ∀ i, (F i).obj.obj (op (V k)),
        c.pt.obj.map (h k).op (γ a b) = ∑ i ∈ S, (c.inj i).hom.app _ (x i) := by
    obtain ⟨R, hR, hsum⟩ := exists_mem_forall_eq_sum_of_isColimit_cofan hc (γ a b)
    obtain ⟨m, V, h, hRh, -, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
    choose S x hx using fun k ↦ hsum (h k) (hRh k)
    refine ⟨Finset.univ.biUnion S, m, V, h, hcov, fun k ↦
      ⟨fun i ↦ if i ∈ S k then x k i else 0, ?_⟩⟩
    rw [hx k]
    symm
    rw [← Finset.sum_subset (Finset.subset_biUnion_of_mem S (Finset.mem_univ k))]
    · exact Finset.sum_congr rfl fun i hi ↦ by simp [hi]
    · intro i _ hi
      simp [hi]
  choose S m V h hVcov x hx using hfin
  -- Step 4: the finite sum `G = ⨁_{i ∈ S₀} Fᵢ` of all indices needed
  let S₀ : Finset ι := Finset.univ.biUnion fun ab : Fin n × Fin n ↦ S ab.1 ab.2
  have hS₀ (a b : Fin n) : S a b ⊆ S₀ :=
    Finset.subset_biUnion_of_mem (fun ab : Fin n × Fin n ↦ S ab.1 ab.2) (Finset.mem_univ (a, b))
  let F' : S₀ → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := fun i ↦ F i.1
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Abelian.hasFiniteBiproducts
  let j : ⨁ F' ⟶ c.pt := biproduct.desc fun i ↦ c.inj i.1
  have hj (i : ι) (hi : i ∈ S₀) : c.inj i = biproduct.ι F' ⟨i, hi⟩ ≫ j := by simp [j]
  have : Mono j := by
    let r : c.pt ⟶ ⨁ F' :=
      Cofan.IsColimit.desc hc fun i ↦ if hi : i ∈ S₀ then biproduct.ι F' ⟨i, hi⟩ else 0
    refine SplitMono.mono ⟨r, biproduct.hom_ext' _ _ fun i ↦ ?_⟩
    simp [j, r, Cofan.IsColimit.fac, i.2]
  have hG : Subsingleton (Sheaf.H (⨁ F') 1) :=
    have (i : S₀) : Subsingleton (Sheaf.H (F' i) 1) := hF i.1
    (Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit F') 1).toEquiv.subsingleton
  let ρ := cokernel.π (j ≫ ι')
  have hSρ : (ShortComplex.mk (j ≫ ι') ρ (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have hρ (i : ι) (hi : i ∈ S₀) (V : X.Etaleᵒᵖ) (y : (F i).obj.obj V) :
      ρ.hom.app V (ι'.hom.app V ((c.inj i).hom.app V y)) = 0 := by
    have : c.inj i ≫ ι' ≫ ρ = 0 := by
      rw [hj i hi, Category.assoc, ← Category.assoc j, cokernel.condition, comp_zero]
    exact congrArg (fun φ ↦ φ.hom.app V y) this
  -- Step 5: modulo `G` the lifts `e_a` glue
  have hzero (a b : Fin n) : ρ.hom.app _ (ι'.hom.app _ (γ a b)) = 0 := by
    refine (isSheafFor_ofArrows (cokernel (j ≫ ι')) (h a b) (hVcov a b)).isSeparatedFor.ext
      fun Z f ⟨k⟩ ↦ ?_
    change (cokernel (j ≫ ι')).obj.map _ _ = (cokernel (j ≫ ι')).obj.map _ 0
    rw [map_zero, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hx, map_sum,
      map_sum]
    exact Finset.sum_eq_zero fun i hi ↦ hρ i (hS₀ a b hi) _ _
  obtain ⟨y, hy, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).1
    (isSheafFor_ofArrows (cokernel (j ≫ ι')) g hcov)) (fun a ↦ ρ.hom.app _ (e a)) fun a b ↦ by
      change (cokernel (j ≫ ι')).obj.map _ _ = (cokernel (j ≫ ι')).obj.map _ _
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← sub_eq_zero, ← map_sub,
        ← hγ, hzero]
  -- Step 6: the glued section lifts to `E`, as `H¹(G) = 0`
  obtain ⟨x₀, hx₀⟩ : y ∈ (ρ.hom.app (op T)).hom.range := by
    rw [← Sheaf.H.ker_δ hSρ hT]
    exact Subsingleton.elim (h := hG) _ _
  refine ⟨x₀, ?_⟩
  -- Step 7: and the lift maps to `q`
  let τ : cokernel (j ≫ ι') ⟶ Q := cokernel.desc _ π (by simp [w])
  have hτ : ρ ≫ τ = π := cokernel.π_desc _ _ _
  refine (isSheafFor_ofArrows Q g hcov).isSeparatedFor.ext fun Z f ⟨a⟩ ↦ ?_
  have hτx : π.hom.app _ x₀ = τ.hom.app _ y := by
    rw [← hx₀, ← hτ]
    rfl
  change Q.obj.map _ (π.hom.app _ x₀) = Q.obj.map _ _
  rw [hτx, ← NatTrans.naturality_apply]
  erw [hy a]
  rw [← he, ← hτ]
  rfl

/-- **Étale cohomology commutes with direct sums on a qcqs scheme.** Let `X` be quasi-compact
and quasi-separated and let `c` be a coproduct of a family `F` of abelian étale sheaves on `X`.
If `Hⁿ(X, Fᵢ) = 0` for all `i`, then `Hⁿ(X, c.pt) = 0`. This is the special case of direct
sums of the commutation of étale cohomology with filtered colimits on qcqs schemes,
[Stacks 03Q6]. The proof is `sorry`; the case `n = 1` is
`AlgebraicGeometry.Scheme.subsingleton_H_one_of_isColimit_cofan`. -/
@[stacks 03Q6]
theorem subsingleton_H_of_isColimit_cofan (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {ι : Type u} {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cofan F} (hc : IsColimit c) (n : ℕ) (hF : ∀ i, Subsingleton (Sheaf.H (F i) n)) :
    Subsingleton (Sheaf.H c.pt n) :=
  sorry

end AlgebraicGeometry.Scheme
