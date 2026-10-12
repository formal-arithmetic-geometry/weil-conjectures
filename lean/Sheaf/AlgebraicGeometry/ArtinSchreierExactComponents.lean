module

public import Sheaf.AlgebraicGeometry.ArtinSchreierData
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
import Sheaf.AlgebraicGeometry.ArtinSchreierKernelSections

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false

private theorem kernelFork_isLimit_of_sections
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {F G H : Sheaf J AddCommGrpCat.{u + 1}} (i : F ⟶ G) (w : G ⟶ H)
    (hz : i ≫ w = 0)
    (hinj : ∀ U, Function.Injective (i.hom.app U))
    (hlift : ∀ U (x : G.obj.obj U), w.hom.app U x = 0 →
      ∃ y, i.hom.app U y = x) :
    Nonempty (IsLimit (KernelFork.ofι i hz)) := by
  classical
  have kills : ∀ {K : Sheaf J AddCommGrpCat.{u + 1}} (j : K ⟶ G)
      (hj : j ≫ w = 0) U (x : K.obj.obj U), w.hom.app U (j.hom.app U x) = 0 := by
    intro K j hj U x
    change (j ≫ w).hom.app U x = 0
    rw [hj]
    rfl
  let pre := fun {K : Sheaf J AddCommGrpCat.{u + 1}} (j : K ⟶ G) (hj : j ≫ w = 0)
    U (x : K.obj.obj U) ↦ (hlift U (j.hom.app U x) (kills j hj U x)).choose
  have pre_spec : ∀ {K : Sheaf J AddCommGrpCat.{u + 1}} (j : K ⟶ G)
      (hj : j ≫ w = 0) U (x : K.obj.obj U), i.hom.app U (pre j hj U x) = j.hom.app U x :=
    fun j hj U x ↦ (hlift U (j.hom.app U x) (kills j hj U x)).choose_spec
  let lift : ∀ {K : Sheaf J AddCommGrpCat.{u + 1}} (j : K ⟶ G),
      j ≫ w = 0 → (K ⟶ F) := fun {K} j hj ↦
    ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := pre j hj U
          map_zero' := by
            apply hinj U
            rw [pre_spec j hj, map_zero, map_zero]
          map_add' := by
            intro x y
            apply hinj U
            rw [map_add, pre_spec j hj, pre_spec j hj, pre_spec j hj, map_add] }
       naturality := by
         intro U V g
         ext x
         symm
         apply hinj V
         change i.hom.app V (F.obj.map g (pre j hj U x)) =
           i.hom.app V (pre j hj V (K.obj.map g x))
         rw [NatTrans.naturality_apply i.hom g, pre_spec j hj, pre_spec j hj]
         exact (NatTrans.naturality_apply j.hom g x).symm }⟩
  have fac : ∀ {K : Sheaf J AddCommGrpCat.{u + 1}} (j : K ⟶ G) (hj : j ≫ w = 0),
      lift j hj ≫ i = j := by
    intro K j hj
    ext U x
    exact pre_spec j hj U x
  refine ⟨KernelFork.IsLimit.ofι i hz lift fac ?_⟩
  intro K j hj m hm
  ext U x
  apply hinj U
  change (m ≫ i).hom.app U x = i.hom.app U (pre j hj U x)
  rw [hm, pre_spec j hj]

private theorem exists_etale_surjective_artinSchreier_eq
    {k : Type u} [Field k] {U : Scheme.{u}} (f : U ⟶ Spec (.of k))
    (p : ℕ) [CharP k p] (hp : p.Prime) (x : Γ(U, ⊤)) :
    ∃ (V : Scheme.{u}) (g : V ⟶ U), Etale g ∧ Surjective g ∧
      ∃ y : Γ(V, ⊤), y ^ p - y = g.appTop x := by
  let : Fact p.Prime := ⟨hp⟩
  let z := ULift.{u} (ZMod p)
  let ψ : z →+* Γ(U, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).comp
      ((ZMod.castHom (dvd_refl p) k).comp ULift.ringEquiv.toRingHom)
  let t : U ⟶ Spec (.of z) := U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have hcard : Fintype.card z = p := by
    rw [Fintype.card_ulift, ZMod.card]
  have hsurj : Surjective (AffineSpace.artinSchreierMap PUnit (Spec (.of z)) p) := by
    have h : Surjective
        (AffineSpace.artinSchreierMap PUnit (Spec (.of z)) (Fintype.card z)) :=
      ⟨AffineSpace.surjective_artinSchreierMap z⟩
    simpa only [hcard] using h
  have hsurjU : Surjective (AffineSpace.artinSchreierMap PUnit U p) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map_artinSchreierMap t p) hsurj
  have hchar : (p : Γ(U, ⊤)) = 0 := by
    rw [← map_natCast ψ, CharP.cast_eq_zero z p, map_zero]
  let AS := AffineSpace.artinSchreierMap PUnit U p
  have : Etale AS := AffineSpace.etale_artinSchreierMap PUnit U hchar
  have : Surjective AS := hsurjU
  let v := AffineSpace.homOfVector (𝟙 U) (fun _ : PUnit ↦ x)
  let g := pullback.snd AS v
  refine ⟨pullback AS v, g, inferInstance, inferInstance,
    (pullback.fst AS v).appTop (AffineSpace.coord U PUnit.unit), ?_⟩
  have h := congrArg (fun m : pullback AS v ⟶ 𝔸(PUnit; U) ↦
    m.appTop (AffineSpace.coord U PUnit.unit)) (pullback.condition (f := AS) (g := v))
  simpa [AS, v, g, Scheme.Hom.comp_appTop, AffineSpace.artinSchreierMap_appTop_coord,
    AffineSpace.homOfVector_appTop_coord, map_sub, map_pow] using h

/-- The kernel, exactness, and epimorphism components of the Artin--Schreier sequence.
Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md.
For every etale section, the equation `x ^ p - x = 0` has precisely the constant
solutions coming from `ZMod p`; this identifies the kernel with the image of
`iota` and gives exactness. The Artin--Schreier polynomial is surjective on
the algebraically closed residue fields, and the section restriction formula
then lifts this to epimorphy of `wp`. The same constant-section calculation
shows that `iota` is monic. These three conclusions are returned as the
conjunction below. (blueprint: lem-sc-as-sequence-exact-components)
-/
theorem artinSchreier_data_exact_components
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : G ≅ (sheafCompose C.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G) (iota : C.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0)
    (hrestr : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x)
    (hiota : ∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
      a U (iota.hom.app U
        ((toSheafify C.smallEtaleTopology
          ((Functor.const C.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤))) :
    (ShortComplex.mk iota wp hzero).Exact ∧
      Mono iota ∧ Epi wp := by
  have _representation_hom := hG.hom
  have hprime : p.Prime := CharP.char_prime_of_ne_zero (R := k) (Nat.ne_of_gt hp)
  have hk := artinSchreier_kernel_sections f p hprime G a iota hrestr hiota
  obtain ⟨hkernel⟩ := kernelFork_isLimit_of_sections C.smallEtaleTopology iota wp hzero
    (fun U ↦ (hk U).1) (fun U x hx ↦ (hk U).2 x (by
      have h := hwp U x
      rw [hx, map_zero] at h
      exact sub_eq_zero.mp h.symm))
  have hlocal : Sheaf.IsLocallySurjective wp := by
    constructor
    intro U x
    obtain ⟨V, g, hg, hsurj, y, hy⟩ := exists_etale_surjective_artinSchreier_eq
      (U.hom ≫ f) p hprime (a (Opposite.op U) x)
    have : Etale (g ≫ U.hom) := by have := U.prop; infer_instance
    let r : MorphismProperty.Over.mk ⊤ (g ≫ U.hom) this ⟶ U :=
      MorphismProperty.Over.homMk g rfl
    refine GrothendieckTopology.superset_covering _ ?_
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit ↦ r)).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      refine ⟨(a (Opposite.op (MorphismProperty.Over.mk ⊤ (g ≫ U.hom) this))).symm y, ?_⟩
      apply (a _).injective
      rw [hwp, AddEquiv.apply_symm_apply, hrestr]
      exact hy
    · simp only [Set.iUnion_const]
      exact Set.range_eq_univ.mpr hsurj.surj
  let : Sheaf.IsLocallySurjective wp := hlocal
  exact ⟨ShortComplex.exact_of_f_is_kernel _ hkernel,
    mono_of_isLimit_fork hkernel, Sheaf.epi_of_isLocallySurjective wp⟩

end AlgebraicGeometry
