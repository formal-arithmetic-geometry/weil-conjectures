module

public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import Mathlib.RingTheory.Smooth.Local
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier

@[expose] public section

/-!
# Nonzero relative differential gives a smooth hypersurface point

Source: Stacks Project, Algebra, Tag 00T7.
(blueprint: lem-zl-hypersurface-nonzero-relative-differential).
-/

open CategoryTheory Limits Opposite TopologicalSpace PresheafOfModules
open AlgebraicGeometry
open scoped AlgebraicGeometry Scheme.Modules

universe u

open scoped TensorProduct in
private theorem formallySmooth_of_principal_kernel
    {R P C K : Type u} [CommRing R] [CommRing P] [CommRing C] [Field K]
    [IsLocalRing C] [Algebra R P] [Algebra R C] [Algebra P C]
    [IsScalarTower R P C] [Algebra C K] [Algebra P K] [IsScalarTower P C K]
    [Algebra.FormallySmooth R P] [Module.Free P (KaehlerDifferential R P)]
    [Module.Finite P (KaehlerDifferential R P)]
    (hf : Function.Surjective (algebraMap P C)) (a : P)
    (hker : RingHom.ker (algebraMap P C) = Ideal.span {a})
    (hm : IsLocalRing.maximalIdeal C ≤ RingHom.ker (algebraMap C K))
    (hda : (1 ⊗ₜ[P] KaehlerDifferential.D R P a :
      K ⊗[P] KaehlerDifferential R P) ≠ 0) : Algebra.FormallySmooth R C := by
  classical
  have ha : a ∈ RingHom.ker (algebraMap P C) := by
    rw [hker]
    exact Ideal.mem_span_singleton_self a
  have hfg : (RingHom.ker (algebraMap P C)).FG := by
    rw [hker]
    exact Submodule.fg_span_singleton a
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange P K hf hfg hm]
  let g : K ⊗[P] RingHom.ker (algebraMap P C) := 1 ⊗ₜ[P] ⟨a, ha⟩
  have hg (t : K ⊗[P] RingHom.ker (algebraMap P C)) : ∃ c : K, t = c • g := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (zero_smul _ _).symm⟩
    | add x y hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, (add_smul _ _ _).symm⟩
    | tmul c x =>
      have hxmem : x.val ∈ Ideal.span {a} := by
        rw [← hker]
        exact x.property
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hxmem
      have hx : x = b • (⟨a, ha⟩ : RingHom.ker (algebraMap P C)) :=
        Subtype.ext hb.symm
      refine ⟨c * algebraMap P K b, ?_⟩
      rw [hx, TensorProduct.tmul_smul, ← algebraMap_smul K b]
      simp only [g, TensorProduct.smul_tmul', smul_eq_mul, one_mul, mul_comm]
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  obtain ⟨c, rfl⟩ := hg t
  rw [map_smul] at ht
  have hgen : KaehlerDifferential.cotangentComplexBaseChange R C P K g =
      1 ⊗ₜ[P] KaehlerDifferential.D R P a := by
    simp only [g, KaehlerDifferential.cotangentComplexBaseChange_tmul, one_smul,
      KaehlerDifferential.kerToTensor_apply]
  rw [hgen] at ht
  rw [(smul_eq_zero.mp ht).resolve_right hda, zero_smul]

namespace AlgebraicGeometry
namespace Scheme.Hom


set_option backward.isDefEq.respectTransparency true in
private theorem exists_stalk_derivation
    {X S : Scheme.{u}} (p : X ⟶ S) (x : X) {Ω : X.Modules}
    (D : Ω.val.Derivation' p.pullbackPresheafToPresheaf)
    (N : Type u) [AddCommGroup N] [Module (X.presheaf.stalk x) N]
    (ℓ : Ω.presheaf.stalk x →ₗ[X.presheaf.stalk x] N) :
    ∃ d : X.presheaf.stalk x →+ N,
      (∀ b c, d (b * c) = b • d c + c • d b) ∧
      (∀ r : S.presheaf.stalk (p x), d (p.stalkMap x r) = 0) ∧
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)),
        d (X.presheaf.germ U x hx a) =
          ℓ (Ω.presheaf.germ U x hx
            (D.d (X := op U) a)) := by
  classical
  let v (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) : N :=
    ℓ (Ω.presheaf.germ U x hx
      (D.d (X := op U) a))
  have hres {U V : X.Opens} (i : V ⟶ U) (hx : x ∈ V) (a : Γ(X, U)) :
      v V hx (X.presheaf.map i.op a) = v U (i.le hx) a := by
    dsimp only [v]
    erw [D.d_map i.op a]
    exact congrArg ℓ (Ω.presheaf.germ_res_apply i x hx _)
  have hcompat {U V : X.Opens} (hx : x ∈ U) (hy : x ∈ V)
      (a : Γ(X, U)) (b : Γ(X, V))
      (h : X.presheaf.germ U x hx a = X.presheaf.germ V x hy b) :
      v U hx a = v V hy b := by
    obtain ⟨W, hw, i, j, he⟩ := X.presheaf.germ_eq x hx hy a b h
    rw [← hres i hw a, ← hres j hw b, he]
  choose U hx a ha using fun b : X.presheaf.stalk x ↦ X.presheaf.exists_germ_eq b
  let d (b : X.presheaf.stalk x) := v (U b) (hx b) (a b)
  have hd (V : X.Opens) (hy : x ∈ V) (b : Γ(X, V)) :
      d (X.presheaf.germ V x hy b) = v V hy b :=
    hcompat _ _ _ _ (ha _)
  have hadd (b c : X.presheaf.stalk x) : d (b + c) = d b + d c := by
    obtain ⟨V, hy, b, rfl⟩ := X.presheaf.exists_germ_eq b
    obtain ⟨W, hz, c, rfl⟩ := X.presheaf.exists_germ_eq c
    have hVW : x ∈ V ⊓ W := ⟨hy, hz⟩
    let i : V ⊓ W ⟶ V := homOfLE inf_le_left
    let j : V ⊓ W ⟶ W := homOfLE inf_le_right
    rw [← X.presheaf.germ_res_apply i x hVW b,
      ← X.presheaf.germ_res_apply j x hVW c, ← map_add, hd, hd, hd]
    dsimp only [v]
    erw [map_add, map_add, map_add]
  have hmul (b c : X.presheaf.stalk x) : d (b * c) = b • d c + c • d b := by
    obtain ⟨V, hy, b, rfl⟩ := X.presheaf.exists_germ_eq b
    obtain ⟨W, hz, c, rfl⟩ := X.presheaf.exists_germ_eq c
    have hVW : x ∈ V ⊓ W := ⟨hy, hz⟩
    let i : V ⊓ W ⟶ V := homOfLE inf_le_left
    let j : V ⊓ W ⟶ W := homOfLE inf_le_right
    rw [← X.presheaf.germ_res_apply i x hVW b,
      ← X.presheaf.germ_res_apply j x hVW c, ← map_mul, hd, hd, hd]
    dsimp only [v]
    erw [D.d_mul, map_add, map_add,
      Scheme.Modules.germ_smul, Scheme.Modules.germ_smul]
    exact congrArg₂ (· + ·) (ℓ.map_smul _ _) (ℓ.map_smul _ _)
  refine ⟨AddMonoidHom.mk' d hadd, hmul, ?_, hd⟩
  intro r
  obtain ⟨V, hy, r, rfl⟩ := S.presheaf.exists_germ_eq r
  rw [Scheme.Hom.germ_stalkMap_apply, AddMonoidHom.mk'_apply]
  erw [hd]
  dsimp only [v]
  erw [PresheafOfModules.Derivation'.d_app_app D V r,
    map_zero, map_zero]

/-- The value at `z` of the relative differential of a local equation `a`, rendered as
`d a (z) ⊗ 1` in `Ω¹_{X/S,z} ⊗_{𝒪_{X,z}} κ(z)` is nonzero.

Source: Stacks Project, Morphisms, Tag 01UM (universal relative derivation), and
Algebra, Tag 00T7 (the differential basis on a standard smooth chart).
(blueprint: lem-zl-hypersurface-nonzero-relative-differential). -/
noncomputable def relativeDifferentialValue {X S : Scheme.{u}} (p : X ⟶ S)
    (U : X.Opens) (z : X) (hz : z ∈ U) (a : Γ(X, U)) : Prop := by
  letI : Module (X.presheaf.stalk z) (X.residueField z) :=
    Module.compHom (X.residueField z) (X.residue z).hom
  let v := TensorProduct.tmul (X.presheaf.stalk z)
    (TopCat.Presheaf.germ (p.relativeDifferentials.val.presheaf) U z hz
      ((p.relativeDifferentialsDerivation.app (op U)).toFun a)) (1 : X.residueField z)
  exact v ≠ 0

set_option backward.isDefEq.respectTransparency true in
/-- **Nonzero relative differential gives a smooth hypersurface point.**

Source: Stacks Project, Algebra, Tag 00T7, applied to a standard smooth chart after adjoining
one equation with a nonzero Jacobian row.
(blueprint: lem-zl-hypersurface-nonzero-relative-differential).
Proof: work on the stalks `R = 𝒪_{S,p(x)}`, `P = 𝒪_{X,x}`, and `C = 𝒪_{Z,z}`.
The kernel of the surjection `P → C` is generated by the germ of `a`, using the
zero scheme's equation on a trivializing affine neighbourhood. A linear functional on
`κ(x) ⊗ Ω¹_{X/S,x}` detects the nonzero differential. Composing it with the sheaf's
universal derivation and passing to germs gives an `R`-derivation `P → κ(x)` detecting
`a`; extend it to `κ(z)`. The universal property of algebraic Kähler differentials
therefore makes `da` nonzero in `κ(z) ⊗[P] Ω[P/R]`.

The ambient smoothness makes `P` formally smooth over `R`, with finite free Kähler
module (finite projective over the local ring `P`). The tensor of the kernel `(a)`
with `κ(z)` is generated by `1 ⊗ a`, whose image under the cotangent map is nonzero.
That map is consequently injective. Mathlib's local cotangent criterion gives formal
smoothness of `C` over `R`. The zero scheme is locally of finite presentation over
the base, since its ideal is locally principal. The open smooth locus of `Z → S`
contains `z` and supplies the required neighbourhood. No flatness of `Z → S` is assumed.
-/
theorem smooth_zeroLocus_of_relativeDifferentialValue
    {X S : Scheme.{u}} (p : X ⟶ S) [Smooth p] (M : X.Modules) [M.IsInvertible]
    (s : M.sections)
    (z : (Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subscheme)
    (U : X.Opens) (hz : (Scheme.Modules.Hom.zeroLocus
      (M.unitHomEquiv.symm s)).subschemeι z ∈ U)
    (e : Γ(M, U)) (he : Scheme.Modules.IsFreeGenerator e) (a : Γ(X, U))
    (ha : ((M.unitHomEquiv.symm s).val.app (op U)) (1 : Γ(X, U)) = a • e)
    (hda : relativeDifferentialValue p U
      ((Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subschemeι z) hz a) :
    ∃ V : (Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subscheme.Opens,
      z ∈ V ∧ Smooth (V.ι ≫
        (Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subschemeι ≫ p) := by
  classical
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
    @Scheme.Modules.IsInvertible.sheafOfModules_isInvertible X _
      Scheme.Modules.isInvertible_tensorUnit
  let φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M :=
    M.unitHomEquiv.symm s
  let I := Scheme.Modules.Hom.zeroLocus φ
  let i := I.subschemeι
  let x := i z
  let P : Type u := X.presheaf.stalk x
  let R : Type u := S.presheaf.stalk (p x)
  let C : Type u := I.subscheme.presheaf.stalk z
  let F : Type u := X.residueField x
  let K : Type u := I.subscheme.residueField z
  let : Algebra R P := (p.stalkMap x).hom.toAlgebra
  let : Algebra P C := (i.stalkMap z).hom.toAlgebra
  let : Algebra R C := Algebra.compHom C (algebraMap R P)
  have : IsScalarTower R P C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra P F := (X.residue x).hom.toAlgebra
  let : Algebra R F := Algebra.compHom F (algebraMap R P)
  have : IsScalarTower R P F := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra C K := (I.subscheme.residue z).hom.toAlgebra
  let : Algebra P K := Algebra.compHom K (algebraMap P C)
  have : IsScalarTower P C K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R K := Algebra.compHom K (algebraMap R P)
  have : IsScalarTower R P K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra F K := (i.residueFieldMap z).hom.toAlgebra
  have : IsScalarTower P F K := IsScalarTower.of_algebraMap_eq' (by
    change (i.stalkMap z ≫ I.subscheme.residue z).hom =
      (X.residue x ≫ i.residueFieldMap z).hom
    rw [Scheme.residue_residueFieldMap i z])
  let m := p.relativeDifferentials.presheaf.germ U x hz
    (p.relativeDifferentialsDerivation.d (X := op U) a)
  have hm : (TensorProduct.tmul P (1 : F) m :
      TensorProduct P F (p.relativeDifferentials.presheaf.stalk x)) ≠ 0 := by
    intro h
    apply hda
    have h' := congrArg (TensorProduct.comm P F (p.relativeDifferentials.presheaf.stalk x)) h
    change TensorProduct.tmul P m (1 : F) = 0
    simpa only [TensorProduct.comm_tmul, map_zero] using h'
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_ne_zero F hm
  let ℓ : p.relativeDifferentials.presheaf.stalk x →ₗ[P] F :=
    L.restrictScalars P ∘ₗ TensorProduct.mk P F _ 1
  obtain ⟨d, hmul, hbase, hd⟩ := exists_stalk_derivation p x p.relativeDifferentialsDerivation F ℓ
  let D : Derivation R P F := Derivation.mk'
    { __ := d
      map_smul' r b := by
        change d (algebraMap R P r * b) = r • d b
        rw [hmul, show d (algebraMap R P r) = 0 from hbase r,
          smul_zero, add_zero]
        rfl }
    hmul
  let ρ : F →ₐ[P] K := IsScalarTower.toAlgHom P F K
  let D' : Derivation R P K := ρ.toLinearMap.compDer D
  have hD : D' (X.presheaf.germ U x hz a) ≠ 0 := by
    change ρ (d (X.presheaf.germ U x hz a)) ≠ 0
    rw [hd]
    exact fun h ↦ hL (ρ.injective (h.trans (map_zero ρ).symm))
  have hda' : (TensorProduct.tmul P (1 : K)
      (KaehlerDifferential.D R P (X.presheaf.germ U x hz a)) :
      TensorProduct P K (KaehlerDifferential R P)) ≠ 0 := by
    intro h
    have h' := congrArg (D'.liftKaehlerDifferential.liftBaseChange K) h
    exact hD (by simpa using h')
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz U.isOpen
  have haW := Scheme.Modules.Hom.app_presheaf_map_of_eq φ (homOfLE hWU) ha
  have hideal : I.ideal ⟨W, hW⟩ =
      Ideal.span {X.presheaf.map (homOfLE hWU).op a} := by
    apply Scheme.Modules.Hom.ideal_zeroLocus φ ⟨W, hW⟩
      (Scheme.Modules.isFreeGenerator_one W) (he.map hWU)
    change (φ.val.app (op W))
      (X.presheaf.map (homOfLE (show W ≤ U from hWU)).op (1 : Γ(X, U))) = _ at haW
    rw [map_one] at haW
    exact haW
  have hker : RingHom.ker (algebraMap P C) =
      Ideal.span {X.presheaf.germ U x hz a} := by
    rw [show RingHom.ker (algebraMap P C) = RingHom.ker (i.stalkMap z).hom from rfl,
      i.ker_stalkMap ⟨W, hW⟩ z hxW, Scheme.IdealSheafData.ker_subschemeι, hideal,
      Ideal.map_span, Set.image_singleton]
    exact congrArg (fun b : P ↦ Ideal.span {b})
      (X.presheaf.germ_res_apply (homOfLE (show W ≤ U from hWU)) x hxW a)
  have : Algebra.FormallySmooth R P := by
    have hx : x ∈ p.smoothLocus := p.smoothLocus_eq_top.symm ▸ Set.mem_univ x
    exact hx
  have : Algebra.EssFiniteType R P := LocallyOfFiniteType.stalkMap p x
  have : Module.Free P (KaehlerDifferential R P) := Module.free_of_flat_of_isLocalRing
  have hsm : Algebra.FormallySmooth R C :=
    formallySmooth_of_principal_kernel (i.stalkMap_surjective z)
      (X.presheaf.germ U x hz a) hker
      (by
        change IsLocalRing.maximalIdeal C ≤ RingHom.ker (IsLocalRing.residue C)
        rw [IsLocalRing.ker_residue]) hda'
  have : LocallyOfFinitePresentation (i ≫ p) :=
    Scheme.IdealSheafData.IsLocallyPrincipal.locallyOfFinitePresentation_subschemeι_comp p
      (Scheme.Modules.Hom.isLocallyPrincipal_zeroLocus φ)
  have hzsm : z ∈ (i ≫ p).smoothLocus := by
    change ((i ≫ p).stalkMap z).hom.FormallySmooth
    rw [Scheme.Hom.stalkMap_comp]
    exact hsm
  refine ⟨(i ≫ p).smoothLocus, hzsm, ?_⟩
  change Smooth ((i ≫ p).smoothLocus.ι ≫ (i ≫ p))
  rw [← Scheme.Hom.smoothLocus_eq_top_iff,
    ← Scheme.Hom.preimage_smoothLocus_eq ((i ≫ p).smoothLocus.ι) (i ≫ p),
    Scheme.Opens.ι_preimage_self]

end Scheme.Hom
end AlgebraicGeometry
