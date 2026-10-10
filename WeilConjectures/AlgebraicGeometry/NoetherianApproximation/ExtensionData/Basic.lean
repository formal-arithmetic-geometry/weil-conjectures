/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Basic
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# The data of the induction step of absolute Noetherian approximation

The data of one induction step of absolute Noetherian approximation (Stacks Project Tag 07RN)
is bundled into `AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData`. This file
defines it, together with the category of *stages*
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData.Stage`, and shows that `Wⱼ`
is an open of the spectrum of the coefficient algebra of a stage
(`Stage.isOpenImmersion_toSpec`, Tags 01Z7 and 01Z9).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
namespace Scheme.NoetherianApproximation

/-!
### The induction step of absolute Noetherian approximation

Following the proof of Stacks Project Tag 07RN, we extend a Noetherian approximation of a
quasi-compact open `U` of a quasi-separated scheme `X` to a Noetherian approximation of
`U ∪ V` for an affine open `V`. The extension is built from *stages*: a stage consists of an
index `j` of (the restriction to a coslice of) the approximation of `U`, a lift `r` of the
generators of `W = U ⊓ V` to sections at the stage `j`, and a finitely generated
`ℤ`-subalgebra `A` of `Γ(X, V) × Γ(Wⱼ, ⊤)` — an algebraic incarnation of the fiber product
`Γ(V) ×_{Γ(W)} Γ(Wⱼ)` of Stacks 07RN. The scheme attached to a stage is the pushout of
`Dⱼ ⟵ Wⱼ ⟶ Spec A` along open immersions.
-/

/-- (Implementation) The setup for the induction step of absolute Noetherian approximation
(Stacks Project Tag 07RN): a quasi-separated scheme `X` covered by a quasi-compact open `U`
carrying a Noetherian approximation `N` and an affine open `V`; the intersection `U ⊓ V`
is descended to a quasi-compact open `W₀` at a stage `i₀` of `N`, and is exhibited as a
finite union of basic opens of sections `b l` of `V`. -/
structure ExtensionData where
  /-- The ambient scheme. -/
  X : Scheme.{u}
  /-- The ambient scheme is quasi-separated. -/
  [qs : QuasiSeparatedSpace X]
  /-- The already approximated quasi-compact open. -/
  U : X.Opens
  /-- The new affine open. -/
  V : X.Opens
  /-- The two opens cover the ambient scheme. -/
  hUV : U ⊔ V = ⊤
  /-- The new open is affine. -/
  hV : IsAffineOpen V
  /-- A Noetherian approximation of `U`. -/
  N : U.toScheme.NoetherianApproximation
  /-- The stage of `N` at which `U ⊓ V` is descended. -/
  i₀ : N.I
  /-- The descended intersection. -/
  W₀ : (N.D.obj i₀).Opens
  /-- The descended intersection is quasi-compact. -/
  hW₀c : IsCompact (W₀ : Set (N.D.obj i₀))
  /-- The descended intersection pulls back to `U ⊓ V`. -/
  hW₀ : N.π.app i₀ ⁻¹ᵁ W₀ = U.ι ⁻¹ᵁ V
  /-- The number of chosen generators of the intersection. -/
  n : ℕ
  /-- The chosen generators of the intersection: sections of `V` whose basic opens
  cover `U ⊓ V`. -/
  b : Fin n → Γ(X, V)
  /-- Each chosen generator has its basic open inside the intersection. -/
  hb (l : Fin n) : X.basicOpen (b l) ≤ U ⊓ V
  /-- The basic opens of the chosen generators cover the intersection. -/
  hb' : U ⊓ V = ⨆ l, X.basicOpen (b l)

namespace ExtensionData

attribute [instance] qs

variable (E : ExtensionData.{u})

/-- (Implementation) The limit cone of the approximation of `U`. -/
abbrev cone : Cone E.N.D := Cone.mk _ E.N.π

/-- (Implementation) `W = U ⊓ V` as an open of `U`. -/
abbrev WU : E.U.toScheme.Opens := E.N.π.app E.i₀ ⁻¹ᵁ E.W₀

/-- (Implementation) The system of the descended intersections `Wⱼ`. -/
noncomputable abbrev WD : Over E.i₀ ⥤ Scheme.{u} := opensDiagram E.N.D E.i₀ E.W₀

/-- (Implementation) The cone exhibiting `W` as the limit of the `Wⱼ`. -/
noncomputable abbrev Wc : Cone E.WD := opensCone E.N.D E.cone E.i₀ E.W₀

/-- (Implementation) `W` is the limit of the `Wⱼ`. -/
noncomputable def isLimitWc : IsLimit E.Wc :=
  isLimitOpensCone E.N.D E.cone E.N.isLimit E.i₀ E.W₀

instance (j : Over E.i₀) : CompactSpace (E.WD.obj j) :=
  isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := E.N.D.map j.hom) _ E.W₀.2 E.hW₀c)

instance (j : Over E.i₀) : IsLocallyNoetherian (E.WD.obj j) := by
  have : IsLocallyNoetherian (E.N.D.obj j.left) := (E.N.isNoetherian_obj j.left).1
  exact isLocallyNoetherian_of_isOpenImmersion (Scheme.Opens.ι _)

/-- (Implementation) The restriction of a section of `V` to `W`, viewed inside the limit of
the `Wⱼ`. -/
noncomputable def sV : Γ(E.X, E.V) ⟶ Γ(E.Wc.pt, ⊤) :=
  (E.WU.ι ≫ E.U.ι).appLE E.V ⊤ (by
    rw [Scheme.Hom.comp_preimage, ← E.hW₀, Scheme.Opens.ι_preimage_self])

/-- (Implementation) The restriction of a section at the stage `j` to the limit `W`. -/
noncomputable abbrev t (j : Over E.i₀) : Γ(E.WD.obj j, ⊤) ⟶ Γ(E.Wc.pt, ⊤) :=
  (E.Wc.π.app j).appTop

/-- (Implementation) The transition map on sections of the system `Wⱼ`. -/
noncomputable abbrev res {j j' : Over E.i₀} (f : j' ⟶ j) :
    Γ(E.WD.obj j, ⊤) ⟶ Γ(E.WD.obj j', ⊤) :=
  (E.WD.map f).appTop

lemma t_res {j j' : Over E.i₀} (f : j' ⟶ j) (x : Γ(E.WD.obj j, ⊤)) :
    E.t j' (E.res f x) = E.t j x := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, E.Wc.w f]

lemma res_res {j j' j'' : Over E.i₀} (f : j' ⟶ j) (g : j'' ⟶ j') (x : Γ(E.WD.obj j, ⊤)) :
    E.res g (E.res f x) = E.res (g ≫ f) x := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp]

/-- (Implementation) A stage of the extended system: an index `j`, a lift `r` of the
generators of `W` to `Wⱼ` such that the basic opens of the `r l` form an affine cover of
`Wⱼ`, and a finitely generated `ℤ`-subalgebra `A` of `Γ(X, V) × Γ(Wⱼ, ⊤)` contained in the
fiber product over `Γ(W, ⊤)`, containing the tautological elements `(b l, r l)` and
generating all the local rings of the cover (condition `hgen`, ensuring that `Wⱼ ⟶ Spec A`
is an open immersion). -/
structure Stage where
  /-- The underlying index. -/
  j : Over E.i₀
  /-- The lifts of the generators of the intersection. -/
  r : Fin E.n → Γ(E.WD.obj j, ⊤)
  hr (l : Fin E.n) : E.t j (r l) = E.sV (E.b l)
  hcov : ⨆ l, (E.WD.obj j).basicOpen (r l) = ⊤
  haff (l : Fin E.n) : IsAffineOpen ((E.WD.obj j).basicOpen (r l))
  /-- The finite-stage coefficient algebra. -/
  A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤))
  hA : ∀ p ∈ A, E.sV p.1 = E.t j p.2
  hAfg : A.FG
  hmem (l : Fin E.n) : (E.b l, r l) ∈ A
  hgen (l : Fin E.n) (z : Γ(E.WD.obj j, (E.WD.obj j).basicOpen (r l))) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)), p ∈ A ∧
      ((E.WD.obj j).presheaf.map (homOfLE le_top).op).hom p.2 =
        z * ((E.WD.obj j).presheaf.map (homOfLE le_top).op).hom (r l) ^ m

/-- (Implementation) A morphism of stages over a morphism of underlying indices: the lifts
`r` are compatible, and the coefficient algebra of the target maps into that of the
source. -/
@[ext] structure Stage.Hom (T T' : E.Stage) where
  /-- The underlying index morphism. -/
  base : T.j ⟶ T'.j
  res_r (l : Fin E.n) : E.res base (T'.r l) = T.r l
  map_mem (p : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)) (hp : p ∈ T'.A) :
    (p.1, E.res base p.2) ∈ T.A

lemma res_id (j : Over E.i₀) (x : Γ(E.WD.obj j, ⊤)) : E.res (𝟙 j) x = x := by
  change ((E.WD.map (𝟙 j)).appTop).hom x = x
  rw [CategoryTheory.Functor.map_id]
  simp

instance : Category E.Stage where
  Hom := Stage.Hom E
  id T := ⟨𝟙 T.j, fun l ↦ E.res_id _ _, fun p hp ↦ by simpa [E.res_id] using hp⟩
  comp {T T' T''} f g := ⟨f.base ≫ g.base,
    fun l ↦ by rw [← E.res_res g.base f.base, g.res_r, f.res_r],
    fun p hp ↦ by
      have := f.map_mem _ (g.map_mem p hp)
      rwa [E.res_res] at this⟩
  id_comp f := Stage.Hom.ext (Category.id_comp f.base)
  comp_id f := Stage.Hom.ext (Category.comp_id f.base)
  assoc f g h := Stage.Hom.ext (Category.assoc f.base g.base h.base)

@[simp] lemma id_base (T : E.Stage) : (𝟙 T : T ⟶ T).base = 𝟙 T.j := rfl

@[simp] lemma comp_base {T T' T'' : E.Stage} (f : T ⟶ T') (g : T' ⟶ T'') :
    (f ≫ g).base = f.base ≫ g.base := rfl

@[ext] lemma stageHom_ext {T T' : E.Stage} {f g : T ⟶ T'} (h : f.base = g.base) : f = g :=
  Stage.Hom.ext h

variable {E}

/-- (Implementation) The ring map from the coefficient algebra of a stage to the sections
of `Wⱼ`. -/
noncomputable def Stage.ρ (T : E.Stage) : CommRingCat.of ↥T.A ⟶ Γ(E.WD.obj T.j, ⊤) :=
  CommRingCat.ofHom ((RingHom.snd _ _).comp (Subalgebra.val T.A).toRingHom)

@[simp] lemma Stage.ρ_apply (T : E.Stage) (a : ↥T.A) :
    T.ρ a = (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 := rfl

/-- (Implementation) The tautological element `(b l, r l)` of the coefficient algebra of a
stage. -/
def Stage.h (T : E.Stage) (l : Fin E.n) : ↥T.A := ⟨(E.b l, T.r l), T.hmem l⟩

@[simp] lemma Stage.coe_h (T : E.Stage) (l : Fin E.n) :
    (T.h l : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)) = (E.b l, T.r l) := rfl

/-- (Implementation) The morphism from `Wⱼ` to the spectrum of the coefficient algebra of a
stage. By `Stage.isOpenImmersion_toSpec` this is an open immersion. -/
noncomputable def Stage.toSpec (T : E.Stage) :
    E.WD.obj T.j ⟶ Spec (CommRingCat.of ↥T.A) :=
  (E.WD.obj T.j).toSpecΓ ≫ Spec.map T.ρ

lemma Stage.toSpec_preimage_basicOpen (T : E.Stage) (l : Fin E.n) :
    T.toSpec ⁻¹ᵁ PrimeSpectrum.basicOpen (T.h l) = (E.WD.obj T.j).basicOpen (T.r l) := by
  rw [Stage.toSpec, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
    Scheme.toSpecΓ_preimage_basicOpen, Stage.ρ_apply, Stage.coe_h]

/-- (Implementation) The ring map from the coefficient algebra of a stage to the sections
of the basic open `Wⱼ(r l) ⊆ Wⱼ`. This realizes the sections over `Wⱼ(r l)` as the
localization of the coefficient algebra away from the tautological element `(b l, r l)`,
see `Stage.isLocalization_away`. -/
noncomputable def Stage.ρRes (T : E.Stage) (l : Fin E.n) :
    CommRingCat.of ↥T.A ⟶ Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) :=
  T.ρ ≫ (E.WD.obj T.j).presheaf.map (homOfLE le_top).op

@[simp] lemma Stage.ρRes_apply (T : E.Stage) (l : Fin E.n) (a : ↥T.A) :
    (T.ρRes l).hom a = ((E.WD.obj T.j).presheaf.map (homOfLE le_top).op).hom a.1.2 := rfl

/-- (Implementation) The image of `W = U ⊓ V` in `X`. -/
lemma opensRange_WUι_comp_Uι (E : ExtensionData.{u}) :
    (E.WU.ι ≫ E.U.ι).opensRange = E.U ⊓ E.V := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, ExtensionData.WU, E.hW₀,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma basicOpen_le_opensRange (E : ExtensionData.{u}) (l : Fin E.n) :
    E.X.basicOpen (E.b l) ≤ (E.WU.ι ≫ E.U.ι).opensRange :=
  (E.hb l).trans E.opensRange_WUι_comp_Uι.ge

/-- (Implementation) Restricting a section of `V` to `X.basicOpen (b l)` and pulling back
to `W` agrees with restricting the pullback to `W`. -/
lemma res_app_eq_sV_res (E : ExtensionData.{u}) (l : Fin E.n) :
    E.X.presheaf.map (homOfLE (E.X.basicOpen_le (E.b l))).op ≫
      (E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)) =
      E.sV ≫ E.WU.toScheme.presheaf.map (homOfLE le_top).op := by
  simp only [ExtensionData.sV, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- (Implementation) A section of `V` restricting to zero on `W` is annihilated by a power
of each of the chosen generators `b l`: the restriction `Γ(X, V) ⟶ Γ(W, 𝒪)` factors through
the localization `Γ(X, V) ⟶ Γ(X, X.basicOpen (b l))` because `X.basicOpen (b l) ≤ U ⊓ V`.
This is the key cancellation step in the proof of Stacks 01Z9. -/
lemma exists_pow_mul_eq_zero_of_sV_eq_zero (l : Fin E.n) {y : Γ(E.X, E.V)}
    (hy : E.sV y = 0) : ∃ K, E.b l ^ K * y = 0 := by
  have := E.hV.isLocalization_basicOpen (E.b l)
  suffices h0 : (E.X.presheaf.map (homOfLE (E.X.basicOpen_le (E.b l))).op) y = 0 by
    obtain ⟨⟨_, K, rfl⟩, hK⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (E.b l)) Γ(E.X, E.X.basicOpen (E.b l)) y).mp h0
    exact ⟨K, hK⟩
  have := (E.WU.ι ≫ E.U.ι).isIso_app _ (E.basicOpen_le_opensRange l)
  apply (ConcreteCategory.bijective_of_isIso
    ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))).1
  rw [map_zero, ← CommRingCat.comp_apply, E.res_app_eq_sV_res l, CommRingCat.comp_apply, hy,
    map_zero]

set_option maxHeartbeats 1600000 in
-- The defeq checks between `algebraMap`s of the two `Algebra` structures in scope and the
-- structure sheaf restriction maps are expensive on the opens diagram of the approximation.
/-- (Implementation, Stacks 01Z9) The sections over the basic open `Wⱼ(r l)` are the
localization of the coefficient algebra of the stage away from the tautological element
`(b l, r l)`. Surjectivity is the condition `hgen` of the stage; injectivity combines the
qcqs lemma on `Wⱼ` with `exists_pow_mul_eq_zero_of_sV_eq_zero` on the `V`-component. -/
lemma Stage.isLocalization_away (T : E.Stage) (l : Fin E.n) :
    letI := (T.ρRes l).hom.toAlgebra
    IsLocalization.Away (T.h l)
      Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := by
  let := (T.ρRes l).hom.toAlgebra
  have := isLocalization_basicOpen_of_qcqs (X := E.WD.obj T.j) (U := ⊤)
    isCompact_univ isQuasiSeparated_univ (T.r l)
  refine ⟨fun ⟨_, m, rfl⟩ ↦ ?_, fun z ↦ ?_, fun {a a'} hd ↦ ?_⟩
  · simp only [RingHom.algebraMap_toAlgebra, map_pow]
    refine IsUnit.pow _ ?_
    exact RingedSpace.isUnit_res_basicOpen (E.WD.obj T.j).toRingedSpace (T.r l)
  · obtain ⟨m, p, hp, hres⟩ := T.hgen l z
    refine ⟨(⟨p, hp⟩, ⟨T.h l ^ m, m, rfl⟩), ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow]
    exact hres.symm
  · -- The second components agree after multiplication by a power of `r l`.
    have hres : a.1.2 |_ (E.WD.obj T.j).basicOpen (T.r l) =
        a'.1.2 |_ (E.WD.obj T.j).basicOpen (T.r l) := hd
    obtain ⟨k, hk⟩ := exists_of_res_eq_of_qcqs_of_top hres
    have hk' : T.r l ^ k * (a.1.2 - a'.1.2) = 0 := by
      rw [mul_sub, sub_eq_zero]
      exact hk
    -- Push down to the intersection `W` and cancel the first components there.
    have hV0 : E.sV (E.b l ^ k * (a.1.1 - a'.1.1)) = 0 := by
      have ht := congrArg (E.t T.j) hk'
      rw [map_mul, map_pow, map_zero, T.hr] at ht
      rw [map_mul, map_pow, map_sub, T.hA _ a.2, T.hA _ a'.2, ← map_sub]
      exact ht
    obtain ⟨K, hK⟩ := E.exists_pow_mul_eq_zero_of_sV_eq_zero l hV0
    refine ⟨⟨T.h l ^ (K + k), K + k, rfl⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Stage.coe_h, Prod.fst_mul,
        Prod.pow_fst]
      rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc]
      exact hK
    · simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Stage.coe_h, Prod.snd_mul,
        Prod.pow_snd]
      rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc, hk', mul_zero]

/-- (Implementation) The heart of Stacks 07RN (via Tags 01Z7 and 01Z9): the morphism from
`Wⱼ` to the spectrum of the coefficient algebra of a stage is an open immersion. -/
instance Stage.isOpenImmersion_toSpec (T : E.Stage) : IsOpenImmersion T.toSpec := by
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  have hx : x ∈ ⨆ l, (E.WD.obj T.j).basicOpen (T.r l) := by rw [T.hcov]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨PrimeSpectrum.basicOpen (T.h l), (T.toSpec_preimage_basicOpen l).ge hl, ?_⟩
  suffices h : IsOpenImmersion (((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec) by
    convert! h <;> rw [toSpec_preimage_basicOpen]
  have e : ((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec =
      ((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ ≫ Spec.map (T.ρRes l) := by
    rw [Stage.toSpec, ← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
      Category.assoc, ← Spec.map_comp, Stage.ρRes]
  rw [e]
  let := (T.ρRes l).hom.toAlgebra
  have : IsLocalization.Away (T.h l)
      Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := T.isLocalization_away l
  exact MorphismProperty.comp_mem _ (T.haff l).isoSpec.hom _ inferInstance
    (IsOpenImmersion.of_isLocalization (T.h l))

/-- (Implementation) The image of `Wⱼ ⟶ Spec A` is the union of the basic opens of the
tautological elements `(b l, r l)`. -/
lemma Stage.opensRange_toSpec (T : E.Stage) :
    T.toSpec.opensRange = ⨆ l, PrimeSpectrum.basicOpen (T.h l) := by
  refine le_antisymm ?_ (iSup_le fun l ↦ ?_)
  · rintro - ⟨x, rfl⟩
    have hx : x ∈ ⨆ l, (E.WD.obj T.j).basicOpen (T.r l) := by rw [T.hcov]; trivial
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, (T.toSpec_preimage_basicOpen l).ge hl⟩
  · have e : ((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec =
        ((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ ≫ Spec.map (T.ρRes l) := by
      rw [Stage.toSpec, ← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
        Category.assoc, ← Spec.map_comp, Stage.ρRes]
    let := (T.ρRes l).hom.toAlgebra
    have : IsLocalization.Away (T.h l)
        Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := T.isLocalization_away l
    have : IsIso (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ) := by
      rw [← IsAffineOpen.isoSpec_hom (T.haff l)]
      infer_instance
    rintro p hp
    obtain ⟨q, hq⟩ : ∃ q, (Spec.map (T.ρRes l)).base q = p := by
      have h := PrimeSpectrum.localization_away_comap_range
        (S := Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l))) (T.h l)
      have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥T.A
          Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)))) := by
        rw [h]
        exact hp
      exact hmem
    obtain ⟨w, hw⟩ := (Scheme.Hom.homeomorph
      (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ)).surjective q
    have hw' : (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ) w = q := hw
    refine ⟨((E.WD.obj T.j).basicOpen (T.r l)).ι w, ?_⟩
    have h1 : (((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec) w = p := by
      rw [e, Scheme.Hom.comp_apply, hw']
      exact hq
    rw [Scheme.Hom.comp_apply] at h1
    exact h1

end ExtensionData

end Scheme.NoetherianApproximation

end AlgebraicGeometry
