/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Algebra.Algebra.Tower
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Filtered.Basic

/-!
# The stages of the induction step of absolute Noetherian approximation

The general case of absolute Noetherian approximation (Stacks Project Tag 01ZA) is proved
by induction over a finite affine cover, extending an approximation of a quasi-compact
open `U` of a quasi-separated scheme `X` across one more affine open `V` (Stacks Project
Tag 07RN). The data of one induction step is bundled into
`AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData`, and the index category
of the extended system is the category
`AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData.Stage` of *stages*: a
stage consists of an index `j` of the approximation of `U`, lifts to the stage `j` of
finitely many sections of `V` whose basic opens cover `W = U ⊓ V`, and a finitely
generated `ℤ`-subalgebra `A` of the fiber product `Γ(X, V) ×_{Γ(W, 𝒪)} Γ(Wⱼ, 𝒪)` big
enough that `Wⱼ` becomes a quasi-affine open of `Spec A`
(`Stage.isOpenImmersion_toSpec`, Tags 01Z7 and 01Z9).

This file constructs the stages and their category; the scheme attached to a stage, the
limit cone and the resulting approximation are in
`WeilConjectures/AlgebraicGeometry/NoetherianApproximation/Extension.lean`.

## Main declarations

* `AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData`: the setup of one
  induction step.
* `AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData.Stage`: a stage of the
  extended system, and its category structure.
* `AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData.Stage.isOpenImmersion_toSpec`:
  the morphism `Wⱼ ⟶ Spec A` attached to a stage is an open immersion (Tags 01Z7, 01Z9).
* `AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData.stageIndex`: the functor
  remembering the underlying index; it is initial, so limits over the system of the `Wⱼ`
  may be computed over the category of stages.

## References

- [Stacks: Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
- [Stacks: Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
- [Stacks: Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
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

/-- The setup for the induction step of absolute Noetherian approximation
(Stacks Project Tag 07RN): a quasi-separated scheme `X` covered by a quasi-compact open `U`
carrying a Noetherian approximation `N` and an affine open `V`; the intersection `U ⊓ V`
is descended to a quasi-compact open `W₀` at a stage `i₀` of `N`, and is exhibited as a
finite union of basic opens of sections `b l` of `V`. -/
structure InductionData where
  /-- The ambient scheme. -/
  X : Scheme.{u}
  /-- The ambient scheme is quasi-separated. -/
  [qs : QuasiSeparatedSpace X]
  /-- The already approximated quasi-compact open. -/
  U : X.Opens
  /-- The new affine open. -/
  V : X.Opens
  /-- The two opens cover the ambient scheme. -/
  sup_eq_top : U ⊔ V = ⊤
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
  /-- The index type of the chosen generators of the intersection. -/
  σ : Type u
  /-- There are only finitely many chosen generators. -/
  [finite : Finite σ]
  /-- The chosen generators of the intersection: sections of `V` whose basic opens
  cover `U ⊓ V`. -/
  b : σ → Γ(X, V)
  /-- The basic opens of the chosen generators cover the intersection. -/
  inf_eq_iSup_basicOpen : U ⊓ V = ⨆ l, X.basicOpen (b l)

namespace InductionData

attribute [instance] qs finite

variable (E : InductionData.{u})

/-- Each chosen generator has its basic open inside the intersection. -/
lemma basicOpen_b_le_inf (E : InductionData.{u}) (l : E.σ) : E.X.basicOpen (E.b l) ≤ E.U ⊓ E.V :=
  E.inf_eq_iSup_basicOpen ▸ le_iSup (fun l ↦ E.X.basicOpen (E.b l)) l

/-- The limit cone of the approximation of `U`. -/
abbrev cone : Cone E.N.D := Cone.mk _ E.N.π

/-- `W = U ⊓ V` as an open of `U`. -/
abbrev WU : E.U.toScheme.Opens := E.N.π.app E.i₀ ⁻¹ᵁ E.W₀

/-- The system of the descended intersections `Wⱼ`. -/
noncomputable def WD : Over E.i₀ ⥤ Scheme.{u} := opensDiagram E.N.D E.i₀ E.W₀

/-- The cone exhibiting `W` as the limit of the `Wⱼ`. -/
noncomputable def Wc : Cone E.WD := opensCone E.N.D E.cone E.i₀ E.W₀

/-- `W` is the limit of the `Wⱼ`. -/
noncomputable def isLimitWc : IsLimit E.Wc :=
  isLimitOpensCone E.N.D E.cone E.N.isLimit E.i₀ E.W₀

instance isAffineHom_WD_map {j j' : Over E.i₀} (f : j ⟶ j') : IsAffineHom (E.WD.map f) :=
  inferInstanceAs (IsAffineHom ((opensDiagram E.N.D E.i₀ E.W₀).map f))

instance (j : Over E.i₀) : CompactSpace (E.WD.obj j) :=
  isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := E.N.D.map j.hom) _ E.W₀.2 E.hW₀c)

instance (j : Over E.i₀) : IsLocallyNoetherian (E.WD.obj j) := by
  have : IsLocallyNoetherian (E.N.D.obj j.left) := (E.N.isNoetherian_obj j.left).1
  exact isLocallyNoetherian_of_isOpenImmersion (Scheme.Opens.ι _)

instance (j : Over E.i₀) : IsNoetherian (E.WD.obj j) := ⟨⟩

/-- The restriction of a section of `V` to `W`, viewed inside the limit of
the `Wⱼ`. -/
noncomputable def resV : Γ(E.X, E.V) ⟶ Γ(E.Wc.pt, ⊤) :=
  (E.WU.ι ≫ E.U.ι).appLE E.V ⊤ (by
    rw [Scheme.Hom.comp_preimage, ← E.hW₀, Scheme.Opens.ι_preimage_self])

/-- The restriction of a section at the stage `j` to the limit `W`. -/
noncomputable def resLimit (j : Over E.i₀) : Γ(E.WD.obj j, ⊤) ⟶ Γ(E.Wc.pt, ⊤) :=
  (E.Wc.π.app j).appTop

lemma resLimit_def (j : Over E.i₀) : E.resLimit j = (E.Wc.π.app j).appTop := rfl

/-- The transition map on sections of the system `Wⱼ`. -/
noncomputable def res {j j' : Over E.i₀} (f : j' ⟶ j) :
    Γ(E.WD.obj j, ⊤) ⟶ Γ(E.WD.obj j', ⊤) :=
  (E.WD.map f).appTop

lemma res_def {j j' : Over E.i₀} (f : j' ⟶ j) : E.res f = (E.WD.map f).appTop := rfl

lemma resLimit_res {j j' : Over E.i₀} (f : j' ⟶ j) (x : Γ(E.WD.obj j, ⊤)) :
    E.resLimit j' (E.res f x) = E.resLimit j x := by
  rw [resLimit_def, res_def, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, E.Wc.w f,
    resLimit_def]

lemma res_res {j j' j'' : Over E.i₀} (f : j' ⟶ j) (g : j'' ⟶ j') (x : Γ(E.WD.obj j, ⊤)) :
    E.res g (E.res f x) = E.res (g ≫ f) x := by
  rw [res_def, res_def, res_def, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Functor.map_comp]

variable {E}

/-- The fiber product `Γ(X, V) ×_{Γ(W, 𝒪)} Γ(Wⱼ, 𝒪)`, i.e. the pairs of
sections agreeing on `W`, as a subalgebra of the product ring. The coefficient algebra of a
stage at `j` is a finitely generated subalgebra of it. -/
noncomputable def fiberProduct (E : InductionData.{u}) (j : Over E.i₀) :
    Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :=
  AlgHom.equalizer (E.resV.hom.comp (RingHom.fst _ _)).toIntAlgHom
    ((E.resLimit j).hom.comp (RingHom.snd _ _)).toIntAlgHom

lemma mem_fiberProduct_iff (E : InductionData.{u}) {j : Over E.i₀}
    (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :
    p ∈ E.fiberProduct j ↔ E.resV p.1 = E.resLimit j p.2 := Iff.rfl

/-- The identity on the `V`-component times restriction on the section
component, as a morphism of `ℤ`-algebras. It maps the fiber product at `j` into the fiber
product at `j'`. -/
noncomputable def resAlgHom {j j' : Over E.i₀} (k : j' ⟶ j) :
    (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) →ₐ[ℤ] Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤) :=
  ((RingHom.id Γ(E.X, E.V)).prodMap (E.res k).hom).toIntAlgHom

@[simp] lemma resAlgHom_apply {j j' : Over E.i₀} (k : j' ⟶ j)
    (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :
    resAlgHom k p = (p.1, E.res k p.2) := rfl

lemma resAlgHom_mem_fiberProduct {j j' : Over E.i₀} (k : j' ⟶ j)
    {p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)} (hp : p ∈ E.fiberProduct j) :
    resAlgHom k p ∈ E.fiberProduct j' := by
  rw [E.mem_fiberProduct_iff] at hp ⊢
  rw [resAlgHom_apply, E.resLimit_res]
  exact hp

variable (E)

/-- A stage of the extended system: an index `j`, a lift `r` of the
generators of `W` to `Wⱼ` such that the basic opens of the `r l` form an affine cover of
`Wⱼ`, and a finitely generated `ℤ`-subalgebra `A` of `Γ(X, V) × Γ(Wⱼ, ⊤)` contained in the
fiber product over `Γ(W, ⊤)`, containing the tautological elements `(b l, r l)` and
generating all the local rings of the cover (condition `hgen`, ensuring that `Wⱼ ⟶ Spec A`
is an open immersion). -/
structure Stage where
  /-- The underlying index. -/
  j : Over E.i₀
  /-- The lifts of the generators of the intersection. -/
  r : E.σ → Γ(E.WD.obj j, ⊤)
  /-- The lifts restrict to the chosen generators on the limit `W`. -/
  hr (l : E.σ) : E.resLimit j (r l) = E.resV (E.b l)
  /-- The basic opens of the lifts cover `Wⱼ`. -/
  hcov : ⨆ l, (E.WD.obj j).basicOpen (r l) = ⊤
  /-- The basic opens of the lifts are affine, so they form an affine cover of `Wⱼ`. -/
  haff (l : E.σ) : IsAffineOpen ((E.WD.obj j).basicOpen (r l))
  /-- The finite-stage coefficient algebra. -/
  A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤))
  /-- The coefficient algebra consists of pairs of sections agreeing on `W`; this is the
  inclusion `A ⊆ Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)` of Stacks 07RN. -/
  A_le_fiberProduct : A ≤ E.fiberProduct j
  /-- The coefficient algebra is a finitely generated `ℤ`-algebra. -/
  fg_A : A.FG
  /-- The coefficient algebra contains the tautological pairs `(b l, r l)`. -/
  hmem (l : E.σ) : (E.b l, r l) ∈ A
  /-- Every section of `Wⱼ` over the basic open of `r l` is, up to a power of `r l`, the
  section component of an element of the coefficient algebra. Together with `hmem` this
  says that `A` is large enough for `Γ(Wⱼ(r l))` to be the localization of `A` away from
  `(b l, r l)` (`Stage.isLocalization_away`), which is what makes `Wⱼ ⟶ Spec A` an open
  immersion. -/
  hgen (l : E.σ) (z : Γ(E.WD.obj j, (E.WD.obj j).basicOpen (r l))) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)), p ∈ A ∧
      ((E.WD.obj j).presheaf.map (homOfLE le_top).op).hom p.2 =
        z * ((E.WD.obj j).presheaf.map (homOfLE le_top).op).hom (r l) ^ m

/-- A morphism of stages over a morphism of underlying indices: the lifts
`r` are compatible, and the coefficient algebra of the target maps into that of the
source. -/
@[ext] structure Stage.Hom (T T' : E.Stage) where
  /-- The underlying index morphism. -/
  base : T.j ⟶ T'.j
  /-- The lifts of the generators are compatible with the transition map. -/
  res_r (l : E.σ) : E.res base (T'.r l) = T.r l
  /-- The coefficient algebra of the target maps into the coefficient algebra of the
  source. -/
  map_mem (p : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)) (hp : p ∈ T'.A) :
    (p.1, E.res base p.2) ∈ T.A

lemma res_id (j : Over E.i₀) (x : Γ(E.WD.obj j, ⊤)) : E.res (𝟙 j) x = x := by
  rw [res_def, CategoryTheory.Functor.map_id]
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

@[ext] lemma Stage.hom_ext {E : InductionData.{u}} {T T' : E.Stage} {f g : T ⟶ T'}
    (h : f.base = g.base) : f = g :=
  Stage.Hom.ext h

variable {E}

/-- The two components of an element of the coefficient algebra of a stage agree on the
intersection `W`. -/
lemma Stage.resV_eq_resLimit_of_mem (T : E.Stage) {p : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)}
    (hp : p ∈ T.A) : E.resV p.1 = E.resLimit T.j p.2 :=
  (E.mem_fiberProduct_iff p).mp (T.A_le_fiberProduct hp)

/-- The ring map from the coefficient algebra of a stage to the sections
of `Wⱼ`. -/
noncomputable def Stage.toSectionsW (T : E.Stage) : CommRingCat.of ↥T.A ⟶ Γ(E.WD.obj T.j, ⊤) :=
  CommRingCat.ofHom ((RingHom.snd _ _).comp (Subalgebra.val T.A).toRingHom)

@[simp] lemma Stage.toSectionsW_apply (T : E.Stage) (a : ↥T.A) :
    T.toSectionsW a = (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 := rfl

/-- The tautological element `(b l, r l)` of the coefficient algebra of a
stage. -/
def Stage.gen (T : E.Stage) (l : E.σ) : ↥T.A := ⟨(E.b l, T.r l), T.hmem l⟩

@[simp] lemma Stage.coe_gen (T : E.Stage) (l : E.σ) :
    (T.gen l : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)) = (E.b l, T.r l) := rfl

/-- The morphism from `Wⱼ` to the spectrum of the coefficient algebra of a
stage. By `Stage.isOpenImmersion_toSpec` this is an open immersion. -/
noncomputable def Stage.toSpec (T : E.Stage) :
    E.WD.obj T.j ⟶ Spec (CommRingCat.of ↥T.A) :=
  (E.WD.obj T.j).toSpecΓ ≫ Spec.map T.toSectionsW

lemma Stage.toSpec_preimage_basicOpen (T : E.Stage) (l : E.σ) :
    T.toSpec ⁻¹ᵁ PrimeSpectrum.basicOpen (T.gen l) = (E.WD.obj T.j).basicOpen (T.r l) := by
  rw [Stage.toSpec, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
    Scheme.toSpecΓ_preimage_basicOpen, Stage.toSectionsW_apply, Stage.coe_gen]

/-- The ring map from the coefficient algebra of a stage to the sections
of the basic open `Wⱼ(r l) ⊆ Wⱼ`. This realizes the sections over `Wⱼ(r l)` as the
localization of the coefficient algebra away from the tautological element `(b l, r l)`,
see `Stage.isLocalization_away`. -/
noncomputable def Stage.toSectionsRes (T : E.Stage) (l : E.σ) :
    CommRingCat.of ↥T.A ⟶ Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) :=
  T.toSectionsW ≫ (E.WD.obj T.j).presheaf.map (homOfLE le_top).op

@[simp] lemma Stage.toSectionsRes_apply (T : E.Stage) (l : E.σ) (a : ↥T.A) :
    (T.toSectionsRes l).hom a = ((E.WD.obj T.j).presheaf.map (homOfLE le_top).op).hom a.1.2 := rfl

/-- The sections of `Wⱼ` over the basic open `Wⱼ(r l)` as an algebra over the coefficient
algebra of the stage, via `Stage.toSectionsRes`. This is the algebra structure in which
`Stage.isLocalization_away` is stated. -/
noncomputable instance Stage.algebraSectionsRes (T : E.Stage) (l : E.σ) :
    Algebra ↥T.A Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) :=
  (T.toSectionsRes l).hom.toAlgebra

@[simp] lemma Stage.algebraMap_apply (T : E.Stage) (l : E.σ) (a : ↥T.A) :
    algebraMap ↥T.A Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) a =
      (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 |_ (E.WD.obj T.j).basicOpen (T.r l) :=
  rfl

/-- The image of `W = U ⊓ V` in `X`. -/
lemma opensRange_WUι_comp_Uι (E : InductionData.{u}) :
    (E.WU.ι ≫ E.U.ι).opensRange = E.U ⊓ E.V := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, InductionData.WU, E.hW₀,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma basicOpen_le_opensRange (E : InductionData.{u}) (l : E.σ) :
    E.X.basicOpen (E.b l) ≤ (E.WU.ι ≫ E.U.ι).opensRange :=
  (E.basicOpen_b_le_inf l).trans E.opensRange_WUι_comp_Uι.ge

/-- Restricting a section of `V` to `X.basicOpen (b l)` and pulling back
to `W` agrees with restricting the pullback to `W`. -/
lemma res_app_eq_resV_res (E : InductionData.{u}) (l : E.σ) :
    E.X.presheaf.map (homOfLE (E.X.basicOpen_le (E.b l))).op ≫
      (E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)) =
      E.resV ≫ E.WU.toScheme.presheaf.map (homOfLE le_top).op := by
  simp only [InductionData.resV, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- A section of `V` restricting to zero on `W` is annihilated by a power
of each of the chosen generators `b l`: the restriction `Γ(X, V) ⟶ Γ(W, 𝒪)` factors through
the localization `Γ(X, V) ⟶ Γ(X, X.basicOpen (b l))` because `X.basicOpen (b l) ≤ U ⊓ V`.
This is the key cancellation step in the proof of Stacks 01Z9. -/
lemma exists_pow_mul_eq_zero_of_resV_eq_zero (l : E.σ) {y : Γ(E.X, E.V)}
    (hy : E.resV y = 0) : ∃ K, E.b l ^ K * y = 0 := by
  have := E.hV.isLocalization_basicOpen (E.b l)
  suffices h0 : (E.X.presheaf.map (homOfLE (E.X.basicOpen_le (E.b l))).op) y = 0 by
    obtain ⟨⟨_, K, rfl⟩, hK⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (E.b l)) Γ(E.X, E.X.basicOpen (E.b l)) y).mp h0
    exact ⟨K, hK⟩
  have := (E.WU.ι ≫ E.U.ι).isIso_app _ (E.basicOpen_le_opensRange l)
  apply (ConcreteCategory.bijective_of_isIso
    ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))).1
  rw [map_zero, ← CommRingCat.comp_apply, E.res_app_eq_resV_res l, CommRingCat.comp_apply, hy,
    map_zero]

/-- Injectivity input for `Stage.isLocalization_away`: two elements of the coefficient
algebra of a stage with the same restriction to the basic open `Wⱼ(r l)` become equal after
multiplication by a power of the tautological element `(b l, r l)`. On the `Wⱼ`-component
this is the qcqs lemma on `Wⱼ`, and on the `V`-component it is
`exists_pow_mul_eq_zero_of_resV_eq_zero`. -/
lemma Stage.exists_pow_gen_mul_eq (T : E.Stage) (l : E.σ) {a a' : ↥T.A}
    (hd : algebraMap ↥T.A Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) a =
      algebraMap ↥T.A Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) a') :
    ∃ c : Submonoid.powers (T.gen l), (c : ↥T.A) * a = (c : ↥T.A) * a' := by
  -- The second components agree after multiplication by a power of `r l`.
  have hres : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 |_ (E.WD.obj T.j).basicOpen (T.r l) =
      (a' : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 |_ (E.WD.obj T.j).basicOpen (T.r l) := hd
  obtain ⟨k, hk⟩ := exists_of_res_eq_of_qcqs_of_top hres
  have hk' : T.r l ^ k * ((a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 - a'.1.2) = 0 := by
    rw [mul_sub, sub_eq_zero]
    exact hk
  -- Push down to the intersection `W` and cancel the first components there.
  have hV0 : E.resV (E.b l ^ k * ((a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 - a'.1.1)) = 0 := by
    have ht := congrArg (E.resLimit T.j) hk'
    rw [map_mul, map_pow, map_zero, T.hr] at ht
    rw [map_mul, map_pow, map_sub, T.resV_eq_resLimit_of_mem a.2,
      T.resV_eq_resLimit_of_mem a'.2, ← map_sub]
    exact ht
  obtain ⟨K, hK⟩ := E.exists_pow_mul_eq_zero_of_resV_eq_zero l hV0
  refine ⟨⟨T.gen l ^ (K + k), K + k, rfl⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
  · simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Stage.coe_gen, Prod.fst_mul,
      Prod.pow_fst]
    rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc]
    exact hK
  · simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Stage.coe_gen, Prod.snd_mul,
      Prod.pow_snd]
    rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc, hk', mul_zero]

/-- The sections over the basic open `Wⱼ(r l)` are the
localization of the coefficient algebra of the stage away from the tautological element
`(b l, r l)`. Surjectivity is the condition `hgen` of the stage; injectivity is
`Stage.exists_pow_gen_mul_eq`. -/
@[stacks 01Z9]
lemma Stage.isLocalization_away (T : E.Stage) (l : E.σ) :
    IsLocalization.Away (T.gen l)
      Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := by
  refine ⟨fun ⟨_, m, rfl⟩ ↦ ?_, fun z ↦ ?_, fun hd ↦ T.exists_pow_gen_mul_eq l hd⟩
  · simp only [map_pow, Stage.algebraMap_apply, Stage.coe_gen]
    exact (RingedSpace.isUnit_res_basicOpen (E.WD.obj T.j).toRingedSpace (T.r l)).pow m
  · obtain ⟨m, p, hp, hres⟩ := T.hgen l z
    refine ⟨(⟨p, hp⟩, ⟨T.gen l ^ m, m, rfl⟩), ?_⟩
    simp only [map_pow, Stage.algebraMap_apply, Stage.coe_gen]
    exact hres.symm

/-- The heart of Stacks 07RN (via Tags 01Z7 and 01Z9): the morphism from
`Wⱼ` to the spectrum of the coefficient algebra of a stage is an open immersion. -/
@[stacks 01Z7]
instance Stage.isOpenImmersion_toSpec (T : E.Stage) : IsOpenImmersion T.toSpec := by
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  have hx : x ∈ ⨆ l, (E.WD.obj T.j).basicOpen (T.r l) := by
    rw [T.hcov]
    trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨PrimeSpectrum.basicOpen (T.gen l), (T.toSpec_preimage_basicOpen l).ge hl, ?_⟩
  suffices h : IsOpenImmersion (((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec) by
    convert! h <;> rw [toSpec_preimage_basicOpen]
  have e : ((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec =
      ((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ ≫ Spec.map (T.toSectionsRes l) := by
    rw [Stage.toSpec, ← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
      Category.assoc, ← Spec.map_comp, Stage.toSectionsRes]
  rw [e]
  have := T.isLocalization_away l
  exact MorphismProperty.comp_mem _ (T.haff l).isoSpec.hom _ inferInstance
    (IsOpenImmersion.of_isLocalization (T.gen l))

/-- The image of `Wⱼ ⟶ Spec A` is the union of the basic opens of the
tautological elements `(b l, r l)`. -/
lemma Stage.opensRange_toSpec (T : E.Stage) :
    T.toSpec.opensRange = ⨆ l, PrimeSpectrum.basicOpen (T.gen l) := by
  refine le_antisymm ?_ (iSup_le fun l ↦ ?_)
  · rintro - ⟨x, rfl⟩
    have hx : x ∈ ⨆ l, (E.WD.obj T.j).basicOpen (T.r l) := by
      rw [T.hcov]
      trivial
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, (T.toSpec_preimage_basicOpen l).ge hl⟩
  · have e : ((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec =
        ((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ ≫ Spec.map (T.toSectionsRes l) := by
      rw [Stage.toSpec, ← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
        Category.assoc, ← Spec.map_comp, Stage.toSectionsRes]
    have := T.isLocalization_away l
    have : IsIso (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ) := by
      rw [← IsAffineOpen.isoSpec_hom (T.haff l)]
      infer_instance
    rintro p hp
    obtain ⟨q, hq⟩ : ∃ q, (Spec.map (T.toSectionsRes l)).base q = p := by
      have h := PrimeSpectrum.localization_away_comap_range
        (S := Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l))) (T.gen l)
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
    rwa [Scheme.Hom.comp_apply] at h1

/-!
#### Existence of stages

Following Stacks 01Z7, we produce stages: the sections of `Wⱼ` over a basic open `Wⱼ(r l)`
form a finitely generated `ℤ`-algebra, and each generator is, up to a power of `r l`, the
second component of an element of the fiber product `Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)`. Adjoining
these elements to any finitely generated subalgebra of the fiber product yields a stage.
-/

/-- The basic open of `W` attached to a generator `b l` is the pullback of
the basic open of `X` attached to it. -/
lemma basicOpen_resV (E : InductionData.{u}) (l : E.σ) :
    E.Wc.pt.basicOpen (E.resV (E.b l)) =
      (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l) := by
  simp only [InductionData.resV, Scheme.basicOpen_appLE, top_inf_eq]

/-- The basic opens of the chosen generators cover `W`. -/
lemma iSup_basicOpen_resV (E : InductionData.{u}) :
    ⨆ l, E.Wc.pt.basicOpen (E.resV (E.b l)) = ⊤ := by
  simp_rw [E.basicOpen_resV]
  rw [← Scheme.Hom.preimage_iSup, ← E.inf_eq_iSup_basicOpen]
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have : (E.WU.ι ≫ E.U.ι) x ∈ (E.WU.ι ≫ E.U.ι).opensRange := ⟨x, rfl⟩
  rwa [E.opensRange_WUι_comp_Uι] at this

/-- `Wⱼ` is of finite type over `ℤ`, being open in a stage of the
approximation of `U`. -/
instance (j : Over E.i₀) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (E.WD.obj j)) := by
  rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from (E.WD.obj j))
    ((E.N.D.map j.hom ⁻¹ᵁ E.W₀).ι ≫ specULiftZIsTerminal.from (E.N.D.obj j.left))]
  infer_instance

instance : CompactSpace E.Wc.pt := by
  have := isAffineHom_π_app E.N.D E.cone E.N.isLimit E.i₀
  exact isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := E.N.π.app E.i₀) _ E.W₀.2 E.hW₀c)

instance : QuasiSeparatedSpace E.Wc.pt := by
  have : QuasiSeparatedSpace E.U.toScheme :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ E.U.2).mp (.of_quasiSeparatedSpace _)
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ E.WU.2).mp (.of_quasiSeparatedSpace _)

variable (E) in
/-- Restricting a global section of `W` to the basic open of `resV (b l)`
factors through the restriction to the pullback of `X.basicOpen (b l)`; the two opens are
equal by `basicOpen_resV`. -/
lemma restrict_basicOpen_resV_eq (l : E.σ) (x : Γ(E.Wc.pt, ⊤)) :
    x |_ E.Wc.pt.basicOpen (E.resV (E.b l)) =
      (E.Wc.pt.presheaf.map (eqToHom (E.basicOpen_resV l)).op)
        ((E.Wc.pt.presheaf.map (homOfLE le_top).op) x) := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg
    (fun f : E.Wc.pt.basicOpen (E.resV (E.b l)) ⟶ (⊤ : E.Wc.pt.Opens) ↦
      (E.Wc.pt.presheaf.map f.op).hom x)
    (Subsingleton.elim _ _)

/-- Every section over a basic open `Wⱼ(r l)` is, up to a
power of `r l`, the restriction of the second component of an element of the fiber product
`Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)`. -/
@[stacks 01Z7]
lemma exists_mem_fiberProduct_res_eq_mul_pow (E : InductionData.{u}) {j : Over E.i₀}
    {l : E.σ} {rl : Γ(E.WD.obj j, ⊤)} (hrl : E.resLimit j rl = E.resV (E.b l))
    (z : Γ(E.WD.obj j, (E.WD.obj j).basicOpen rl)) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)), p ∈ E.fiberProduct j ∧
      ((E.WD.obj j).presheaf.map (homOfLE le_top).op) p.2 =
        z * ((E.WD.obj j).presheaf.map (homOfLE le_top).op) rl ^ m := by
  classical
  -- Lift `z` to a global section `y` of `Wⱼ`, up to a power of `rl`.
  obtain ⟨m₀, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
    (E.WD.obj j) ⊤ isCompact_univ isQuasiSeparated_univ rl z
  -- The restriction of `resLimit y` to the basic open of `W` comes from a section `zV` of
  -- `X.basicOpen (b l)`.
  have hiso := (E.WU.ι ≫ E.U.ι).isIso_app _ (E.basicOpen_le_opensRange l)
  obtain ⟨zV, hzV⟩ := (ConcreteCategory.bijective_of_isIso
    ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))).2
    ((E.WU.toScheme.presheaf.map (homOfLE le_top).op) (E.resLimit j y))
  -- Write `zV` as `v₀ / (b l) ^ K` using that `V` is affine.
  have := E.hV.isLocalization_basicOpen (E.b l)
  obtain ⟨⟨v₀, ⟨_, K, rfl⟩⟩, hv⟩ := IsLocalization.surj (M := Submonoid.powers (E.b l)) zV
  rw [map_pow] at hv
  -- Restricting sections of `V` to `X.basicOpen (b l)` and pulling back to `W` agrees with
  -- pulling back to `W` and restricting.
  have happ (x : Γ(E.X, E.V)) :
      ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))
        ((algebraMap Γ(E.X, E.V) Γ(E.X, E.X.basicOpen (E.b l))) x) =
      (E.WU.toScheme.presheaf.map (homOfLE le_top).op) (E.resV x) := by
    have h := congrArg
      (fun f : Γ(E.X, E.V) ⟶
          Γ(E.WU.toScheme, (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l)) ↦ f x)
      (E.res_app_eq_resV_res l)
    dsimp only at h
    rwa [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  -- Transport the localization relation along the pullback to `W`.
  have e₁ := congrArg ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)) ·) hv
  dsimp only at e₁
  rw [map_mul, map_pow, happ, happ, hzV] at e₁
  have e₁' : (E.Wc.pt.presheaf.map (homOfLE le_top).op) (E.resLimit j y) *
        (E.Wc.pt.presheaf.map (homOfLE le_top).op) (E.resV (E.b l)) ^ K =
      (E.Wc.pt.presheaf.map (homOfLE (le_top :
        (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l) ≤ ⊤)).op) (E.resV v₀) := e₁
  -- `resV v₀` and `resLimit (rl ^ K * y)` agree on the basic open of `resV (b l)`.
  have h6 : E.resV v₀ |_ E.Wc.pt.basicOpen (E.resV (E.b l)) =
      E.resLimit j (rl ^ K * y) |_ E.Wc.pt.basicOpen (E.resV (E.b l)) := by
    rw [E.restrict_basicOpen_resV_eq, E.restrict_basicOpen_resV_eq]
    congr 1
    rw [map_mul, map_pow, hrl, map_mul, map_pow]
    linear_combination -e₁'
  -- Hence they agree after multiplication by a power of `resV (b l)`.
  obtain ⟨M, hM⟩ := exists_of_res_eq_of_qcqs_of_top (X := E.Wc.pt) h6
  -- Assemble the element of the fiber product.
  refine ⟨M + K + m₀, (E.b l ^ M * v₀, rl ^ (M + K) * y), ?_, ?_⟩
  · rw [E.mem_fiberProduct_iff]
    dsimp only
    rw [map_mul, map_pow, hM, ← hrl, ← map_pow, ← map_mul, ← mul_assoc, ← pow_add]
  · dsimp only
    rw [map_mul, map_pow]
    have hy' : ((E.WD.obj j).presheaf.map (homOfLE le_top).op) y =
        ((E.WD.obj j).presheaf.map (homOfLE le_top).op) rl ^ m₀ * z := hy
    rw [hy', pow_add, pow_add]
    ring

/-!
#### The category of stages

Following `lemma:nagata-valid-refinements-directed`, the stages form a nonempty cofiltered
category: any finitely generated subalgebra of the fiber product can be enlarged to satisfy
the generation condition (Stacks 01Z7), lifts of the generators exist at a common index by
the section-descent lemmas for the limit `W = lim Wⱼ`, and the covering and affineness
conditions descend from the limit by Stacks 01Z4.
-/

variable (E)

/-- The data of a stage without its coefficient algebra: an index `j` and
lifts `r` of the generators of the intersection such that the basic opens of the `r l` form
an affine cover of `Wⱼ`. -/
structure PreStage where
  /-- The underlying index. -/
  j : Over E.i₀
  /-- The lifts of the generators of the intersection. -/
  r : E.σ → Γ(E.WD.obj j, ⊤)
  /-- The lifts restrict to the chosen generators on the limit `W`. -/
  hr (l : E.σ) : E.resLimit j (r l) = E.resV (E.b l)
  /-- The basic opens of the lifts cover `Wⱼ`. -/
  hcov : ⨆ l, (E.WD.obj j).basicOpen (r l) = ⊤
  /-- The basic opens of the lifts are affine. -/
  haff (l : E.σ) : IsAffineOpen ((E.WD.obj j).basicOpen (r l))

variable {E}

/-- The pre-stage underlying a stage. -/
def Stage.toPreStage (T : E.Stage) : E.PreStage :=
  ⟨T.j, T.r, T.hr, T.hcov, T.haff⟩

/-- The basic open of a restricted section is the preimage of the basic open. -/
lemma basicOpen_res {j j' : Over E.i₀} (k : j' ⟶ j) (x : Γ(E.WD.obj j, ⊤)) :
    (E.WD.obj j').basicOpen (E.res k x) = E.WD.map k ⁻¹ᵁ ((E.WD.obj j).basicOpen x) :=
  (Scheme.preimage_basicOpen_top (E.WD.map k) x).symm

/-- Pre-stages restrict along morphisms of indices. -/
noncomputable def PreStage.restrict (P : E.PreStage) {j' : Over E.i₀} (k : j' ⟶ P.j) :
    E.PreStage where
  j := j'
  r l := E.res k (P.r l)
  hr l := by rw [E.resLimit_res, P.hr]
  hcov := by
    simp_rw [basicOpen_res, ← Scheme.Hom.preimage_iSup, P.hcov, Scheme.Hom.preimage_top]
  haff l := by
    rw [basicOpen_res]
    exact (P.haff l).preimage _

/-- For every pre-stage and every generator index `l`, there
is a finite subset of the fiber product such that every subalgebra containing it and the
tautological pair `(b l, r l)` satisfies the generation condition of a stage at `l`: the
sections over the affine basic open `Wⱼ(r l)` form a finitely generated `ℤ`-algebra, and
every generator is, up to a power of `r l`, the section component of an element of the
fiber product. -/
@[stacks 01Z7]
lemma PreStage.exists_finset_hgen (P : E.PreStage) (l : E.σ) :
    ∃ s : Finset (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)),
      (∀ q ∈ s, q ∈ E.fiberProduct P.j) ∧
      ∀ A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)),
        (E.b l, P.r l) ∈ A → (∀ q ∈ s, q ∈ A) →
        ∀ z : Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)),
          ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
            ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom p.2 =
              z * ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom (P.r l) ^ m := by
  classical
  have hft : Algebra.FiniteType ℤ Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)) :=
    IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType
      (f := specULiftZIsTerminal.from (E.WD.obj P.j)) (P.haff l)
  obtain ⟨s₀, hs₀⟩ := hft.1
  choose m p hp₁ hp₂ using fun z : s₀ ↦
    E.exists_mem_fiberProduct_res_eq_mul_pow (P.hr l) (z : _)
  refine ⟨s₀.attach.image p, fun q hq ↦ ?_, ?_⟩
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
    exact hp₁ z
  · intro A hbr hsub z
    set resTop := ((E.WD.obj P.j).presheaf.map
      (homOfLE (le_top : (E.WD.obj P.j).basicOpen (P.r l) ≤ ⊤)).op).hom
    let S : Subalgebra ℤ Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)) :=
      { carrier := {z | ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
          resTop p.2 = z * resTop (P.r l) ^ m}
        one_mem' := ⟨0, 1, one_mem A, by simp⟩
        zero_mem' := ⟨0, 0, zero_mem A, by simp⟩
        mul_mem' := by
          rintro z₁ z₂ ⟨m₁, p₁, h₁, e₁⟩ ⟨m₂, p₂, h₂, e₂⟩
          refine ⟨m₁ + m₂, p₁ * p₂, mul_mem h₁ h₂, ?_⟩
          change resTop (p₁.2 * p₂.2) = _
          rw [map_mul, e₁, e₂]
          ring
        add_mem' := by
          rintro z₁ z₂ ⟨m₁, p₁, h₁, e₁⟩ ⟨m₂, p₂, h₂, e₂⟩
          refine ⟨m₁ + m₂, p₁ * (E.b l, P.r l) ^ m₂ + p₂ * (E.b l, P.r l) ^ m₁,
            add_mem (mul_mem h₁ (pow_mem hbr m₂)) (mul_mem h₂ (pow_mem hbr m₁)), ?_⟩
          change resTop (p₁.2 * P.r l ^ m₂ + p₂.2 * P.r l ^ m₁) = _
          rw [map_add, map_mul, map_mul, map_pow, map_pow, e₁, e₂]
          ring
        algebraMap_mem' := fun c ↦ ⟨0, algebraMap ℤ _ c, A.algebraMap_mem c, by
          change resTop (algebraMap ℤ _ c) = _
          rw [pow_zero, mul_one]
          exact map_intCast resTop c⟩ }
    have hS : Algebra.adjoin ℤ (↑s₀ : Set _) ≤ S := by
      refine Algebra.adjoin_le fun z hz ↦ ?_
      exact ⟨m ⟨z, hz⟩, p ⟨z, hz⟩,
        hsub _ (Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩), hp₂ ⟨z, hz⟩⟩
    exact hS (hs₀ ▸ Algebra.mem_top (R := ℤ) (x := z))

/-- The finite subset of the fiber product chosen by
`AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData.PreStage.exists_finset_hgen`:
adjoining it to a subalgebra containing `(b l, r l)` makes the generation condition of a
stage hold at `l`. -/
noncomputable def PreStage.genFinset (P : E.PreStage) (l : E.σ) :
    Finset (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)) :=
  (P.exists_finset_hgen l).choose

lemma PreStage.genFinset_le_fiberProduct (P : E.PreStage) (l : E.σ) {q}
    (hq : q ∈ P.genFinset l) : q ∈ E.fiberProduct P.j :=
  (P.exists_finset_hgen l).choose_spec.1 q hq

lemma PreStage.exists_mem_of_genFinset_subset (P : E.PreStage) (l : E.σ)
    (A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤))) (hbr : (E.b l, P.r l) ∈ A)
    (hsub : ∀ q ∈ P.genFinset l, q ∈ A)
    (z : Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l))) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
      ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom p.2 =
        z * ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom (P.r l) ^ m :=
  (P.exists_finset_hgen l).choose_spec.2 A hbr hsub z

/-- Enlarge a finitely generated subalgebra of the fiber
product containing the tautological pairs to the coefficient algebra of a stage over a
given pre-stage. -/
noncomputable def PreStage.mkStage (P : E.PreStage)
    (A₀ : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)))
    (hA₀ : A₀ ≤ E.fiberProduct P.j) (hfg : A₀.FG)
    (hmem : ∀ l, (E.b l, P.r l) ∈ A₀) : E.Stage where
  j := P.j
  r := P.r
  hr := P.hr
  hcov := P.hcov
  haff := P.haff
  A := A₀ ⊔ Algebra.adjoin ℤ (⋃ l, ↑(P.genFinset l))
  A_le_fiberProduct :=
    sup_le hA₀ (Algebra.adjoin_le fun q hq ↦ by
      obtain ⟨l, hql⟩ := Set.mem_iUnion.mp hq
      exact P.genFinset_le_fiberProduct l hql)
  fg_A := hfg.sup (Subalgebra.fg_def.mpr
    ⟨_, Set.finite_iUnion fun l ↦ (P.genFinset l).finite_toSet, rfl⟩)
  hmem l := Algebra.mem_sup_left (hmem l)
  hgen l z :=
    P.exists_mem_of_genFinset_subset l _ (Algebra.mem_sup_left (hmem l))
      (fun q hq ↦ Algebra.mem_sup_right
        (Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨l, hq⟩))) z

@[simp] lemma PreStage.mkStage_j (P : E.PreStage)
    (A₀ : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤))) (hA₀ : A₀ ≤ E.fiberProduct P.j)
    (hfg : A₀.FG) (hmem : ∀ l, (E.b l, P.r l) ∈ A₀) :
    (P.mkStage A₀ hA₀ hfg hmem).j = P.j := rfl

@[simp] lemma PreStage.mkStage_r (P : E.PreStage)
    (A₀ : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤))) (hA₀ : A₀ ≤ E.fiberProduct P.j)
    (hfg : A₀.FG) (hmem : ∀ l, (E.b l, P.r l) ∈ A₀) :
    (P.mkStage A₀ hA₀ hfg hmem).r = P.r := rfl

lemma PreStage.le_mkStage_A (P : E.PreStage)
    (A₀ : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤))) (hA₀ : A₀ ≤ E.fiberProduct P.j)
    (hfg : A₀.FG) (hmem : ∀ l, (E.b l, P.r l) ∈ A₀) :
    A₀ ≤ (P.mkStage A₀ hA₀ hfg hmem).A := le_sup_left

/-- The minimal stage over a pre-stage: adjoin the tautological pairs and
close up under the generation condition. -/
noncomputable def PreStage.stage (P : E.PreStage) : E.Stage :=
  P.mkStage (Algebra.adjoin ℤ (Set.range fun l ↦ (E.b l, P.r l)))
    (Algebra.adjoin_le (by
      rintro p ⟨l, rfl⟩
      exact (E.mem_fiberProduct_iff _).mpr (P.hr l).symm))
    (Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩)
    (fun l ↦ Algebra.subset_adjoin ⟨l, rfl⟩)

@[simp] lemma PreStage.stage_j (P : E.PreStage) : P.stage.j = P.j := rfl

/-- Restrict a stage along a morphism of indices, adjoining an extra
finitely generated subalgebra of the fiber product. -/
noncomputable def Stage.restrict (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤)))
    (hA' : A' ≤ E.fiberProduct j') (hfg : A'.FG) : E.Stage :=
  (T.toPreStage.restrict k).mkStage (T.A.map (resAlgHom k) ⊔ A')
    (sup_le (by
      rintro p ⟨q, hq, rfl⟩
      exact resAlgHom_mem_fiberProduct k (T.A_le_fiberProduct hq)) hA')
    ((T.fg_A.map _).sup hfg)
    (fun l ↦ Algebra.mem_sup_left ⟨(E.b l, T.r l), T.hmem l, rfl⟩)

variable (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
  (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤))) (hA' : A' ≤ E.fiberProduct j')
  (hfg : A'.FG)

@[simp] lemma Stage.restrict_j : (T.restrict k A' hA' hfg).j = j' := rfl

@[simp] lemma Stage.restrict_r (l : E.σ) :
    (T.restrict k A' hA' hfg).r l = E.res k (T.r l) := rfl

lemma Stage.le_restrict_A : A' ≤ (T.restrict k A' hA' hfg).A :=
  le_trans le_sup_right ((T.toPreStage.restrict k).le_mkStage_A _ _ _ _)

/-- The canonical morphism from a restricted stage. -/
noncomputable def Stage.restrictHom : T.restrict k A' hA' hfg ⟶ T where
  base := k
  res_r _ := rfl
  map_mem p hp := (T.toPreStage.restrict k).le_mkStage_A _ _ _ _
    (Algebra.mem_sup_left ⟨p, hp, rfl⟩)

@[simp] lemma Stage.restrictHom_base : (T.restrictHom k A' hA' hfg).base = k := rfl

variable (E)

/-- The lifts of the generators of the intersection exist at a common
index below any given index. -/
lemma exists_r (j₀ : Over E.i₀) :
    ∃ (j : Over E.i₀) (_ : j ⟶ j₀) (r : E.σ → Γ(E.WD.obj j, ⊤)),
      ∀ l, E.resLimit j (r l) = E.resV (E.b l) := by
  have hex (j : Over E.i₀) (l : E.σ) :
      ∃ (j' : Over E.i₀) (_ : j' ⟶ j) (r : Γ(E.WD.obj j', ⊤)),
        E.resLimit j' r = E.resV (E.b l) := by
    obtain ⟨i, r₀, hr₀⟩ := exists_appTop_π_eq_of_isLimit E.WD E.Wc E.isLimitWc (E.resV (E.b l))
    obtain ⟨j', kj, ki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    exact ⟨j', kj, E.res ki r₀, by
      rw [E.resLimit_res]
      exact hr₀.symm⟩
  obtain ⟨j, k, h⟩ := exists_hom_forall_of_stableUnderPrecomp_of_forall_exists_hom (i := j₀)
    (fun j' _ l ↦ ∃ r, E.resLimit j' r = E.resV (E.b l))
    (fun {j j'} k' k l hl ↦ by
      obtain ⟨r, hr⟩ := hl
      exact ⟨E.res k' r, by
        rw [E.resLimit_res]
        exact hr⟩)
    (fun j k l ↦ by
      obtain ⟨j', k', r, hr⟩ := hex j l
      exact ⟨j', k', r, hr⟩)
  choose r hr using h
  exact ⟨j, k, r, hr⟩

/-- The basic opens of the limit lifts of the generators are affine: they
are the basic opens of the affine `V`, transported into the limit `W`. -/
lemma isAffineOpen_basicOpen_resV (l : E.σ) :
    IsAffineOpen (E.Wc.pt.basicOpen (E.resV (E.b l))) := by
  rw [E.basicOpen_resV]
  exact (E.hV.basicOpen (E.b l)).preimage_of_isOpenImmersion _
    (by
      rw [E.opensRange_WUι_comp_Uι]
      exact E.basicOpen_b_le_inf l)

/-- Below any index, there is a pre-stage: lifts of the generators whose
basic opens are affine and cover. The covering condition descends from the limit by
`exists_map_eq_top`, and affineness by descending the affine limit basic open
(Stacks 01Z4). -/
lemma exists_preStage_hom (j₀ : Over E.i₀) :
    ∃ (P : E.PreStage), Nonempty (P.j ⟶ j₀) := by
  -- Step 1: lifts with the covering condition.
  obtain ⟨j₁, k₁, r, hr⟩ := E.exists_r j₀
  have hU : E.Wc.π.app j₁ ⁻¹ᵁ (⨆ l, (E.WD.obj j₁).basicOpen (r l)) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    simp_rw [Scheme.preimage_basicOpen_top]
    have h (l : E.σ) : (E.Wc.π.app j₁).appTop (r l) = E.resV (E.b l) := hr l
    simp_rw [h]
    exact E.iSup_basicOpen_resV
  obtain ⟨j₂, k₂, hk₂⟩ := exists_map_eq_top E.WD E.Wc E.isLimitWc _ hU
  set r₂ : E.σ → Γ(E.WD.obj j₂, ⊤) := fun l ↦ E.res k₂ (r l) with hr₂def
  have hr₂ (l : E.σ) : E.resLimit j₂ (r₂ l) = E.resV (E.b l) := by rw [hr₂def, E.resLimit_res, hr]
  have hcov₂ : ⨆ l, (E.WD.obj j₂).basicOpen (r₂ l) = ⊤ := by
    simp_rw [hr₂def, basicOpen_res, ← Scheme.Hom.preimage_iSup, hk₂]
  -- Step 2: affineness of the basic opens, by descending the affine limit basic open
  -- and equalizing (Stacks 01Z4).
  have hex (j : Over E.i₀) (k : j ⟶ j₂) (l : E.σ) :
      ∃ (ja : Over E.i₀) (ka : ja ⟶ j),
        IsAffineOpen ((E.WD.obj ja).basicOpen (E.res (ka ≫ k) (r₂ l))) := by
    obtain ⟨i, O, hO, hOeq⟩ := exists_isAffineOpen_preimage_eq E.WD E.Wc E.isLimitWc _
      (E.isAffineOpen_basicOpen_resV l)
    obtain ⟨j', kj, ki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    have hpre : E.Wc.π.app j' ⁻¹ᵁ ((E.WD.obj j').basicOpen (E.res (kj ≫ k) (r₂ l))) =
        E.Wc.π.app j' ⁻¹ᵁ (E.WD.map ki ⁻¹ᵁ O) := by
      rw [Scheme.preimage_basicOpen_top, ← Scheme.Hom.comp_preimage, E.Wc.w ki, hOeq]
      congr 1
      exact (E.resLimit_res (kj ≫ k) (r₂ l)).trans (hr₂ l)
    obtain ⟨j'', k'', heq⟩ := exists_map_preimage_eq_map_preimage E.WD E.Wc E.isLimitWc
      (TopologicalSpace.NoetherianSpace.isCompact _)
      (TopologicalSpace.NoetherianSpace.isCompact _) hpre
    refine ⟨j'', k'' ≫ kj, ?_⟩
    have e : (E.WD.obj j'').basicOpen (E.res ((k'' ≫ kj) ≫ k) (r₂ l)) =
        E.WD.map k'' ⁻¹ᵁ ((E.WD.obj j').basicOpen (E.res (kj ≫ k) (r₂ l))) := by
      rw [Scheme.preimage_basicOpen_top]
      congr 1
      rw [Category.assoc]
      exact (E.res_res (kj ≫ k) k'' _).symm
    rw [e, heq]
    exact (hO.preimage (E.WD.map ki)).preimage (E.WD.map k'')
  obtain ⟨j₃, k₃, h₃⟩ := exists_hom_forall_of_stableUnderPrecomp_of_forall_exists_hom (i := j₂)
    (fun j' k l ↦ IsAffineOpen ((E.WD.obj j').basicOpen (E.res k (r₂ l))))
    (fun {j j'} k' k l hl ↦ by
      have e : (E.WD.obj j').basicOpen (E.res (k' ≫ k) (r₂ l)) =
          E.WD.map k' ⁻¹ᵁ ((E.WD.obj j).basicOpen (E.res k (r₂ l))) := by
        rw [Scheme.preimage_basicOpen_top]
        congr 1
        exact (E.res_res k k' _).symm
      rw [e]
      exact hl.preimage _)
    hex
  have hcov₃ : ⨆ l, (E.WD.obj j₃).basicOpen (E.res k₃ (r₂ l)) = ⊤ := by
    simp_rw [basicOpen_res, ← Scheme.Hom.preimage_iSup, hcov₂, Scheme.Hom.preimage_top]
  exact ⟨⟨j₃, fun l ↦ E.res k₃ (r₂ l), fun l ↦ by rw [E.resLimit_res, hr₂], hcov₃, h₃⟩,
    ⟨(k₃ ≫ k₂) ≫ k₁⟩⟩

/-- Equalize two families of sections with equal limit restrictions at a
common finer index. -/
lemma exists_hom_res_eq {j₂ : Over E.i₀} (x y : E.σ → Γ(E.WD.obj j₂, ⊤))
    (h : ∀ l, E.resLimit j₂ (x l) = E.resLimit j₂ (y l)) :
    ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l, E.res k (x l) = E.res k (y l) := by
  apply exists_hom_forall_of_stableUnderPrecomp_of_forall_exists_hom
    (fun j k l ↦ E.res k (x l) = E.res k (y l))
  · intro j j' k' k l hl
    exact (E.res_res k k' _).symm.trans
      ((congrArg (fun z ↦ E.res k' z) hl).trans (E.res_res k k' _))
  · intro j k l
    have hcpt : IsCompact ((⊤ : (E.WD.obj j).Opens) : Set (E.WD.obj j)) := isCompact_univ
    obtain ⟨j', k', hk'⟩ := exists_app_map_eq_map_of_isLimit E.WD E.Wc E.isLimitWc hcpt
      (E.res k (x l)) (E.res k (y l))
      (show E.resLimit j (E.res k (x l)) = E.resLimit j (E.res k (y l)) by
        rw [E.resLimit_res, E.resLimit_res, h])
    refine ⟨j', k', ?_⟩
    exact (E.res_res k k' _).symm.trans (hk'.trans (E.res_res k k' _))

instance : Nonempty E.Stage := by
  obtain ⟨P, -⟩ := E.exists_preStage_hom (Over.mk (𝟙 E.i₀))
  exact ⟨P.stage⟩

instance : IsCofilteredOrEmpty E.Stage where
  cone_objs T₁ T₂ := by
    obtain ⟨j', k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs T₁.j T₂.j
    obtain ⟨j, k, hk⟩ := E.exists_hom_res_eq (fun l ↦ E.res k₁ (T₁.r l))
      (fun l ↦ E.res k₂ (T₂.r l)) (fun l ↦ by rw [E.resLimit_res, E.resLimit_res, T₁.hr, T₂.hr])
    have hmap : T₂.A.map (resAlgHom (k ≫ k₂)) ≤ E.fiberProduct j := by
      rintro p ⟨q, hq, rfl⟩
      exact resAlgHom_mem_fiberProduct _ (T₂.A_le_fiberProduct hq)
    refine ⟨T₁.restrict (k ≫ k₁) (T₂.A.map (resAlgHom (k ≫ k₂))) hmap (T₂.fg_A.map _),
      T₁.restrictHom _ _ _ _, ⟨k ≫ k₂, fun l ↦ ?_, fun p hp ↦ ?_⟩, trivial⟩
    · exact (E.res_res k₂ k _).symm.trans ((hk l).symm.trans (E.res_res k₁ k _))
    · exact T₁.le_restrict_A _ _ _ _ ⟨p, hp, rfl⟩
  cone_maps T₁ T₂ f g := by
    obtain ⟨j', k, hk⟩ := IsCofilteredOrEmpty.cone_maps f.base g.base
    refine ⟨T₁.restrict k ⊥ bot_le Subalgebra.fg_bot, T₁.restrictHom _ _ _ _, ?_⟩
    exact Stage.hom_ext (by simpa using hk)

instance : IsCofiltered E.Stage := ⟨⟩

/-- The index functor from stages to the base indices. By
`exists_preStage_hom` and the restriction construction it is initial: limits over the
system of the `Wⱼ` may be computed over the category of stages. -/
@[simps] def stageIndex : E.Stage ⥤ Over E.i₀ where
  obj T := T.j
  map f := f.base

instance : E.stageIndex.Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro j
    obtain ⟨P, ⟨k⟩⟩ := E.exists_preStage_hom j
    exact ⟨P.stage, ⟨k⟩⟩
  · intro j T s s'
    obtain ⟨j', k, hk⟩ := IsCofilteredOrEmpty.cone_maps s s'
    exact ⟨T.restrict k ⊥ bot_le Subalgebra.fg_bot, T.restrictHom _ _ _ _, by simpa using hk⟩

end InductionData

end Scheme.NoetherianApproximation

end AlgebraicGeometry
