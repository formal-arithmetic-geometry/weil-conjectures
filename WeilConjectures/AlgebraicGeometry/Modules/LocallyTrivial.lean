/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# An invertible sheaf of modules is locally isomorphic to the structure sheaf

A sheaf of modules `M` on a scheme `X` is invertible, in the sense of
`WeilConjectures.AlgebraicGeometry.Modules.Picard`, when there is a sheaf of modules `N` and an
isomorphism `M ⊗ N ≅ 𝒪ₓ`. This file proves that such an `M` is a line bundle in the geometric
sense: it is locally free of rank one. Concretely, every point of `X` has an open neighbourhood
`W` carrying a section `m` of `M` such that multiplication by `m` is an isomorphism
`𝒪_W ≅ M|_W`; in particular `M` is `SheafOfModules.IsLocallyFree` and
`SheafOfModules.IsFiniteType`, which is this project's spelling of "line bundle".

The proof has two halves.

The first is a comparison between the tensor product of two sheaves of modules and the
*sectionwise* tensor product of the underlying presheaves of modules. The former is by
construction the sheafification of the latter, so there is a canonical morphism
`SheafOfModules.tensorPresheafHom` from the sectionwise tensor product to `M ⊗ N`, and it becomes
an isomorphism after sheafification; over a topological space this makes it locally surjective.
Composing it with an isomorphism `M ⊗ N ≅ 𝒪ₓ` gives a pairing
`AlgebraicGeometry.Scheme.Modules.tensorPairing` of a section of `M` and a section of `N` over an
open `U` with values in `Γ(X, U)`, and local surjectivity says that `1` is locally a finite sum of
such products. Since the local rings of `X` are local rings, one of the summands has a germ which
is a unit at any prescribed point, and shrinking to a basic open set makes that product itself a
unit: this is `AlgebraicGeometry.Scheme.Modules.exists_tensorPairing_eq_one`.

The second half is formal. Two sections `m` of `M` and `n` of `N` over `W` whose product is `1`
give a morphism `𝒪_W ⟶ M|_W`, multiplication by `m`, and a morphism `M|_W ⟶ 𝒪_W`, pairing with
`n`, whose composite is the identity of `𝒪_W`. A split monomorphism from the tensor unit to an
invertible object of a monoidal category is an isomorphism
(`CategoryTheory.MonoidalCategory.isIso_of_comp_eq_id`), and `M|_W` is invertible because the
pullback of an invertible sheaf of modules is invertible.

## Main declarations

- `SheafOfModules.tensorPresheafHom`: the comparison morphism from the sectionwise tensor product
  of the underlying presheaves of modules of `F` and `G` to the underlying presheaf of modules of
  `F ⊗ G`, together with `SheafOfModules.w_toPresheaf_map_tensorPresheafHom`, the statement that
  it becomes an isomorphism after sheafification.
- `AlgebraicGeometry.Scheme.Modules.tensorPairing`: the pairing on sections determined by an
  isomorphism `M ⊗ N ≅ 𝒪ₓ`.
- `SheafOfModules.Invertible.exists_isIso_unitSmulRestrictHom`: **an invertible sheaf of modules
  on a scheme is trivialised near every point by an explicit section**, multiplication by which
  is an isomorphism `𝒪_W ≅ M|_W`.
- `SheafOfModules.Invertible.isLocallyFree` and `SheafOfModules.Invertible.isFiniteType`: **an
  invertible sheaf of modules on a scheme is a line bundle**, in the sense used elsewhere in the
  project, and `SheafOfModules.Invertible.isCoherent`: it is therefore coherent.
- `SheafOfModules.Invertible.exists_restrict_iso_unit`: the same statement in the explicit local
  form, an isomorphism `M|_W ≅ 𝒪_W`.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj_of_invertible`,
  `isFiniteType_tensorObj_of_invertible` and `isCoherent_tensorObj_of_invertible`: **tensoring
  by an invertible sheaf of modules preserves quasi-coherence, being of finite type, and
  coherence.**

Invertibility of the second factor is a deliberate simplification in the last three statements.
Both halves hold for a general second factor — a tensor product of quasi-coherent sheaves of
modules is quasi-coherent, and a tensor product of sheaves of finite type is of finite type —
but the quasi-coherent half in that generality needs the comparison `(M ⊗ N)~ ≅ M~ ⊗ N~` on
affines, which is not available here and is not needed by Snapper's theorem. For an invertible
second factor local triviality replaces it.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite TensorProduct

universe v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

variable (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))

/-- The underlying presheaf of modules of a sheaf of modules, spelled as a presheaf of modules
over the underlying presheaf of rings of `R`, so that the monoidal structure of
`PresheafOfModules` is found by instance resolution. -/
abbrev presheafOfModules : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (SheafOfModules.forget _).obj F

/-- **The tensor product of two sheaves of modules is the sheafification of the sectionwise
tensor product** of the underlying presheaves of modules:

```
a (F₀ ⊗ G₀) --μ⁻¹--> a F₀ ⊗ a G₀ --ε ⊗ ε--> F ⊗ G
```

where `F₀` is the underlying presheaf of modules of `F`, `a` is sheafification, `μ` is its
monoidal structure map and `ε` is the counit of the sheafification adjunction.

The counit isomorphism `a F₀ ≅ F` is written out rather than named, because the open pull request
#723 declares it as `SheafOfModules.sheafificationObjIso` in
`WeilConjectures/AlgebraicGeometry/Modules/Sheafification.lean`, which is its proper home; issue
928 will move the material below there. -/
noncomputable def tensorSheafificationIso :
    (sheafification R).obj (presheafOfModules F ⊗ presheafOfModules G) ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (sheafification R) _ _).symm ≪≫
    tensorIso
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).counit).app F)
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).counit).app G)

/-- The canonical morphism from the sectionwise tensor product of the underlying presheaves of
modules of `F` and `G` to the underlying presheaf of modules of `F ⊗ G`. It is the transpose of
`SheafOfModules.tensorSheafificationIso` under the sheafification adjunction, so that the square

```
     F₀ ⊗ G₀ --tensorPresheafHom--> (F ⊗ G)₀
        |                              ‖
  toSheafify                           ‖
        |                              ‖
        v                              ‖
   a (F₀ ⊗ G₀) --tensorSheafificationIso--> F ⊗ G
```

commutes; this is `SheafOfModules.toPresheaf_map_tensorPresheafHom`. -/
noncomputable def tensorPresheafHom :
    presheafOfModules F ⊗ presheafOfModules G ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).obj
          (presheafOfModules (F ⊗ G)) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).homEquiv _ _
      (tensorSheafificationIso F G).hom

lemma toPresheaf_map_tensorPresheafHom :
    (PresheafOfModules.toPresheaf _).map (tensorPresheafHom F G) =
      CategoryTheory.toSheafify J (presheafOfModules F ⊗ presheafOfModules G).presheaf ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          (tensorSheafificationIso F G).hom := rfl

/-- The comparison morphism from the sectionwise tensor product to the tensor product becomes an
isomorphism after sheafification; in particular it is locally bijective. -/
lemma w_toPresheaf_map_tensorPresheafHom :
    J.W ((PresheafOfModules.toPresheaf _).map (tensorPresheafHom F G)) := by
  have h : J.W ((SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      PresheafOfModules.toPresheaf _).map (tensorSheafificationIso F G).hom) :=
    J.W.of_isIso _
  rw [toPresheaf_map_tensorPresheafHom]
  exact J.W.comp_mem _ _ (J.W_toSheafify _) h

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

instance (U : X.Opens) (M : X.Modules) :
    Module Γ(X, U) ((SheafOfModules.presheafOfModules M).obj (op U)) :=
  inferInstanceAs (Module Γ(X, U) Γ(M, U))

variable (e : M ⊗ N ≅ SheafOfModules.unit X.ringCatSheaf)

/-- The pairing of sections of `M` and of `N` over an open `U` determined by an isomorphism
`e : M ⊗ N ≅ 𝒪_X`: a section of `M` and a section of `N` over `U` have a product in `Γ(X, U)`,
obtained by pushing their tensor product through the comparison morphism
`SheafOfModules.tensorPresheafHom` and then through `e`:

```
Γ(M, U) × Γ(N, U) --⊗ₜ--> Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)
                                        |
                            tensorPresheafHom
                                        |
                                        v
                       Γ(X, U) <--e--  Γ(M ⊗ N, U)
```
-/
noncomputable def tensorPairing (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  LinearMap.compr₂ (TensorProduct.mk Γ(X, U) Γ(M, U) Γ(N, U))
    { toFun := fun t ↦ Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom t)
      map_add' := fun t t' ↦ by rw [map_add, map_add]
      map_smul' := fun r t ↦ by rw [RingHom.id_apply, _root_.map_smul, Hom.app_smul] }

variable {e}

lemma tensorPairing_apply (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    tensorPairing e U m n =
      Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom
        (m ⊗ₜ[Γ(X, U)] n)) :=
  rfl

lemma tensorPairing_tmul (U : X.Opens) (t : Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) :
    Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom t) =
      TensorProduct.lift (tensorPairing e U) t := by
  induction t with
  | zero => simp
  | tmul m n => rfl
  | add t t' h h' => rw [map_add, map_add, map_add, h, h']

/-- The pairing of sections is compatible with restriction to a smaller open subset. -/
lemma map_tensorPairing {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    X.presheaf.map i.op (tensorPairing e U m n) =
      tensorPairing e V (M.presheaf.map i.op m) (N.presheaf.map i.op n) := by
  rw [tensorPairing_apply, tensorPairing_apply]
  have h₁ := CategoryTheory.congr_fun ((Hom.mapPresheaf e.hom).naturality i.op)
    (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom (m ⊗ₜ[Γ(X, U)] n))
  have h₂ := PresheafOfModules.naturality_apply (SheafOfModules.tensorPresheafHom M N) i.op
    (m ⊗ₜ[Γ(X, U)] n)
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at h₁
  refine h₁.symm.trans ?_
  exact congrArg (ConcreteCategory.hom (Hom.app e.hom V)) h₂.symm

/-- **Any point has a neighbourhood on which `M` and `N` have sections pairing to `1`.** -/
lemma exists_tensorPairing_eq_one (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ (m : Γ(M, V)) (n : Γ(N, V)), tensorPairing e V m n = 1 := by
  have h1 : TopCat.Presheaf.IsLocallySurjective
      ((PresheafOfModules.toPresheaf _).map (SheafOfModules.tensorPresheafHom M N)) :=
    (SheafOfModules.w_toPresheaf_map_tensorPresheafHom M N).isLocallySurjective
  obtain ⟨V, hVle, ⟨s, hs⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).1 h1 ⊤ (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) x trivial
  have key : TensorProduct.lift (tensorPairing e V) s = 1 := by
    rw [← tensorPairing_tmul]
    have hs' : ((SheafOfModules.tensorPresheafHom M N).app (op V)).hom s =
        (M ⊗ N).presheaf.map (homOfLE hVle).op (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) := hs
    have hnat := CategoryTheory.congr_fun ((Hom.mapPresheaf e.hom).naturality (homOfLE hVle).op)
      (Hom.app e.inv ⊤ (1 : Γ(X, ⊤)))
    simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hnat
    have hone : Hom.app e.hom ⊤ (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app,
        ConcreteCategory.id_apply]
    rw [hs', hnat, hone]
    exact (X.presheaf.map (homOfLE hVle).op).hom.map_one
  obtain ⟨t, key⟩ : ∃ t : Γ(M, V) ⊗[Γ(X, V)] Γ(N, V),
      TensorProduct.lift (tensorPairing e V) t = 1 := ⟨s, key⟩
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  rw [hS, map_sum] at key
  simp only [TensorProduct.lift.tmul] at key
  have hgerm : IsUnit (∑ p ∈ S, X.presheaf.germ V x hxV (tensorPairing e V p.1 p.2)) := by
    rw [← map_sum, key, map_one]
    exact isUnit_one
  obtain ⟨p, -, hp⟩ := IsLocalRing.exists_of_isUnit_sum hgerm
  have hunit : IsUnit (X.presheaf.map
      (homOfLE (X.basicOpen_le (tensorPairing e V p.1 p.2))).op (tensorPairing e V p.1 p.2)) :=
    X.toRingedSpace.isUnit_res_basicOpen _
  obtain ⟨u, hu⟩ := hunit
  refine ⟨X.basicOpen (tensorPairing e V p.1 p.2),
    (Scheme.mem_basicOpen X _ x hxV).2 hp,
    M.presheaf.map (homOfLE (X.basicOpen_le _)).op p.1,
    ((u⁻¹ : (Γ(X, X.basicOpen (tensorPairing e V p.1 p.2)))ˣ) :
      Γ(X, X.basicOpen (tensorPairing e V p.1 p.2))) •
      N.presheaf.map (homOfLE (X.basicOpen_le _)).op p.2, ?_⟩
  rw [_root_.map_smul, ← map_tensorPairing, ← hu, smul_eq_mul]
  exact u.inv_mul

section Restrict

variable (e) {W : X.Opens}

/-- Multiplication by the restriction of a section `m` of `M` over `W` to a smaller open `V`. -/
noncomputable def smulSection (m : Γ(M, W)) (V : X.Opens) (hV : V ≤ W) : Γ(X, V) →+ Γ(M, V) :=
  AddMonoidHom.mk' (fun r ↦ r • M.presheaf.map (homOfLE hV).op m) (fun r r' ↦ add_smul r r' _)

lemma smulSection_smul (m : Γ(M, W)) (V : X.Opens) (hV : V ≤ W) (r z : Γ(X, V)) :
    smulSection m V hV (r • z) = r • smulSection m V hV z :=
  mul_smul r z _

lemma map_smulSection (m : Γ(M, W)) {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ W) (i : V' ⟶ V)
    (r : Γ(X, V)) :
    M.presheaf.map i.op (smulSection m V hV r) = smulSection m V' hV' (X.presheaf.map i.op r) := by
  rw [smulSection, smulSection]
  simp only [AddMonoidHom.mk'_apply]
  rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

/-- Pairing with the restriction of a section `n` of `N` over `W` to a smaller open `V`. -/
noncomputable def pairSection (n : Γ(N, W)) (V : X.Opens) (hV : V ≤ W) : Γ(M, V) →+ Γ(X, V) :=
  AddMonoidHom.mk' (fun z ↦ tensorPairing e V z (N.presheaf.map (homOfLE hV).op n))
    (fun z z' ↦ by rw [map_add, LinearMap.add_apply])

lemma pairSection_smul (n : Γ(N, W)) (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V)) (z : Γ(M, V)) :
    pairSection e n V hV (r • z) = r • pairSection e n V hV z := by
  rw [pairSection]
  simp only [AddMonoidHom.mk'_apply]
  rw [_root_.map_smul, LinearMap.smul_apply]

lemma map_pairSection (n : Γ(N, W)) {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ W) (i : V' ⟶ V)
    (z : Γ(M, V)) :
    X.presheaf.map i.op (pairSection e n V hV z) =
      pairSection e n V' hV' (M.presheaf.map i.op z) := by
  rw [pairSection, pairSection]
  simp only [AddMonoidHom.mk'_apply]
  rw [map_tensorPairing, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 3

lemma pairSection_smulSection (m : Γ(M, W)) (n : Γ(N, W)) (h : tensorPairing e W m n = 1)
    (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V)) :
    pairSection e n V hV (smulSection m V hV r) = r := by
  rw [smulSection]
  simp only [AddMonoidHom.mk'_apply]
  rw [pairSection_smul, pairSection]
  simp only [AddMonoidHom.mk'_apply, smul_eq_mul]
  rw [← map_tensorPairing, h, map_one, mul_one]

/-- Multiplication by a section `m` of `M` over `W`, as a morphism `𝒪_X|_W ⟶ M|_W` of sheaves
of modules on the open subscheme `W`. -/
noncomputable def smulRestrictHom (m : Γ(M, W)) :
    restrict (SheafOfModules.unit X.ringCatSheaf) W.ι ⟶ restrict M W.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimage <|
    PresheafOfModules.homMk
      { app := fun U' ↦ AddCommGrpCat.ofHom (smulSection m (W.ι ''ᵁ U'.unop) (W.ι_image_le _))
        naturality := fun {U' V'} f ↦ by
          ext r
          exact (map_smulSection m _ _ _ r).symm }
      (fun U' r z ↦ smulSection_smul m _ _ ((W.ι.appIso U'.unop).inv r) z)

/-- Pairing with a section `n` of `N` over `W`, as a morphism `M|_W ⟶ 𝒪_X|_W`. -/
noncomputable def pairRestrictHom (n : Γ(N, W)) :
    restrict M W.ι ⟶ restrict (SheafOfModules.unit X.ringCatSheaf) W.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimage <|
    PresheafOfModules.homMk
      { app := fun U' ↦ AddCommGrpCat.ofHom (pairSection e n (W.ι ''ᵁ U'.unop) (W.ι_image_le _))
        naturality := fun {_U' _V'} f ↦ by
          ext z
          exact (map_pairSection e n (W.ι_image_le _) (W.ι_image_le _)
            (W.ι.opensFunctor.map f.unop) z).symm }
      (fun U' r z ↦ pairSection_smul e n _ _ ((W.ι.appIso U'.unop).inv r) z)

/-- If the sections `m` of `M` and `n` of `N` over `W` pair to `1`, then multiplication by `m`
is a split monomorphism `𝒪_X|_W ⟶ M|_W`. -/
lemma smulRestrictHom_comp_pairRestrictHom (m : Γ(M, W)) (n : Γ(N, W))
    (h : tensorPairing e W m n = 1) :
    smulRestrictHom m ≫ pairRestrictHom e n = 𝟙 _ := by
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  ext U' r
  exact pairSection_smulSection e m n h _ _ r

/-- **Multiplication by a section `m` of `M` over `W`**, as a morphism `𝒪_W ⟶ M|_W` of sheaves
of modules on the open subscheme `W`. This is the morphism `SheafOfModules.unitHomEquiv.symm`
would produce from the section of `M|_W` determined by `m`; it is built by hand because the
scalars on `M.restrict W.ι` are twisted by `(W.ι.appIso _).inv`, which no amount of unfolding
identifies with the identity. -/
noncomputable def unitSmulRestrictHom (m : Γ(M, W)) :
    SheafOfModules.unit W.toScheme.ringCatSheaf ⟶ restrict M W.ι :=
  (restrictUnitIso W.ι).inv ≫ smulRestrictHom m

end Restrict

/-- The tensor unit of the category of `𝒪_W`-modules on an open subscheme `W` of `X` is the
restriction of the structure sheaf of `X`. -/
noncomputable def tensorUnitRestrictIso (W : X.Opens) :
    𝟙_ W.toScheme.Modules ≅ restrict (SheafOfModules.unit X.ringCatSheaf) W.ι :=
  SheafOfModules.tensorUnitIso W.toScheme.sheaf ≪≫ (restrictUnitIso W.ι).symm

/-- **An invertible sheaf of modules on a scheme is locally trivial, with an explicit
trivialising section**: every point `x` has an open neighbourhood `W` carrying a section `m` of
`M` such that multiplication by `m` is an isomorphism `𝒪_W ≅ M|_W`. In other words `m` is a
generator of `M` over `W`. -/
theorem _root_.SheafOfModules.Invertible.exists_isIso_unitSmulRestrictHom {M : X.Modules}
    (hM : M.Invertible) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ ∃ m : Γ(M, W), IsIso (unitSmulRestrictHom m) := by
  obtain ⟨N, ⟨e₀⟩⟩ := SheafOfModules.invertible_iff_exists.{u, u, u}.1 hM
  obtain ⟨W, hxW, m, n, h⟩ :=
    exists_tensorPairing_eq_one (e := e₀ ≪≫ SheafOfModules.tensorUnitIso X.sheaf) x
  refine ⟨W, hxW, m, ?_⟩
  have hMW : (M.restrict W.ι).Invertible :=
    (hM.pullback W.ι).of_iso ((restrictFunctorIsoPullback W.ι).app M).symm
  obtain ⟨N', ⟨eW⟩⟩ : ∃ N' : W.toScheme.Modules,
      Nonempty (M.restrict W.ι ⊗ N' ≅ 𝟙_ W.toScheme.Modules) :=
    SheafOfModules.invertible_iff_exists.{u, u, u}.1 hMW
  have key : ((tensorUnitRestrictIso W).hom ≫ smulRestrictHom m) ≫
      (pairRestrictHom (e₀ ≪≫ SheafOfModules.tensorUnitIso X.sheaf) n ≫
        (tensorUnitRestrictIso W).inv) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (smulRestrictHom m),
      smulRestrictHom_comp_pairRestrictHom _ m n h, Category.id_comp,
      (tensorUnitRestrictIso W).hom_inv_id]
  have hcomp : IsIso ((tensorUnitRestrictIso W).hom ≫ smulRestrictHom m) :=
    MonoidalCategory.isIso_of_comp_eq_id eW (β_ N' (M.restrict W.ι) ≪≫ eW) key
  have hfac : unitSmulRestrictHom m = (SheafOfModules.tensorUnitIso W.toScheme.sheaf).inv ≫
      (tensorUnitRestrictIso W).hom ≫ smulRestrictHom m := by
    rw [tensorUnitRestrictIso, Iso.trans_hom, Category.assoc, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp, Iso.symm_hom, unitSmulRestrictHom]
  rw [hfac]
  infer_instance

/-- **An invertible sheaf of modules on a scheme is locally trivial**: every point has an open
neighbourhood on which the sheaf is isomorphic to the structure sheaf. -/
theorem _root_.SheafOfModules.Invertible.exists_restrict_iso_unit {M : X.Modules}
    (hM : M.Invertible) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧
      Nonempty (M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  obtain ⟨W, hxW, m, hm⟩ := hM.exists_isIso_unitSmulRestrictHom x
  exact ⟨W, hxW, ⟨(asIso (unitSmulRestrictHom m)).symm⟩⟩

/-- An invertible sheaf of modules on a scheme is locally isomorphic to the tensor unit. -/
theorem _root_.SheafOfModules.Invertible.exists_restrict_iso_tensorUnit {M : X.Modules}
    (hM : M.Invertible) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ Nonempty (M.restrict W.ι ≅ 𝟙_ W.toScheme.Modules) := by
  obtain ⟨W, hxW, ⟨i⟩⟩ := hM.exists_restrict_iso_unit x
  exact ⟨W, hxW, ⟨i ≪≫ (SheafOfModules.tensorUnitIso W.toScheme.sheaf).symm⟩⟩

section LocallyFree

open TopologicalSpace

/-- Transporting generating sections along an isomorphism of sheaves of modules preserves being
a basis. -/
lemma _root_.SheafOfModules.GeneratingSections.isIso_π_equivOfIso {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {P Q : SheafOfModules.{u} R} (i : P ≅ Q) (σ : P.GeneratingSections) [IsIso σ.π] :
    IsIso (SheafOfModules.GeneratingSections.equivOfIso i σ).π := by
  have h : (SheafOfModules.GeneratingSections.equivOfIso i σ).π = σ.π ≫ i.hom :=
    SheafOfModules.GeneratingSections.ofEpi_π σ i.hom
  rw [h]
  infer_instance

/-- The section `m` of `M` over `W`, seen as a family of generating sections of `M|_W` indexed by
a one-point type, when multiplication by `m` is an isomorphism `𝒪_W ≅ M|_W`. -/
noncomputable def generatingSectionsOfIsIso {W : X.Opens} (m : Γ(M, W))
    [IsIso (unitSmulRestrictHom m)] : (M.restrict W.ι).GeneratingSections :=
  SheafOfModules.GeneratingSections.equivOfIso
    (SheafOfModules.freeUniqueIso PUnit.{u + 1} ≪≫ asIso (unitSmulRestrictHom m))
    (SheafOfModules.free.generatingSections PUnit.{u + 1})

instance {W : X.Opens} (m : Γ(M, W)) [IsIso (unitSmulRestrictHom m)] :
    IsIso (generatingSectionsOfIsIso m).π :=
  SheafOfModules.GeneratingSections.isIso_π_equivOfIso _ _

instance {W : X.Opens} (m : Γ(M, W)) [IsIso (unitSmulRestrictHom m)] :
    (generatingSectionsOfIsIso m).IsFiniteType :=
  ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩

variable (M)

/-- Generating sections of `M|_W` which form a basis stay a basis when transported to the
restriction of `M` to the slice site over `W`. -/
lemma isIso_overGeneratingSections_π {W : X.Opens} (G : (M.restrict W.ι).GeneratingSections)
    (hG : IsIso G.π) : IsIso (overGeneratingSections M W G).π := by
  have := hG
  exact SheafOfModules.GeneratingSections.isIso_π_equivOfIso _ _

/-- Local generators of `M` attached to generating sections over each member of an open cover. -/
noncomputable def localGeneratorsDataOfCover {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (G : ∀ i, (M.restrict (U i).ι).GeneratingSections) :
    SheafOfModules.LocalGeneratorsData.{u} M :=
  .mk (M := M) ι U ((Opens.coversTop_iff _ U).mpr hU)
    fun i ↦ overGeneratingSections M (U i) (G i)

lemma isLocallyFreeData_localGeneratorsDataOfCover {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (G : ∀ i, (M.restrict (U i).ι).GeneratingSections)
    (hG : ∀ i, IsIso (G i).π) :
    (localGeneratorsDataOfCover.{u} M U hU G).IsLocallyFreeData where
  isIso i := isIso_overGeneratingSections_π M (G i) (hG i)

/-- **Being locally free is local**: a sheaf of modules which over each member of an open cover
has generating sections forming a basis is locally free. -/
theorem isLocallyFree_of_generatingSections {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (G : ∀ i, (M.restrict (U i).ι).GeneratingSections) (hG : ∀ i, IsIso (G i).π) :
    M.IsLocallyFree :=
  have := isLocallyFreeData_localGeneratorsDataOfCover.{u} M U hU G hG
  (localGeneratorsDataOfCover.{u} M U hU G).isLocallyFree

variable {M}

/-- **An invertible sheaf of modules on a scheme is a line bundle**: it is locally free.

Together with `SheafOfModules.Invertible.isFiniteType` this is the project's spelling of "`M` is
a line bundle on `X`", as used for instance by the projection formula. -/
theorem _root_.SheafOfModules.Invertible.isLocallyFree {M : X.Modules} (hM : M.Invertible) :
    M.IsLocallyFree := by
  choose W hW m hm using hM.exists_isIso_unitSmulRestrictHom
  have hU : IsOpenCover W :=
    .mk (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hW x⟩)
  exact isLocallyFree_of_generatingSections M W hU (fun x ↦ generatingSectionsOfIsIso (m x))
    fun x ↦ inferInstance

/-- **An invertible sheaf of modules on a scheme is of finite type**: locally it is generated by
a single section. -/
theorem _root_.SheafOfModules.Invertible.isFiniteType {M : X.Modules} (hM : M.Invertible) :
    M.IsFiniteType := by
  choose W hW m hm using hM.exists_isIso_unitSmulRestrictHom
  have hU : IsOpenCover W :=
    .mk (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hW x⟩)
  exact isFiniteType_of_generatingSections M W hU (fun x ↦ generatingSectionsOfIsIso (m x))
    fun x ↦ inferInstance

/-- **An invertible sheaf of modules on a scheme is coherent**: it is locally free, hence
quasi-coherent, and of finite type. -/
theorem _root_.SheafOfModules.Invertible.isCoherent {M : X.Modules} (hM : M.Invertible) :
    M.IsCoherent :=
  have := hM.isLocallyFree
  have := hM.isFiniteType
  inferInstance

end LocallyFree

section TensorInvertible

open TopologicalSpace

variable {L : X.Modules}

/-- A trivialisation of `L` over an open `W` restricts to a trivialisation over a smaller
open `V`. -/
noncomputable def restrictIsoTensorUnitOfLE {W : X.Opens}
    (e : L.restrict W.ι ≅ 𝟙_ W.toScheme.Modules) {V : X.Opens} (h : V ≤ W) :
    L.restrict V.ι ≅ 𝟙_ V.toScheme.Modules :=
  (restrictRestrictIso L h).symm ≪≫ (restrictFunctor' (X.homOfLE h)).mapIso e ≪≫
    (Functor.Monoidal.εIso (restrictFunctor (X.homOfLE h))).symm

/-- **An invertible sheaf of modules on a scheme is trivial over each member of some cover of
`X` by affine opens**: the trivialising opens given by
`SheafOfModules.Invertible.exists_restrict_iso_tensorUnit` are refined by affine opens, over
which the trivialisation restricts. -/
theorem _root_.SheafOfModules.Invertible.exists_isAffineOpenCover_restrict_iso_tensorUnit
    (hL : L.Invertible) :
    ∃ (ι : Type u) (U : ι → X.Opens), IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
      ∀ i, Nonempty (L.restrict (U i).ι ≅ 𝟙_ (U i).toScheme.Modules) := by
  choose W hxW hW using hL.exists_restrict_iso_tensorUnit
  choose κ hκ hWeq using fun x : X ↦ Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (W x)
  have hle (j : Σ x : X, κ x) : (j.2 : X.Opens) ≤ W j.1 := by
    rw [hWeq j.1]
    exact le_sSup j.2.2
  refine ⟨Σ x : X, κ x, fun j ↦ (j.2 : X.Opens), ?_, fun j ↦ hκ _ j.2.2, fun j ↦ ⟨?_⟩⟩
  · have hcov : ⨆ x : X, W x = ⊤ := eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩
    rw [IsOpenCover, iSup_sigma, ← hcov]
    exact iSup_congr fun x ↦ by rw [hWeq x, sSup_eq_iSup']
  · exact restrictIsoTensorUnitOfLE (hW j.1).some (hle j)

/-- **Tensoring a quasi-coherent sheaf of modules with an invertible one preserves
quasi-coherence.** Over an affine open trivialising `L` the restriction of `F ⊗ L` is
isomorphic to that of `F`, and quasi-coherence is local on the base. -/
theorem isQuasicoherent_tensorObj_of_invertible (F : X.Modules) [F.IsQuasicoherent]
    (hL : L.Invertible) : (F ⊗ L).IsQuasicoherent := by
  obtain ⟨ι, U, hU, hU', e⟩ := hL.exists_isAffineOpenCover_restrict_iso_tensorUnit
  refine isQuasicoherent_of_isAffineOpenCover _ U hU hU' fun i ↦ ?_
  exact (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso
    (restrictTensorIsoOfRestrictIsoTensorUnit (U i).ι F (e i).some).symm inferInstance

/-- **Tensoring a sheaf of modules of finite type with an invertible one preserves being of
finite type.** Over an open trivialising `L` the restriction of `F ⊗ L` is isomorphic to that of
`F`, so the generating sections of `F` transport, and being of finite type is local on the
base. -/
theorem isFiniteType_tensorObj_of_invertible (F : X.Modules) [F.IsFiniteType]
    (hL : L.Invertible) : (F ⊗ L).IsFiniteType := by
  choose W hxW hW using hL.exists_restrict_iso_tensorUnit
  have hWcover : IsOpenCover W := .mk (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩)
  obtain ⟨ι, U, r, G, hU, -, hUle, hG⟩ := exists_isOpenCover_generatingSections_le F W hWcover
  have e (i : ι) : (F ⊗ L).restrict (U i).ι ≅ F.restrict (U i).ι :=
    restrictTensorIsoOfRestrictIsoTensorUnit (U i).ι F
      (restrictIsoTensorUnitOfLE (hW (r i)).some (hUle i))
  exact isFiniteType_of_generatingSections _ U hU
    (fun i ↦ SheafOfModules.GeneratingSections.equivOfIso (e i).symm (G i))
    fun i ↦ ⟨(hG i).finite⟩

/-- **Tensoring a coherent sheaf of modules with an invertible one preserves coherence.** -/
theorem isCoherent_tensorObj_of_invertible (F : X.Modules) [F.IsCoherent] (hL : L.Invertible) :
    (F ⊗ L).IsCoherent := by
  -- `SheafOfModules.IsCoherent` has no explicit fields: it is `IsQuasicoherent` together with
  -- `IsFiniteType`, and instance search assembles it out of the two halves below.
  have := isQuasicoherent_tensorObj_of_invertible F hL
  have := isFiniteType_tensorObj_of_invertible F hL
  constructor

end TensorInvertible

end AlgebraicGeometry.Scheme.Modules
