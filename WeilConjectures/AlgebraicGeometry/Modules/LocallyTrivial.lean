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
- `AlgebraicGeometry.Scheme.Modules.bijective_smulSection` and
  `AlgebraicGeometry.Scheme.Modules.exists_map_leTop_eq_smul`: over a trivialising open `W`,
  multiplication by the trivialising section `m` is a bijection on sections, so every global
  section of `M` restricts to `g • m` for a function `g ∈ Γ(X, W)`.
- `AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_notMem_basicOpen`: **vanishing of a section
  of a line bundle is vanishing of its local equation**: written as `g • m` on a trivialising
  open, a section vanishes at a point of `W` exactly outside the basic open subset of `g`.

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
monoidal structure map and `ε` is the counit of the sheafification adjunction,
`SheafOfModules.sheafificationObjIso`. -/
noncomputable def tensorSheafificationIso :
    (sheafification R).obj (presheafOfModules F ⊗ presheafOfModules G) ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (sheafification R) _ _).symm ≪≫
    tensorIso (sheafificationObjIso R F) (sheafificationObjIso R G)

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

`AlgebraicGeometry.Scheme.Modules.pairingHom` is the same product of two *global* sections, taken
as an endomorphism of the structure sheaf rather than as a global function; that is the form which
pulls back along a morphism of schemes, which a section does not. -/
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

/-- Multiplication by a section over the trivialising open itself is multiplication by that
section. -/
@[simp]
lemma smulSection_le_rfl (m : Γ(M, W)) (r : Γ(X, W)) : smulSection m W le_rfl r = r • m := by
  rw [smulSection]
  simp

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

/-- **An invertible sheaf of modules has non-zero stalks.** -/
theorem _root_.SheafOfModules.Invertible.nontrivial_stalk {M : X.Modules} (hM : M.Invertible)
    (x : X) : Nontrivial (M.presheaf.stalk x) := by
  -- if the germ of `m` at `x` vanished, then the sections `m` of `M` and `n` of `N` with
  -- `m · n = 1` supplied by `exists_tensorPairing_eq_one` would pair to `0` on a neighbourhood
  -- of `x`, making `1 = 0` in the local ring of `X` at `x`
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  obtain ⟨N, ⟨e₀⟩⟩ := SheafOfModules.invertible_iff_exists.{u, u, u}.1 hM
  obtain ⟨V, hxV, m, n, hmn⟩ :=
    exists_tensorPairing_eq_one (e := e₀ ≪≫ SheafOfModules.tensorUnitIso X.sheaf) x
  have hgerm : M.presheaf.germ V x hxV m = M.presheaf.germ V x hxV 0 := Subsingleton.elim _ _
  obtain ⟨W, hxW, iWV, iWV', hW⟩ := M.presheaf.germ_eq x hxV hxV m 0 hgerm
  have hzero : M.presheaf.map iWV.op m = 0 := by rw [hW, map_zero]
  have key : (1 : Γ(X, W)) = 0 := by
    have h := map_tensorPairing (e := e₀ ≪≫ SheafOfModules.tensorUnitIso X.sheaf) iWV m n
    rwa [hmn, hzero, map_one, map_zero, LinearMap.zero_apply] at h
  exact one_ne_zero (by rw [← map_one (X.presheaf.germ W x hxW).hom, key, map_zero])

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

section Trivialisation

variable {L : X.Modules} {W : X.Opens}

/-- **A trivialising section generates the sections over every smaller open subset.** If
multiplication by `m : Γ(L, W)` is an isomorphism `𝒪_W ≅ L|_W`, then for every open `V ≤ W`
multiplication by the restriction of `m` is a bijection of `Γ(X, V)` onto `Γ(L, V)`. -/
theorem bijective_smulSection (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    {V : X.Opens} (hV : V ≤ W) :
    Function.Bijective (smulSection m V hV) := by
  have hiso : IsIso (smulRestrictHom m) := by
    have h : smulRestrictHom m = (restrictUnitIso W.ι).hom ≫ unitSmulRestrictHom m := by
      rw [unitSmulRestrictHom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h]
    infer_instance
  obtain ⟨V', rfl⟩ : ∃ V' : W.toScheme.Opens, W.ι ''ᵁ V' = V :=
    ⟨W.ι ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.2 hV]⟩
  exact ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation W.toScheme.ringCatSheaf (op V')).map (smulRestrictHom m))

/-- **A global section is a multiple of a trivialising section over the trivialising open.** If
multiplication by `m : Γ(L, W)` is an isomorphism `𝒪_W ≅ L|_W`, then the restriction to `W` of a
global section `s` of `L` is `g • m` for a function `g ∈ Γ(X, W)`. -/
theorem exists_map_leTop_eq_smul (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)] (s : Γ(L, ⊤)) :
    ∃ g : Γ(X, W), L.presheaf.map W.leTop.op s = g • m := by
  obtain ⟨g, hg⟩ := (bijective_smulSection m le_rfl).2 (L.presheaf.map W.leTop.op s)
  exact ⟨g, by rw [← hg, smulSection_le_rfl]⟩

/-- **A trivialising section generates every stalk over the trivialising open.** -/
theorem span_germ_eq_top (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)] {x : X} (hx : x ∈ W) :
    Submodule.span (X.presheaf.stalk x) {L.presheaf.germ W x hx m} = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨V, hxV, t, rfl⟩ := L.presheaf.exists_germ_eq y
  have hxV' : x ∈ V ⊓ W := ⟨hxV, hx⟩
  rw [← L.presheaf.germ_res_apply (homOfLE (inf_le_left : V ⊓ W ≤ V)) x hxV' t]
  obtain ⟨r, hr⟩ := (bijective_smulSection m (V := V ⊓ W) inf_le_right).2
    (L.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op t)
  rw [← hr]
  change L.presheaf.germ (V ⊓ W) x hxV' (r • L.presheaf.map (homOfLE inf_le_right).op m) ∈ _
  rw [germ_smul L x hxV' r, L.presheaf.germ_res_apply]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **A trivialising section is a free generator of every stalk over the trivialising open**:
no nonzero element of the local ring kills it. -/
theorem eq_zero_of_smul_germ_eq_zero (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    {x : X} (hx : x ∈ W) {z : X.presheaf.stalk x} (hz : z • L.presheaf.germ W x hx m = 0) :
    z = 0 := by
  obtain ⟨V, hxV, r, rfl⟩ := X.presheaf.exists_germ_eq z
  have hxV' : x ∈ V ⊓ W := ⟨hxV, hx⟩
  rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : V ⊓ W ≤ V)) x hxV' r] at hz ⊢
  rw [← L.presheaf.germ_res_apply (homOfLE (inf_le_right : V ⊓ W ≤ W)) x hxV' m,
    ← germ_smul L x hxV'] at hz
  obtain ⟨V'', hxV'', i, i', hzz⟩ :=
    L.presheaf.germ_eq (U := V ⊓ W) (V := V ⊓ W) x hxV' hxV' _ 0 (by simpa using hz)
  rw [map_zero, Scheme.Modules.map_smul] at hzz
  have hreg : smulSection m V'' (i.le.trans inf_le_right)
      (X.presheaf.map i.op (X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op r)) = 0 := by
    rw [smulSection]
    simp only [AddMonoidHom.mk'_apply]
    rw [← hzz]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 2
  have := (bijective_smulSection m (V := V'') (i.le.trans inf_le_right)).1
    (hreg.trans (map_zero _).symm)
  rw [← X.presheaf.germ_res_apply i x hxV'' _, this, map_zero]

/-- **The bridge between vanishing and basic open subsets.** If `s` restricts to `g • m` on a
trivialising open `W`, then `s` vanishes at a point of `W` exactly when that point lies outside
the basic open subset of `g`.

This identifies `AlgebraicGeometry.Scheme.Modules.VanishesAt` for an invertible sheaf with the
hypothesis of
`AlgebraicGeometry.Scheme.Modules.isSMulRegular_iff_associatedPoints_subset_basicOpen`, and
generalises `AlgebraicGeometry.Scheme.Modules.vanishesAt_structureModules_iff`. -/
theorem vanishesAt_iff_notMem_basicOpen (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    (s : Γ(L, ⊤)) (g : Γ(X, W)) (hg : L.presheaf.map W.leTop.op s = g • m)
    {x : X} (hx : x ∈ W) :
    L.VanishesAt s x ↔ x ∉ X.basicOpen g := by
  have he : L.presheaf.germ ⊤ x trivial s
      = X.presheaf.germ W x hx g • L.presheaf.germ W x hx m := by
    rw [← L.presheaf.germ_res_apply W.leTop x hx s, hg, germ_smul L x hx]
  have hne : L.presheaf.germ W x hx m ≠ 0 := fun h0 ↦
    one_ne_zero (eq_zero_of_smul_germ_eq_zero m hx (by rw [h0, smul_zero]))
  have hnt : Nontrivial (L.presheaf.stalk x) := nontrivial_of_ne _ _ hne
  have hfin : Module.Finite (X.presheaf.stalk x) (L.presheaf.stalk x) :=
    ⟨span_germ_eq_top m hx ▸ Submodule.fg_span_singleton _⟩
  rw [vanishesAt_iff, he, Scheme.mem_basicOpen X g x hx]
  constructor
  · intro h hu
    obtain ⟨u, hu⟩ := hu
    have hmem := Submodule.smul_mem (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)))
      ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) h
    rw [smul_smul, ← hu, Units.inv_mul, one_smul] at hmem
    have hspan : Submodule.span (X.presheaf.stalk x) {L.presheaf.germ W x hx m} ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤ :=
      Submodule.span_le.2 (Set.singleton_subset_iff.2 hmem)
    rw [span_germ_eq_top m hx] at hspan
    exact absurd (le_antisymm le_top hspan)
      (Submodule.ideal_smul_top_lt_top (R := X.presheaf.stalk x)
        (M := L.presheaf.stalk x)
        (I := IsLocalRing.maximalIdeal (X.presheaf.stalk x)) le_rfl).ne
  · intro h
    exact Submodule.smul_mem_smul
      ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)) Submodule.mem_top


end Trivialisation

end AlgebraicGeometry.Scheme.Modules
