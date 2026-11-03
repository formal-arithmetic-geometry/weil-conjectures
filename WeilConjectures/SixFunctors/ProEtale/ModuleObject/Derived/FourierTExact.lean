/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSubcategories
public import WeilConjectures.AlgebraicGeometry.CondensedFourierPerverse.CondensedFourierPerverse
public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open StrictWeilCondensed
open PurityTransport

/-!
# Perverse t-exactness of the affine-line Fourier transform

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-fourier-transform/sec-perverse-t-exactness-of-the-fourier-transform/`
`sk-p-dl-a1-perverse/thm-a1-fourier-t-exact.md` (blueprint: thm-a1-fourier-t-exact).

The statement is made on strict condensed Weil complexes over the finite field
 datum. The displayed functors are strict Weil lifts of the two condensed
Fourier transforms and of the Tate tensor from `StrictWeilCondensed.tateComplex`;
all three are tied to their named geometric constructions by natural carrier
isomorphisms, including the canonical Weil structure of `lem-wft-fourier-weil`.
-/

/-- The upper perverse class on strict Weil pairs, tested on the recorded condensed
support class. The field hypotheses and `hk` are retained in this strict
wrapper interface. Elaboration selects the current predicate API first and retains
compatibility with the frozen interface snapshot, whose predicate also takes `hk`.
Source: [def-per-perverse-subcategories], [sk-def-sf-weil-complexes].
(blueprint: thm-a1-fourier-t-exact). -/
def strictPerverseLE (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Invertible (ell : k)]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] {g : X.left ≅ X.left} (n : ℤ) :
    ObjectProperty (StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj ell) g) := by
  first
  | exact fun K ↦ ∃ hK : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left) K.carrier.obj,
      CondensedPerverseLE ell X n ⟨K.carrier.obj, hK⟩
  | exact fun K ↦ ∃ hK : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left) K.carrier.obj,
      CondensedPerverseLE ell hk X n ⟨K.carrier.obj, hK⟩

/-- The lower perverse class on strict Weil pairs, tested on the recorded condensed
cosupport class. The field hypotheses and `hk` are retained in this strict
wrapper interface. Elaboration selects the current predicate API first and retains
compatibility with the frozen interface snapshot, whose predicate also takes `hk`.
Source: [def-per-perverse-subcategories], [sk-def-sf-weil-complexes].
(blueprint: thm-a1-fourier-t-exact). -/
def strictPerverseGE (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Invertible (ell : k)]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] {g : X.left ≅ X.left} (n : ℤ) :
    ObjectProperty (StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj ell) g) := by
  first
  | exact fun K ↦ ∃ hK : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left) K.carrier.obj,
      CondensedPerverseGE ell X n ⟨K.carrier.obj, hK⟩
  | exact fun K ↦ ∃ hK : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left) K.carrier.obj,
      CondensedPerverseGE ell hk X n ⟨K.carrier.obj, hK⟩

/-- The Weil perverse heart is the full subcategory cut out by the two recorded
classes. Source: [thm-a1-curve-perverse-heart].
(blueprint: thm-a1-fourier-t-exact). -/
abbrev strictPerverseHeart
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Invertible (ell : k)]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] {g : X.left ≅ X.left} :=
  ObjectProperty.FullSubcategory
    (fun K : StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj ell) g ↦
      strictPerverseLE ell hk 0 K ∧ strictPerverseGE ell hk 0 K)

/-- The carrier functor forgets the strict Weil structure and includes the
finite-Tor object into the ambient derived category.
Source: [sk-def-sf-weil-complexes] (blueprint: thm-a1-fourier-t-exact). -/
def strictCarrier
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}} {g : T ≅ T} :
    StrictWeilCondensed.Complex Λ g ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj Λ T)) :=
  StrictWeilCondensed.forget Λ g ⋙ ObjectProperty.ι _

/-- A strict lift is tied to the named geometric functor by a natural carrier
isomorphism. This records the action on morphisms and the canonical Weil
structure, rather than only an objectwise carrier equivalence.
Source: [lem-wft-fourier-weil] (blueprint: thm-a1-fourier-t-exact). -/
def isCarrierLiftNat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    {gX : X ≅ X} {gY : Y ≅ Y}
    (F : StrictWeilCondensed.Complex Λ gX ⥤
      StrictWeilCondensed.Complex Λ gY)
    (Φ : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (α : Φ ⋙ StrictWeilCondensed.action Λ gY ≅
      StrictWeilCondensed.action Λ gX ⋙ Φ) : Prop :=
  ∃ e : F ⋙ strictCarrier Λ ≅ strictCarrier Λ ⋙ Φ,
    ∀ K : StrictWeilCondensed.Complex Λ gX,
      ((StrictWeilCondensed.action Λ gY).map (e.hom.app K) ≫
        α.hom.app ((strictCarrier Λ).obj K) ≫
        Φ.map (((ObjectProperty.ι _).mapIso K.str).hom)) =
      (((ObjectProperty.ι _).mapIso (F.obj K).str).hom ≫ e.hom.app K)

/-- The tensor with the signed Tate line remains in the recorded Dctf class. This
membership is a named theorem so the strict functor below has concrete object data.
Source: [def-wf-tate-twist] (blueprint: thm-a1-fourier-t-exact). -/
theorem tateTensor_mem
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {T : Scheme.{u}} (r : ℤ)
    (K : ConstantModelConstructibleFiniteTor (c.obj ell) T) :
    (constantModelBoundedConstructible (c.obj ell) T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (c.obj ell) T)) L) (MonoidalCategory.tensorObj K.obj
        (StrictWeilCondensed.derivedTateLine ell c T r)) := by
  sorry

/-- The carrier functor used for the strict Tate lift, tensoring on the right by the
signed derived Tate line. Source: [def-wf-tate-twist] (blueprint: thm-a1-fourier-t-exact). -/
noncomputable def strictTateCarrier
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {T : Scheme.{u}} (r : ℤ) :
    ConstantModelConstructibleFiniteTor (c.obj ell) T ⥤
      ConstantModelConstructibleFiniteTor (c.obj ell) T :=
  ObjectProperty.lift _
    ((ObjectProperty.ι _) ⋙ MonoidalCategory.tensorRight
      (StrictWeilCondensed.derivedTateLine ell c T r))
    (fun K ↦ tateTensor_mem ell c r K)

/-- The canonical strict datum on the Tate tensor is the ambient tensor datum.
Source: [def-wf-tate-twist], [lem-wft-fourier-weil] (blueprint: thm-a1-fourier-t-exact). -/
noncomputable def strictTateDatum
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ)
    (K : StrictWeilCondensed.Complex (c.obj ell) g) :
    (StrictWeilCondensed.smallAction (c.obj ell) g).obj
        (strictTateCarrier ell c r |>.obj K.carrier) ≅
      strictTateCarrier ell c r |>.obj K.carrier :=
  ObjectProperty.isoMk _
    (StrictWeilCondensed.tensorDatum (c.obj ell) g
      ((ObjectProperty.ι _).mapIso K.str)
      (StrictWeilCondensed.tateDatum ell c g r))

/-- The ambient tensorator component restricted to the strict Dctf carrier.
Source: [def-wf-tate-twist] (blueprint: thm-a1-fourier-t-exact). -/
noncomputable def strictTateActionComponent
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ)
    (K : ConstantModelConstructibleFiniteTor (c.obj ell) T) :
    (StrictWeilCondensed.smallAction (c.obj ell) g).obj
        (strictTateCarrier ell c r |>.obj K) ≅
      strictTateCarrier ell c r |>.obj
        ((StrictWeilCondensed.smallAction (c.obj ell) g).obj K) := by
  apply ObjectProperty.isoMk
  change (StrictWeilCondensed.action (c.obj ell) g).obj
      (MonoidalCategory.tensorObj K.obj
        (StrictWeilCondensed.derivedTateLine ell c T r)) ≅
    MonoidalCategory.tensorObj
      ((StrictWeilCondensed.action (c.obj ell) g).obj K.obj)
      (StrictWeilCondensed.derivedTateLine ell c T r)
  exact (Functor.Monoidal.μIso (StrictWeilCondensed.action (c.obj ell) g)
    K.obj (StrictWeilCondensed.derivedTateLine ell c T r)).symm ≪≫
      MonoidalCategory.tensorIso (Iso.refl _)
        (StrictWeilCondensed.tateDatum ell c g r)

/-- Naturality of the canonical tensor comparison for the strict Tate carrier.
Source: monoidality of inverse image and [def-wf-tate-twist]
(blueprint: thm-a1-fourier-t-exact). -/
theorem strictTateAction_naturality
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ)
    {K L : ConstantModelConstructibleFiniteTor (c.obj ell) T}
    (f : K ⟶ L) :
    (StrictWeilCondensed.smallAction (c.obj ell) g).map
          ((strictTateCarrier ell c r).map f) ≫
        (strictTateActionComponent ell c g r L).hom =
      (strictTateActionComponent ell c g r K).hom ≫
        (strictTateCarrier ell c r).map
          ((StrictWeilCondensed.smallAction (c.obj ell) g).map f) := by
  apply (ObjectProperty.ι _).map_injective
  change (StrictWeilCondensed.action (c.obj ell) g).map
      (f.hom ▷ StrictWeilCondensed.derivedTateLine ell c T r) ≫
      ((Functor.Monoidal.μIso (StrictWeilCondensed.action (c.obj ell) g)
        L.obj (StrictWeilCondensed.derivedTateLine ell c T r)).inv ≫
        tensorHom (𝟙 _) (StrictWeilCondensed.tateDatum ell c g r).hom) =
    ((Functor.Monoidal.μIso (StrictWeilCondensed.action (c.obj ell) g)
      K.obj (StrictWeilCondensed.derivedTateLine ell c T r)).inv ≫
      tensorHom (𝟙 _) (StrictWeilCondensed.tateDatum ell c g r).hom) ≫
      (StrictWeilCondensed.action (c.obj ell) g).map f.hom ▷
        StrictWeilCondensed.derivedTateLine ell c T r
  simp only [Functor.Monoidal.μIso_inv, ← Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left]
  simp only [Category.assoc, id_tensorHom, whisker_exchange]

/-- The strict Tate lift is the functor induced by the tensor carrier and its
canonical action comparison. On `K` it is `IsoAlgebra.mk ⟨K ⊗ T(r), mem⟩
(tensorDatum K.str (tateDatum r))`.
Source: [def-wf-tate-twist], [lem-wft-fourier-weil]
(blueprint: thm-a1-fourier-t-exact). -/
noncomputable def strictTateActionIso
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ) :
    strictTateCarrier ell c r ⋙ StrictWeilCondensed.smallAction (c.obj ell) g ≅
      StrictWeilCondensed.smallAction (c.obj ell) g ⋙ strictTateCarrier ell c r :=
  NatIso.ofComponents
    (fun K ↦ strictTateActionComponent ell c g r K)
    (by
      intro K L f
      exact strictTateAction_naturality ell c g r f)

/-- The strict Tate functor with the canonical tensor carrier and Weil datum.
Source: [def-wf-tate-twist] (blueprint: thm-a1-fourier-t-exact). -/
noncomputable def strictTateFunctor
    (ell : ℕ) [Fact ell.Prime] {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] :
    StrictWeilCondensed.Complex (Profinite.padicAlgClRingObj ell) g ⥤
      StrictWeilCondensed.Complex (Profinite.padicAlgClRingObj ell) g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (strictTateActionIso ell (.closure) g (1 : ℤ))

/-- The inverse-character carrier is the published inverse-character transform on the
same geometric line. Source: [def-fd-transform], affine-line application paragraph
(blueprint: thm-a1-fourier-t-exact). -/
def inverseFourierCarrier
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell)))
    (c : Compactification (CondensedFourierPerverse.secondModel D).left) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (D.geometricFiber (CondensedFourierPerverse.lineModel D)).left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (D.geometricFiber (CondensedFourierPerverse.lineModel D)).left)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (D.geometricFiber (CondensedFourierPerverse.lineModel D)).left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (D.geometricFiber (CondensedFourierPerverse.lineModel D)).left)) :=
  CondensedFourierPerverse.transform D ell ψ⁻¹ c

/-- The canonical forward action comparison is the published component itself.
Source: [lem-wft-fourier-weil] (blueprint: thm-a1-fourier-t-exact). -/
def canonicalForwardFourierActionSpec
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell)))
    (c : Compactification (CondensedFourierPerverse.secondModel D).left)
    (α : CondensedFourierPerverse.transform D ell ψ c ⋙
        CondensedFourierPerverse.action D ell ≅
      CondensedFourierPerverse.action D ell ⋙
        CondensedFourierPerverse.transform D ell ψ c) : Prop :=
  ∀ K, α.app K = CondensedFourierPerverse.frobeniusComponent D ell ψ c K

/-- The canonical inverse action comparison is the published inverse-character
component itself. Source: [lem-wft-fourier-weil]
(blueprint: thm-a1-fourier-t-exact). -/
def canonicalInverseFourierActionSpec
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell)))
    (c : Compactification (CondensedFourierPerverse.secondModel D).left)
    (α : inverseFourierCarrier D ell ψ c ⋙
        CondensedFourierPerverse.action D ell ≅
      CondensedFourierPerverse.action D ell ⋙
        inverseFourierCarrier D ell ψ c) : Prop :=
  ∀ K, α.app K = CondensedFourierPerverse.frobeniusComponent D ell ψ⁻¹ c K

/--
The Fourier--Deligne transform is t-exact on the strict Weil hearts.  The
nontriviality hypothesis is essential: the trivial character sends the constant
perverse sheaf to a non-punctual constant object.  The inverse character is
also t-exact, and the Tate tensor from `def-wf-tate-twist` gives
`G = FT_{ψ⁻¹}(-)(1)` from the dual heart to the original heart.

The field-characteristic facts and `hk` are retained in the strict wrapper
interface. The underlying ordinary perverse predicates take the scheme directly.
Here `D.k` is the specified algebraic
closure of the finite base field: it is algebraically closed, and every nonzero
element lies in a finite subextension and has finite multiplicative order.
The characteristic facts follow from `D.prime` and `hEll`.

The strict lifts are tied to the named carrier transforms by the declarations
`canonicalForwardFourierActionSpec` and `canonicalInverseFourierActionSpec`, which require
objectwise equality with the transported canonical `frobeniusComponent` comparisons
of `lem-wft-fourier-weil`, as in
`CondensedFourierPerverse.fourier_perverse_equivalence`. The Tate carrier is tensoring
with the existing
`StrictWeilCondensed.tateComplex`; its Weil structure is the canonical
`tensorDatum`, as supplied by `lem-wft-fourier-weil`.  Thus the equivalence
cannot be witnessed by unrelated identity functors.

Proof route (blueprint: thm-a1-fourier-t-exact): Step 0 fixes the finite-field
strict-Weil models and the two Fourier carriers. Step 1 uses the nontrivial
character, the punctual calculation, stalk formula, and the affine-curve
cohomology range. Step 2 uses a lisse open, localization, coinvariants, the
pairwise distinct Artin--Schreier characters, and the quotient-functional rank
bound to obtain upper preservation. Step 3 applies canonical geometric
truncation and the lower-bound Hom test, with the induced Weil datum. Step 4
repeats the upper and lower argument for the inverse character, applies the exact
invertible Tate tensor on the source line after the inverse transform, and then uses
Weil Fourier inversion and cancellation of the Tate line to obtain the exact heart
equivalence.
-/
theorem fourierTransform_tExact
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) [Invertible (ell : D.k)]
    [Fact (ringChar D.k).Prime] [Fact (ringChar D.k ≠ ell)]
    (hk : (Finite D.k ∨ IsAlgClosed D.k) ∧
      ∀ x : D.k, x ≠ 0 → IsOfFinOrder x)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell))) (hψ : ψ ≠ 1)
    (c : Compactification (CondensedFourierPerverse.secondModel D).left) :
    let A₀ : Over (Spec (.of D.k₀)) := CondensedFourierPerverse.lineModel D
    let A'₀ : Over (Spec (.of D.k)) := D.geometricFiber A₀
    letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
    letI : LocallyOfFiniteType (D.geometricFiber A₀).hom := inferInstanceAs
      (LocallyOfFiniteType (pullback.snd A₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    letI : QuasiCompact (D.geometricFiber A₀).hom := inferInstanceAs
      (QuasiCompact (pullback.snd A₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    letI : IsSeparated (D.geometricFiber A₀).hom := inferInstanceAs
      (IsSeparated (pullback.snd
        (AffineSpace PUnit (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    letI : LocallyOfFiniteType A'₀.hom := inferInstanceAs
      (LocallyOfFiniteType (D.geometricFiber A₀).hom)
    letI : QuasiCompact A'₀.hom := inferInstanceAs
      (QuasiCompact (D.geometricFiber A₀).hom)
    letI : IsSeparated A'₀.hom := inferInstanceAs
      (IsSeparated (D.geometricFiber A₀).hom)
    let gA := CondensedFourierPerverse.frobenius D
    let gA' := gA
    let Cₓ := D.geometricFiber A₀
    let Cᵧ := A'₀
    let X := StrictWeilCondensed.Complex (Profinite.padicAlgClRingObj ell) gA
    let Y := StrictWeilCondensed.Complex (Profinite.padicAlgClRingObj ell) gA'
    let Pₓ := strictPerverseHeart ell hk (X := Cₓ) (g := gA)
    let Pᵧ := strictPerverseHeart ell hk (X := Cᵧ) (g := gA')
    let iₓ : Pₓ ⥤ X := ObjectProperty.ι _
    let iᵧ : Pᵧ ⥤ Y := ObjectProperty.ι _
    ∃ hInvₓ : ∀ x : Cₓ.left, Invertible (ell : Cₓ.left.residueField x),
      letI := hInvₓ
      ∃ hInvᵧ : ∀ x : Cᵧ.left, Invertible (ell : Cᵧ.left.residueField x),
        letI := hInvᵧ
        ∃ (FTψ : X ⥤ Y) (FTψinv : Y ⥤ X),
        (∃ αFT, canonicalForwardFourierActionSpec D ell ψ c αFT ∧
          isCarrierLiftNat (Profinite.padicAlgClRingObj ell) FTψ
            (CondensedFourierPerverse.transform D ell ψ c) αFT) ∧
        (∃ αFTinv, canonicalInverseFourierActionSpec D ell ψ c αFTinv ∧
          isCarrierLiftNat (Profinite.padicAlgClRingObj ell) FTψinv
            (inverseFourierCarrier D ell ψ c) αFTinv) ∧
        (∀ K : X, strictPerverseLE ell hk (X := Cₓ) (g := gA) 0 K →
          strictPerverseLE ell hk (X := Cᵧ) (g := gA') 0 (FTψ.obj K)) ∧
        (∀ K : X, strictPerverseGE ell hk (X := Cₓ) (g := gA) 0 K →
          strictPerverseGE ell hk (X := Cᵧ) (g := gA') 0 (FTψ.obj K)) ∧
        (∀ K : Y, strictPerverseLE ell hk (X := Cᵧ) (g := gA') 0 K →
          strictPerverseLE ell hk (X := Cₓ) (g := gA) 0 (FTψinv.obj K)) ∧
        (∀ K : Y, strictPerverseGE ell hk (X := Cᵧ) (g := gA') 0 K →
          strictPerverseGE ell hk (X := Cₓ) (g := gA) 0 (FTψinv.obj K)) ∧
        (∀ K : Y, strictPerverseLE ell hk (X := Cᵧ) (g := gA') 0 K →
          strictPerverseLE ell hk (X := Cₓ) (g := gA) 0
            ((strictTateFunctor ell gA).obj (FTψinv.obj K))) ∧
        (∀ K : Y, strictPerverseGE ell hk (X := Cᵧ) (g := gA') 0 K →
          strictPerverseGE ell hk (X := Cₓ) (g := gA) 0
            ((strictTateFunctor ell gA).obj (FTψinv.obj K))) ∧
        Exists fun [_hPx : Abelian Pₓ] ↦
          Exists fun [_hPy : Abelian Pᵧ] ↦
            ∃ E : Pₓ ≌ Pᵧ,
              Nonempty (E.functor ⋙ iᵧ ≅ iₓ ⋙ FTψ) ∧
              Nonempty (E.inverse ⋙ iₓ ≅
                iᵧ ⋙ FTψinv ⋙ strictTateFunctor ell gA) ∧
              PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor ∧
              PreservesFiniteLimits E.inverse ∧ PreservesFiniteColimits E.inverse
    := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
