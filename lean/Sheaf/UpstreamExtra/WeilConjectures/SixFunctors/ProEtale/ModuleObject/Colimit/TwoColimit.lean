module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison
public import Sheaf.Paper.CondensedFiniteModelProofAPI
import all Sheaf.Paper.CondensedFiniteModelProofAPI
public import Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
public import Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful
public import Sheaf.CategoryTheory.DirectedTriangulatedImage
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Sheaf.Paper.CondensedFinitePresentationDescent
public import Sheaf.Paper.CondensedSheafExtContinuity
public import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation

/-! Private proof helpers extracted from the upstream two-colimit file during the
2026-10-20 source synchronization. The public declarations remain upstream. -/

/-!

# The bounded constructible `ℚ̄_ℓ`-complexes as the 2-colimit over the finite subextensions

Let `ℓ` be a prime and `X` a scheme. For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`), let `C_E(X) = D^b_cons(X, E)` be the bounded
constructible derived category of modules over `E_X = p_X^* E̲`
(`ProEtale.BoundedConstructible (padicSubfieldRingObj X ℓ E)`, the full subcategory of the
unbounded `D(Mod_{E_X})` of `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`),
and let `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` be the one of modules over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`. The
derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} -
```
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` preserve
bounded constructibility, as proved below
(`ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj`,
`ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`), and hence restrict to
functors
```
ProEtale.constructibleExtendScalars h : C_E(X) ⥤ C_F(X)   (E ≤ F),
ProEtale.constructibleToPadicAlgCl E : C_E(X) ⥤ C_Ω(X),
```
compatible with each other through the transitivity of extension of scalars
(`ProEtale.constructibleToPadicAlgClCompIso`). Together these form a cocone of categories
`ProEtale.constructibleCocone X ℓ` on the directed system `E ↦ C_E(X)`, with vertex `C_Ω(X)`,
in the sense of `WeilConjectures.CategoryTheory.FilteredTwoColimit`.

The main statement, **`ℚ̄_ℓ` is a 2-colimit** (`ProEtale.constructibleCocone_isFilteredTwoColimit`),
is that this cocone is a filtered 2-colimit: the comparison functor
`2-colim_E C_E(X) ⟶ C_Ω(X)`, `(E, K_E) ↦ T^X_{E,Ω} K_E`, is an equivalence of ordinary
categories. By `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` this is the conjunction of

* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: every bounded constructible
  `ℚ̄_ℓ,X`-complex `K` is isomorphic to `T^X_{E,Ω} K_E` for some finite subextension `E` and some
  bounded constructible `E_X`-complex `K_E` (descent of constructible objects);
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` in `D(Mod_{ℚ̄_ℓ,X})` is defined over some finite
  subextension `H ⊇ E, F`, and two morphisms over `H` with the same image are equal over some
  finite subextension `H' ⊇ H`. Since the bounded constructible complexes are stable under
  shifts, this includes the statement for the shifted targets `L_F[n]`, which is what the
  compatibility with the triangulated structures requires.

These are stated for a topologically noetherian `X`, the setting in which the bounded
constructible complexes form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`). They are *not* formal consequences of the
identification `ℚ̄_ℓ,X ≃ colim_E E_X` of `ProEtale.isColimitPadicAlgClRingObjCocone`, and they
are false for the unbounded derived categories; see the module docstring of
`WeilConjectures.CategoryTheory.FilteredTwoColimit` for the ordinary-category model of the
2-colimit that they describe.

## Proof inputs

The preservation and object-descent clauses below are proved from the named inputs.
Hom injectivity uses a splitting of the coefficient inclusion on the entire derived category.
Hom surjectivity uses the single-sheaf continuity input and a uniformly bounded-below
coefficient complex presentation. Its distinguished-triangle devissage is proved here.

* `ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj` and
  `ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`: extension of scalars
  along `E_X ⟶ F_X` and `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes. The extension
  of scalars is exact
  (`ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`), so it
  is computed termwise and preserves boundedness, and it sends a locally finitely
  presented module on a stratum to a locally finitely presented one, the presentation being
  tensored up.
* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: constructible descent. A bounded
  constructible `ℚ̄_ℓ,X`-complex has finitely many constructible cohomology sheaves; each is
  locally, on the strata of a stratification, finitely presented, and a finite presentation
  involves finitely many sections of `ℚ̄_ℓ,X`, which are defined over a finite subextension since
  `ℚ̄_ℓ,X = colim_E E_X` (`ProEtale.isColimitPadicAlgClRingObjCocone`). A finite Postnikov
  induction on the length of the complex then descends the complex itself, the gluing data being
  morphisms which descend by (Hom).
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  continuity of the derived hom. For a bounded constructible first argument `K_E` and a
  bounded below second argument, `Hom_{D(Mod_{ℚ̄_ℓ,X})}(T_{E,Ω} K_E, T_{E,Ω} L_E)` is the filtered
  colimit over `H ⊇ E` of the `Hom_{D(Mod_{H_X})}(T_{E,H} K_E, T_{E,H} L_E)`: `K_E` is a finite
  extension of shifts of locally finitely presented modules, for which the derived hom into a
  filtered colimit of uniformly bounded below complexes is the filtered colimit of the derived
  homs, and `ℚ̄_ℓ,X = colim_H H_X`.

This is the input needed to transport base change theorems from finite to `ℚ̄_ℓ`-coefficients:
by (Obj) every constructible `K` is `T^X_{E,Ω} K_E`, and the compatibility of the base change
maps with the extension of scalars (built from the (Pull) and (Push) comparisons of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`) then shows that the
base change map at `K` is the extension of scalars of the one at `K_E`. This compatibility of
the base change maps of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems`
with the extension of scalars is not yet formalized.

-/

@[expose] public section

-- This support module intentionally consists of private helpers.
set_option linter.privateModule false
set_option autoImplicit false


universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian ZeroObject

open scoped CategoryTheory.Obj CategoryTheory.Functor

section HomFactorization

set_option linter.unusedSectionVars false

universe v w vI uI
open CategoryTheory.Pretriangulated Preadditive

namespace CategoryTheory
variable {D : Type w} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {I : Type uI} [Category.{vI} I] [IsFiltered I] {N : I ⥤ D} (c : Cocone N)

private lemma factors_middle [∀ i, Mono (c.ι.app i)]
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : factors c T.obj₁) (h₃ : factors c T.obj₃) : factors c T.obj₂ := by
  intro f
  obtain ⟨i, a, ha⟩ := h₁ (T.mor₁ ≫ f)
  have hz : T.invRotate.mor₁ ≫ a = 0 := by
    apply (cancel_mono (c.ι.app i)).mp
    rw [zero_comp, Category.assoc, ← ha, ← Category.assoc]
    rw [show T.invRotate.mor₁ ≫ T.mor₁ = 0 from
      comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hT), zero_comp]
  obtain ⟨b, hb⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang _ hT) a hz
  change T.obj₂ ⟶ N.obj i at b
  change a = T.mor₁ ≫ b at hb
  have hz' : T.mor₁ ≫ (f - (b ≫ c.ι.app i : T.obj₂ ⟶ c.pt)) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc]
    rw [← hb, ← ha, sub_self]
  obtain ⟨d, hd⟩ := T.yoneda_exact₂ hT (f - (b ≫ c.ι.app i : T.obj₂ ⟶ c.pt)) hz'
  obtain ⟨j, e, he⟩ := h₃ d
  let k := IsFiltered.max i j
  let p : i ⟶ k := IsFiltered.leftToMax i j
  let q : j ⟶ k := IsFiltered.rightToMax i j
  refine ⟨k, (b ≫ N.map p) + (T.mor₂ ≫ e ≫ N.map q), ?_⟩
  rw [Preadditive.add_comp, Category.assoc, c.w p,
    Category.assoc, Category.assoc, c.w q, ← he]
  exact (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)

private lemma shiftFactors_iso : (shiftFactors c).IsClosedUnderIsomorphisms where
  of_iso e h n := factors_iso c ((shiftFunctor D n).mapIso e) (h n)

private lemma shiftFactors_shift : (shiftFactors c).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K h m ↦
    factors_iso c ((shiftFunctorAdd D n m).app K) (h (n + m))⟩

attribute [local instance] shiftFactors_iso shiftFactors_shift

private lemma shiftFactors_tri [∀ i, Mono (c.ι.app i)] :
    (shiftFactors c).IsTriangulated where
  exists_zero := by
    obtain ⟨i⟩ := IsFiltered.nonempty (C := I)
    refine ⟨0, isZero_zero D, fun n f ↦ ⟨i, 0, ?_⟩⟩
    exact ((shiftFunctor D n).map_isZero (isZero_zero D)).eq_of_src f _
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ n ↦
    factors_middle c (T⟦n⟧)
      (Triangle.shift_distinguished T hT n) (h₁ n) (h₃ n))

private lemma mono_map_colimit_leg
    {A : Type*} [Category A] {J : Type*} [Category J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (c : Cocone N) (hc : IsColimit c)
    (hmono : ∀ i, Mono (Q.map (c.ι.app i))) (i : J) :
    Mono (Q.map (colimit.ι N i)) := by
  let e := (colimit.isColimit N).coconePointUniqueUpToIso hc
  have he : colimit.ι N i ≫ e.hom = c.ι.app i :=
    (colimit.isColimit N).comp_coconePointUniqueUpToIso_hom hc i
  have : Mono (Q.map (c.ι.app i)) := hmono i
  have : Mono (Q.map (colimit.ι N i) ≫ Q.map e.hom) := by
    rw [← Q.map_comp, he]
    infer_instance
  exact mono_of_mono _ (Q.map e.hom)



end CategoryTheory


end HomFactorization

set_option linter.unusedSectionVars true

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The derived extensions of scalars and their transitivity -/

section ExtendScalars

end ExtendScalars

/-! ### The bounded constructible categories and the functors between them -/

section Constructible

end Constructible

/-! ### `ℚ̄_ℓ` is a 2-colimit -/

section TwoColimit

variable [TopologicalSpace.NoetherianSpace X]

omit [TopologicalSpace.NoetherianSpace X] in
set_option backward.isDefEq.respectTransparency true in
private lemma mono_of_coefficient_comparison
    {E F H : FiniteIntermediateField ℓ} (he : E ≤ H) (hf : F ≤ H)
    (L : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)))
    (A B : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (p : A ⟶ B)
    (ei : A ≅ (finiteCoefficientDerivedRestriction X ℓ he).obj
      ((finiteCoefficientDerivedExtension X ℓ hf).obj L))
    (eΩ : B ≅ (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
      ((finiteCoefficientDerivedToAlgCl X ℓ F).obj L))
    (hcomp : ∀ K g,
      finiteCoefficientDerivedAlgClHomEquiv X ℓ E K _
        ((finiteCoefficientDerivedTensorCompIso X ℓ he).inv.app K ≫
          (finiteCoefficientDerivedToAlgCl X ℓ H).map
            ((finiteCoefficientDerivedHomEquiv X ℓ he K _).symm (g ≫ ei.hom)) ≫
          (finiteCoefficientDerivedTensorCompIso X ℓ hf).hom.app L) =
        g ≫ p ≫ eΩ.hom) : Mono p := by
  let T := finiteCoefficientDerivedToAlgCl X ℓ H
  let : T.Faithful := faithful_leftDerivedExtendScalarsToPadicAlgCl X ℓ H
  constructor
  intro W a b hab
  let adjH := finiteCoefficientDerivedHomEquiv X ℓ he W
    ((finiteCoefficientDerivedExtension X ℓ hf).obj L)
  let adjΩ := finiteCoefficientDerivedAlgClHomEquiv X ℓ E W
    ((finiteCoefficientDerivedToAlgCl X ℓ F).obj L)
  have hh : adjΩ
      ((finiteCoefficientDerivedTensorCompIso X ℓ he).inv.app W ≫
        T.map (adjH.symm (a ≫ ei.hom)) ≫
        (finiteCoefficientDerivedTensorCompIso X ℓ hf).hom.app L) =
    adjΩ ((finiteCoefficientDerivedTensorCompIso X ℓ he).inv.app W ≫
        T.map (adjH.symm (b ≫ ei.hom)) ≫
        (finiteCoefficientDerivedTensorCompIso X ℓ hf).hom.app L) :=
    (hcomp W a).trans ((Category.assoc a p eΩ.hom).symm.trans
      ((congrArg (fun t ↦ t ≫ eΩ.hom) hab).trans
        ((Category.assoc b p eΩ.hom).trans (hcomp W b).symm)))
  have hh1 := adjΩ.injective hh
  have hh2 := (cancel_epi
    ((finiteCoefficientDerivedTensorCompIso X ℓ he).inv.app W)).mp hh1
  have hh3 := (cancel_mono
    ((finiteCoefficientDerivedTensorCompIso X ℓ hf).hom.app L)).mp
    hh2
  have hh4 := T.map_injective hh3
  have hh5 := adjH.symm.injective hh4
  exact (cancel_mono ei.hom).mp hh5


private lemma single_factors
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) M)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ)
    [HasColimit N]
    (hN : ∃ a : ℤ, ∀ (i : J) (r : ℤ), r < a → IsZero ((N.obj i).X r)) :
    CategoryTheory.shiftFactors (DerivedCategory.Q.mapCocone (colimit.cocone N))
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  exact CategoryTheory.shiftFactors_of_hom_colimit N DerivedCategory.Q _
    (fun n ↦ isIso_constructible_condensed_sheaf_hom_colimit X ℓ E M hM N hN n)

private lemma bounded_factors
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ)
    [HasColimit N]
    (hN : ∃ a : ℤ, ∀ (i : J) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (hmono : ∀ i : J, Mono (DerivedCategory.Q.map (colimit.ι N i)))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    CategoryTheory.factors (DerivedCategory.Q.mapCocone (colimit.cocone N)) K := by
  let c := DerivedCategory.Q.mapCocone (colimit.cocone N)
  let : ∀ i, Mono (c.ι.app i) := hmono
  let Q := CategoryTheory.shiftFactors c
  let : Q.IsClosedUnderIsomorphisms := CategoryTheory.shiftFactors_iso c
  let : Q.IsStableUnderShift ℤ := CategoryTheory.shiftFactors_shift c
  let : Q.IsTriangulated := CategoryTheory.shiftFactors_tri c
  let P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
    ObjectProperty.isoClosure (IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E))
  have hP : ∀ M, P M → Q ((DerivedCategory.singleFunctor _ 0).obj M) := by
    rintro M ⟨M', hM', ⟨e⟩⟩
    exact Q.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm
      (single_factors X ℓ E M' hM' N hN)
  have hQ : Q K := DerivedCategory.prop_of_bounded Q P hP K hK.1
    (fun n ↦ ⟨_, hK.2 n, ⟨Iso.refl _⟩⟩)
  exact CategoryTheory.factors_iso c ((shiftFunctorZero _ ℤ).app K) (hQ 0)

private lemma bounded_factors_cocone
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ)
    (c : Cocone N) (hc : IsColimit c)
    (hN : ∃ a : ℤ, ∀ (i : J) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (hmono : ∀ i : J, Mono (DerivedCategory.Q.map (c.ι.app i)))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    ∀ f : K ⟶ DerivedCategory.Q.obj c.pt,
      ∃ (i : J) (g : K ⟶ DerivedCategory.Q.obj (N.obj i)),
        f = g ≫ DerivedCategory.Q.map (c.ι.app i) := by
  let : HasColimit N := ⟨⟨c, hc⟩⟩
  exact CategoryTheory.factors_of_colimit_cocone N DerivedCategory.Q c hc K
    (bounded_factors X ℓ E N hN
      (CategoryTheory.mono_map_colimit_leg N DerivedCategory.Q c hc hmono) K hK)


omit [TopologicalSpace.NoetherianSpace X] in
private lemma constructibleToPadicAlgCl_map_hom (E : FiniteIntermediateField ℓ)
    {K L : PadicSubfieldConstructible X ℓ E} (f : K ⟶ L) :
    ((constructibleToPadicAlgCl X ℓ E).map f).hom =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).map f.hom := rfl

omit [TopologicalSpace.NoetherianSpace X] in
private lemma tensorComp_hom {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ h).hom.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  exact Category.id_comp _

omit [TopologicalSpace.NoetherianSpace X] in
private lemma tensorComp_inv {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).inv.app K).hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ h).inv.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  simp only [Iso.trans_inv, Iso.refl_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.comp_id]
  rfl

private instance moduleFlatResolution {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) := by infer_instance

private instance moduleTensorFour {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C D : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)),
      GradedObject.HasTensor₄ObjExt A B C D := by infer_instance

private instance moduleTensorLeft {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensor₁₂Tensor A B C := by infer_instance

private instance moduleTensorRight {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensorTensor₂₃ A B C := by infer_instance

private instance moduleTensorColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ
        ((curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)).obj M) := by
  infer_instance

private instance moduleTensorFlipColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ
        ((curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)).flip.obj M) := by
  infer_instance

set_option backward.isDefEq.respectTransparency true in
private noncomputable def algClDerivedIso (E : FiniteIntermediateField ℓ) :
    derivedExtendScalarsToPadicAlgCl X ℓ E ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory :=
  (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))
    |>.leftDerivedFunctorIsoMapDerivedCategory

private noncomputable instance algClCommShift (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ :=
  Functor.CommShift.ofIso (algClDerivedIso X ℓ E).symm ℤ

private instance algClTriangulated (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility (algClDerivedIso X ℓ E).symm ℤ
  exact Functor.isTriangulated_of_iso (algClDerivedIso X ℓ E).symm

private lemma finitePresentation_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) (e : M ≅ N) : Mod.IsFinitelyPresented R N := by
  rcases h with ⟨n, m, f, ⟨i⟩⟩
  exact ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩

private lemma localFinitePresentation_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsLocallyFinitelyPresented R M) (e : M ≅ N) : IsLocallyFinitelyPresented R N := by
  rcases h with ⟨U, hU⟩
  exact ⟨U, fun i ↦ finitePresentation_of_iso (hU i)
    (((upperStar Ab.{u + 1} (U.f i)).mapMod R).mapIso e)⟩

private lemma constructible_of_iso_model {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsConstructibleModuleObject R M) (e : M ≅ N) :
    IsConstructibleModuleObject R N := by
  rcases h with ⟨U, hU⟩
  exact ⟨U, fun i ↦ localFinitePresentation_of_iso (hU i)
    (((upperStar Ab.{u + 1} (U.immersion i)).mapMod R).mapIso e)⟩

private lemma fp_zero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (hM : IsZero M) :
    Mod.IsFinitelyPresented R M := by
  have hF : IsZero (Mod.finiteFree R 0) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro j
    exact Fin.elim0 j
  exact ⟨0, 0, 0, ⟨hM.iso (IsZero.of_epi (cokernel.π (0 :
    Mod.finiteFree R 0 ⟶ Mod.finiteFree R 0)) hF)⟩⟩
private lemma constructible_zero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (hM : IsZero M) :
    IsConstructibleModuleObject R M := by
  refine ⟨Scheme.Stratification.trivial X, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} ((Scheme.Stratification.trivial X).immersion i)
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  exact fp_zero _ (((upperStar Ab.{u + 1} (𝟙 X)).mapMod (F.obj R)).map_isZero
    ((F.mapMod R).map_isZero hM))
attribute [local instance 2000] finiteBoundedTriangulated

private lemma algClBoundedTriangulated :
    (boundedConstructible (padicAlgClRingObj X ℓ)).IsTriangulated := by
  obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicAlgCl X ℓ
  exact bounded_tri_of_serre _ hk he

attribute [local instance 2000] algClBoundedTriangulated

private noncomputable def ambientCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicAlgClRingObj X ℓ))) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := (constructibleToPadicAlgCl X ℓ E) ⋙ (boundedConstructible (padicAlgClRingObj X ℓ)).ι
  iso h := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constructibleToPadicAlgClCompIso X ℓ h) _

private noncomputable instance ambientCommShift (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).CommShift ℤ :=
  inferInstanceAs (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ)

private instance ambientTriangulated (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).IsTriangulated :=
  inferInstanceAs (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated)

private lemma ambientHomSurj : (ambientCocone X ℓ).HomSurj := by
  intro i j K L f
  obtain ⟨k, hi, hj, g, hg⟩ := constructibleCocone_homSurj X ℓ i j K L
    (ObjectProperty.homMk f)
  refine ⟨k, hi, hj, g, ?_⟩
  simpa [ambientCocone, constructibleCocone] using congrArg (·.hom) hg

private lemma single_model (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicAlgClRingObj X ℓ)) (hM : IsConstructibleModuleObject (padicAlgClRingObj X ℓ) M) :
    ∃ E, ((ambientCocone X ℓ).Φ E).essImage ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨E, M_E, hE, ⟨e⟩⟩ := exists_constructible_finiteCoefficient_model X ℓ M hM
  refine ⟨E, ⟨(DerivedCategory.singleFunctor _ 0).obj M_E,
    single_bounded_constructible X (padicSubfieldRingObj X ℓ E) M_E hE⟩, ⟨?_⟩⟩
  exact (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
    |>.singleFunctorCompLeftDerivedFunctorIso).app M_E ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e

end TwoColimit

end AlgebraicGeometry.ProEtale
