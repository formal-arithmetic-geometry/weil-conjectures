# FiniteHomNuTensorNormalization

## Reason

The expanded representative equation repeated concrete intrinsic tensor-model data
beneath four binders. Applying descent repeatedly compared the large instantiated
coefficient-category structures. Share the predicate generically, and use an explicit
total-tensor functor whose object and map fields are the native total complex and
tensor map. This avoids reducing the full monoidal structure of cochain complexes
when checking the representative equation. The source localization map and final native chain isomorphism are
identified by heterogeneous equality certificates, so that its shared type stays
abstract through specialization. No target signature or mathematical
hypothesis changes. Targets using this definition need statement-meaning review.

## Old

```lean
def FiniteHomNuTensorNormalization (n : ℕ)
    (μ : (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ≅
      (finiteHomNu l E X n).prod (finiteHomNu l E X n) ⋙
        (finiteIntrinsicClosed l E X n).tensor) : Prop :=
  ∀ (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ),
    ∀ hP : finiteHomKFlat l E X n P, ∀ hQ : finiteHomKFlat l E X n Q,
    letI : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
      essentiallySmallSelf.{0, u, u + 1} _
    letI : HasDerivedCategory.{u + 2} (normalizedDVRModules l E X n) :=
      HasDerivedCategory.standard _
    FiniteHomNuModelSquareAux
      (finiteHomEtaleQ l E X n) (finiteHomIntrinsicQ l E X n)
      (finiteHomNuComplex l E X n) (finiteHomNu l E X n)
      (finiteHomNuFactors l E X n)
      (fun P Q ↦ HomologicalComplex.tensorObj P Q)
      (fun P Q ↦ (coefficientTotalTensor.{u, u + 1, u}
        (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)).obj (P, Q))
      (finiteHomEtaleClosed l E X n).tensor
      (finiteIntrinsicClosed l E X n).tensor
      (finiteHomEtaleTensorModel l E X n) μ P Q
      (finiteHomNuChainTensor l E X n P Q)
      ((finiteIntrinsicTensorModels l E X n).comparison.inv.app
        (⟨(finiteHomNuComplex l E X n).obj P, hP⟩,
          ⟨(finiteHomNuComplex l E X n).obj Q, hQ⟩))
```

## New

```lean
def FiniteHomNuTensorNormalization (n : ℕ)
    (μ : (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ≅
      (finiteHomNu l E X n).prod (finiteHomNu l E X n) ⋙
        (finiteIntrinsicClosed l E X n).tensor) : Prop :=
  let : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let : HasDerivedCategory.{u + 2} (normalizedDVRModules l E X n) :=
    HasDerivedCategory.standard _
  let K := CochainComplex (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1))))) ℤ
  let S : ObjectProperty (CochainComplex (normalizedDVRModules l E X n) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
  let P : ObjectProperty K := fun A ↦ S ((finiteHomNuComplex l E X n).obj A)
  FiniteHomNuTensorNormalizationAux
    (finiteHomEtaleQ l E X n) (finiteHomIntrinsicQ l E X n)
    (finiteHomNuComplex l E X n) (finiteHomNu l E X n) (finiteHomNuFactors l E X n)
    P S (fun _ h ↦ h) (finiteHomCochainTensorGeneral _)
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n))
    (finiteHomEtaleClosed l E X n).tensor (finiteIntrinsicClosed l E X n).tensor
    (finiteIntrinsicTensorModels l E X n).comparison
    (finiteHomEtaleTensorModel l E X n) (finiteHomNuChainTensor l E X n) μ
```

The new auxiliary predicate is:

```lean
def FiniteHomNuTensorNormalizationAux
    {C : Type a} {D : Type b} {A : Type c} {B : Type d}
    [Category.{e} C] [Category.{f} D] [Category.{g} A] [Category.{w} B]
    (QA : C ⥤ A) (QB : D ⥤ B) (U : C ⥤ D) (V : A ⥤ B)
    (ρ : QA ⋙ V ≅ U ⋙ QB) (P : ObjectProperty C) (S : ObjectProperty D)
    (hU : ∀ x, P x → S (U.obj x))
    (t : C × C ⥤ C) (t' : D × D ⥤ D) (T : A × A ⥤ A) (T' : B × B ⥤ B)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ QB ≅ ((S.ι ⋙ QB).prod (S.ι ⋙ QB)) ⋙ T')
    {M : C → C → Type g} (η : ∀ x y, M x y)
    {F : C → C → Type f} (ε : ∀ x y, F x y)
    (μ : T ⋙ V ≅ V.prod V ⋙ T') : Prop :=
  ∀ x y (hx : P x) (hy : P y),
    ∃ (a : T.obj (QA.obj x, QA.obj y) ⟶ QA.obj (t.obj (x, y)))
      (e : U.obj (t.obj (x, y)) ≅ t'.obj (U.obj x, U.obj y)),
      HEq a (η x y) ∧ HEq e (ε x y) ∧
      μ.hom.app (QA.obj x, QA.obj y) ≫
          T'.map (Prod.mkHom (ρ.hom.app x) (ρ.hom.app y)) ≫
            r'.inv.app (⟨U.obj x, hU x hx⟩, ⟨U.obj y, hU y hy⟩) =
        V.map a ≫ ρ.hom.app (t.obj (x, y)) ≫ QB.map e.hom
```

It contains the same universally quantified `FiniteHomNuModelSquareAux` equation,
with the category, representative properties, functors, tensor bifunctors and
intrinsic comparison shared as parameters. A pointwise native localization map
`a` is certified heterogeneously equal to the specified source model map, and a
pointwise native isomorphism `e` is certified heterogeneously equal to the
specified chain comparison. Substituting both certificates recovers the original
representative equation with exactly its original maps, for each pair of K-flat
representatives. These witnesses add no choices to the construction: their values
are fixed by equality to the specified maps. In the generic uniqueness proof,
`eq_of_heq` identifies them with the corresponding components of the source and
chain natural comparisons. The shared source and combined presentation predicates
retain the map carrier until that generic proof. No hypothesis is added or
dropped, and every displayed square remains the original tensor-localization square.

The explicit source functor is constructed in the unclaimed etale module as follows:

```lean
def finiteHomCochainTensorGeneral
    (C : Type a) [Category.{b} C] [Preadditive C] [HasZeroObject C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C] :
    CochainComplex C ℤ × CochainComplex C ℤ ⥤ CochainComplex C ℤ := by
  let (P Q : CochainComplex C ℤ) : HomologicalComplex.HasTensor P Q := inferInstance
  exact
    { obj := fun P ↦ HomologicalComplex.tensorObj P.1 P.2
      map := fun f ↦ HomologicalComplex.tensorHom f.1 f.2
      map_id := fun P ↦ by
        apply HomologicalComplex.Hom.ext
        funext k
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro p q hpq
        simp only [HomologicalComplex.tensorHom, HomologicalComplex.ι_mapBifunctorMap,
          prod_id_fst, prod_id_snd, HomologicalComplex.id_f,
          curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc,
          id_tensorHom_id, Category.id_comp, Category.comp_id]
      map_comp := fun f g ↦ by
        apply HomologicalComplex.Hom.ext
        funext k
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro p q hpq
        simp only [HomologicalComplex.tensorHom, prod_comp_fst, prod_comp_snd,
          HomologicalComplex.comp_f,
          HomologicalComplex.ι_mapBifunctorMap_assoc,
          HomologicalComplex.ι_mapBifunctorMap, curriedTensor_map_app,
          curriedTensor_obj_map, ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc] }
```

The constructor takes the additive structure, zero object and small colimits directly,
so it carries no unused Grothendieck universe or large abelian structure.
This functor has exactly the native tensor's object and map functions. Its functor
laws follow directly from naturality of the total-summand inclusions and the
identity and composition laws for tensor maps. The former version using the native functor laws was checked equal to the
native tensor functor by reflexivity in the diagnostic compile. The current
constructor has the same object and map fields; its law proofs are propositions. In particular its object
function is exactly `HomologicalComplex.tensorObj`, as in the old normalization.
No naturality or representative test is added or dropped.

## Users

The source-import closure and whole-name searches give the following consumers.
The normalization predicate is equivalent to the old one by the equality
substitution described above. The explicit source constructor has the original
object and map fields. Thus each consumer retains its mathematical statement.
Rows also retain adapted and new modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Adds the real explicit total-tensor functor; preserves existing declarations. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | new, Y7 | Representative localization uses that same source functor. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Same equation and K-flat tests; shared predicate and explicit source functor. |
| Sheaf.Paper.FiniteCoefficientSiteTensorNaturality | new, Y7 | Naturality uses the same explicit native tensor maps. |
| Sheaf.Paper.FiniteCoefficientSiteTensorPresentation | new, Y7 | Bundles the same source functor with its comparison data. |

## Status

landed 20261022T114256-L-598666 2026-10-22 (merge of deliver/Y7/Sheaf.Paper.FiniteCoefficientSiteHomArrow)
