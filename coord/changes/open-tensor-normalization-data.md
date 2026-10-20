# SheafOfModules.OpenTensorNormalization data and finite comparison interface

## Reason

The three independent geometric subresults must refer to the existing operation records,
and the original theorem must import those subresults. Move the data and previously proved
infrastructure to `Sheaf.SixFunctors.OpenTensorNormalizationData` and publicly reexport it
from the original module. This removes the import cycle without changing the names,
universes, hypotheses or mathematical definitions of any existing declaration. The two
original holed theorems and the final theorem stay in their original module.

Profiling also found expensive kernel checks in the finite tensor specification. Introduce
`finiteTensor` as an explicitly typed alias of the existing uncurried finite tensor and
use it in the finite comparison types. Replace closed `finiteInput` projections by their
explicit, definitionally equal fields in `FiniteComparisonsCore` and `finiteGammaLeft`.
The original structure continued to exceed 60 seconds even with the typed aliases;
the subtype data module compiled in 47.9 and 51.2 seconds in the checked runs.
These are presentation changes only. No target statement or source-library declaration
changes. The targets' meanings are unchanged; this record permits independent verification
of that claim.

`FiniteTensorPin` is represented by a subtype of `FiniteTensorTotal` satisfying
exactly the original two proof fields. Named `totalIso`, `pure_summands`, `model`
and `mk` accessors retain the mathematical interface. Its generated structure recursors
are no longer generated; searching both library roots found no users of these recursors,
constructor, or fields outside the item's own record declaration. The representation has
exactly the same comparison data and equations, up to proof irrelevance. Definitions used
by target statements have changed their representation, so the semantic target review is
reopened for this record; the claim to review is equivalence with the original data.

## Old

The declarations were local to the original module.

```lean
/-- The source and target of the finite signed-total comparison.
Source: Stacks 06YN (blueprint: lem-sf-open-tensor-normalization). -/
def FiniteTensorTotal {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) : Type _ :=
  ∀ P Q : CochainComplex (FiniteModules A X) ℤ,
    (e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj
      (HomologicalComplex.mapBifunctor P Q (curriedTensor (FiniteModules A X)) (.up ℤ)) ≅
    (total R).obj ((e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P,
      (e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj Q)

set_option backward.isDefEq.respectTransparency false in
/-- The total comparison carries every fixed-scalar pure bidegree summand to the
same ring-sheaf pure summand. Source: Stacks 03EK and 06YN
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteTensorPure {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i)
    (totalIso : FiniteTensorTotal e) : Prop :=
  ∀ (P Q : CochainComplex (FiniteModules A X) ℤ)
      (p q n : ℤ) (hn : p + q = n) (W : X.ProEtᵒᵖ)
      (x : (P.X p).obj.obj W) (y : (Q.X q).obj.obj W),
    ((totalIso P Q).hom.f n).val.app W
      ((e.underlying.inv.app _).hom.app W
        ((HomologicalComplex.ιMapBifunctor P Q (curriedTensor (FiniteModules A X))
          (.up ℤ) p q n hn).hom.app W (finitePure (P.X p) (Q.X q) W x y))) =
    (HomologicalComplex.ιMapBifunctor
      ((e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P)
      ((e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj Q)
      (tensor R) (.up ℤ) p q n hn).val.app W
        (pure R (e.equivalence.functor.obj (P.X p)) (e.equivalence.functor.obj (Q.X q)) W
          ((e.underlying.inv.app (P.X p)).hom.app W x)
          ((e.underlying.inv.app (Q.X q)).hom.app W y))

set_option backward.isDefEq.respectTransparency false in
/-- The tensor comparison commutes with the finite localization map and the
ring-sheaf representative comparison. Source: Stacks 06YU and 0GL1
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteTensorModel {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (t : TensorModel R)
    (d : Functor.uncurry.obj (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X) ⋙ e.derived ≅
      (e.derived.prod e.derived) ⋙ t.functor)
    (totalIso : FiniteTensorTotal e) : Prop :=
  ∀ (P Q : CochainComplex (FiniteModules A X) ℤ)
      (hp : resolving R ((e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P))
      (hq : resolving R ((e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj Q)),
    HEq (e.derived.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      e.equivalence.functor.mapDerivedCategoryFactors.hom.app
        (HomologicalComplex.mapBifunctor P Q (curriedTensor (FiniteModules A X)) (.up ℤ)) ≫
      DerivedCategory.Q.map (totalIso P Q).hom ≫
      tensorRepresentative (R := R) t
        ((e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P)
        ((e.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj Q) hp hq)
    (d.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      t.functor.map (CategoryTheory.Prod.mkHom
        (e.equivalence.functor.mapDerivedCategoryFactors.hom.app P)
        (e.equivalence.functor.mapDerivedCategoryFactors.hom.app Q)))

/-- Finite tensor transport is fixed on every total-complex pure summand and then
on all flat K-flat representatives by the two published tensor factorizations.
Source: Stacks 03EK, 06YU, 0GL1 (blueprint: lem-sf-open-tensor-normalization). -/
structure FiniteTensorPin {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (t : TensorModel R)
    (d : Functor.uncurry.obj (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X) ⋙ e.derived ≅
      (e.derived.prod e.derived) ⋙ t.functor) where
  totalIso : FiniteTensorTotal e
  pure_summands : finiteTensorPure e totalIso
  model : finiteTensorModel e t d totalIso
```

```lean
structure FiniteComparisonsCore (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} {sq : OpenImmersionSquare gU j' j g}
    [_hj : IsOpenImmersion j] [_hj' : IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t) where
  realizeX : FiniteRealization A X (finiteInput A gU j' j g sq).R
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
  realizeX' : FiniteRealization A X' (finiteInput A gU j' j g sq).S
    (toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A)))
  realizeU : FiniteRealization A U
    (restrictRing .ordinary (finiteInput A gU j' j g sq).j (finiteInput A gU j' j g sq).R)
    (Functor.whiskerLeft (openInclusion .ordinary (finiteInput A gU j' j g sq).j).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  realizeU' : FiniteRealization A U'
    (restrictRing .ordinary (finiteInput A gU j' j g sq).j' (finiteInput A gU j' j g sq).S)
    (Functor.whiskerLeft (openInclusion .ordinary (finiteInput A gU j' j g sq).j').op
      (toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A))))
  shriek : finiteShriek A (finiteInput A gU j' j g sq).j ⋙ realizeX.derived ≅ realizeU.derived ⋙
    o.opens.jShriek
  shriek' : finiteShriek A (finiteInput A gU j' j g sq).j' ⋙ realizeX'.derived ≅ realizeU'.derived ⋙
    o.opens.jShriek'
  pull : finitePull A g ⋙ realizeX'.derived ≅ realizeX.derived ⋙ o.gPull.derived
  pullU : finitePull A gU ⋙ realizeU'.derived ≅ realizeU.derived ⋙ o.gUPull.derived
  openPull : (ProEtale.upperStar (ModuleCat.{u + 1} A) (finiteInput A gU j' j g
    sq).j).leftDerivedFunctor ⋙ realizeU.derived ≅
    realizeX.derived ⋙ o.opens.jStar
  tensorX : Functor.uncurry.obj (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X) ⋙
    realizeX.derived ≅ (realizeX.derived.prod realizeX.derived) ⋙ o.tensorX.functor
  tensorU : Functor.uncurry.obj (ProEtale.derivedTensor (ModuleCat.{u + 1} A) U) ⋙
    realizeU.derived ≅ (realizeU.derived.prod realizeU.derived) ⋙ o.tensorU.functor
  openPull' : finitePull A (finiteInput A gU j' j g sq).j' ⋙ realizeU'.derived ≅
    realizeX'.derived ⋙ o.opens.jStar'
  pull_pin : FinitePullPin realizeX realizeX' g (finiteInput A gU j' j g sq).coefficient
    o.gPull pull
  pullU_pin : FinitePullPin realizeU realizeU' gU (cornerCoefficient t) o.gUPull pullU
  open_pin : FiniteOpenPin (finiteInput A gU j' j g sq).j
    (finiteInput A gU j' j g sq).R realizeX realizeU o.opens.extension shriek
      (Functor.isoWhiskerRight
        (ProEtale.upperStar (ModuleCat.{u + 1} A)
          (finiteInput A gU j' j g sq).j).leftDerivedFunctorIsoMapDerivedCategory.symm
        realizeU.derived ≪≫ openPull)
  open'_pin : FiniteOpenPin (finiteInput A gU j' j g sq).j'
    (finiteInput A gU j' j g sq).S realizeX' realizeU' o.opens.extension' shriek' openPull'
  tensorX_pin : FiniteTensorPin realizeX o.tensorX tensorX
  tensorU_pin : FiniteTensorPin realizeU o.tensorU tensorU
```

```lean
def finiteGammaLeft (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} {sq : OpenImmersionSquare gU j' j g}
    [_hj : IsOpenImmersion j] [_hj' : IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) (M : FiniteD A U) (N : FiniteD A X) :
    e.realizeX.derived.obj
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((@finiteShriek A _ U X j sq.isOpenImmersion).obj M)).obj N) ⟶
    o.opens.jShriek.obj (o.tensorU.functor.obj
      (e.realizeU.derived.obj M, o.opens.jStar.obj (e.realizeX.derived.obj N))) :=
  e.realizeX.derived.map
        (@finiteGamma A _ _ U X j sq.isOpenImmersion M N) ≫
      e.shriek.hom.app
        (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
          (((ProEtale.upperStar (ModuleCat.{u + 1} A) (finiteInput A gU j' j g
            sq).j).leftDerivedFunctor).obj N)) ≫
      o.opens.jShriek.map
        (e.tensorU.hom.app (M, ((ProEtale.upperStar (ModuleCat.{u + 1} A) (finiteInput A gU j' j g
          sq).j).leftDerivedFunctor).obj N)) ≫
      o.opens.jShriek.map (o.tensorU.functor.map
        (CategoryTheory.Prod.mkHom (𝟙 _) (e.openPull.hom.app N)))
```

## New

The original module publicly imports the data module, which retains its original
public imports. All other moved definitions and proofs are unchanged.

```lean
/-- The fixed-scalar derived tensor bifunctor with explicit product endpoints.
Source: Stacks 06YU (blueprint: lem-sf-open-tensor-normalization). -/
def finiteTensor (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    FiniteD A X × FiniteD A X ⥤ FiniteD A X :=
  Functor.uncurry.obj (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)

/-- Termwise realization of fixed-scalar complexes, with explicit complex categories.
Source: Stacks 015F (blueprint: lem-sf-open-tensor-normalization). -/
def finiteComplexRealization {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) :
    CochainComplex (FiniteModules A X) ℤ ⥤ CochainComplex (Mod R) ℤ :=
  e.equivalence.functor.mapHomologicalComplex (.up ℤ)

/-- The fixed-scalar signed total complex, with its endpoints explicit.
Source: Stacks 06YN (blueprint: lem-sf-open-tensor-normalization). -/
def finiteTotal (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (P Q : CochainComplex (FiniteModules A X) ℤ) : CochainComplex (FiniteModules A X) ℤ :=
  HomologicalComplex.mapBifunctor P Q (curriedTensor (FiniteModules A X)) (.up ℤ)

/-- The source and target of the finite signed-total comparison.
Source: Stacks 06YN (blueprint: lem-sf-open-tensor-normalization). -/
def FiniteTensorTotal {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) : Type _ :=
  ∀ P Q : CochainComplex (FiniteModules A X) ℤ,
    (finiteComplexRealization e).obj
      (finiteTotal A X P Q) ≅
    (total R).obj ((finiteComplexRealization e).obj P,
      (finiteComplexRealization e).obj Q)

set_option backward.isDefEq.respectTransparency false in
/-- The total comparison carries every fixed-scalar pure bidegree summand to the
same ring-sheaf pure summand. Source: Stacks 03EK and 06YN
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteTensorPure {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i)
    (totalIso : FiniteTensorTotal e) : Prop :=
  ∀ (P Q : CochainComplex (FiniteModules A X) ℤ)
      (p q n : ℤ) (hn : p + q = n) (W : X.ProEtᵒᵖ)
      (x : (P.X p).obj.obj W) (y : (Q.X q).obj.obj W),
    ((totalIso P Q).hom.f n).val.app W
      ((e.underlying.inv.app _).hom.app W
        ((HomologicalComplex.ιMapBifunctor P Q (curriedTensor (FiniteModules A X))
          (.up ℤ) p q n hn).hom.app W (finitePure (P.X p) (Q.X q) W x y))) =
    (HomologicalComplex.ιMapBifunctor
      ((finiteComplexRealization e).obj P)
      ((finiteComplexRealization e).obj Q)
      (tensor R) (.up ℤ) p q n hn).val.app W
        (pure R (e.equivalence.functor.obj (P.X p)) (e.equivalence.functor.obj (Q.X q)) W
          ((e.underlying.inv.app (P.X p)).hom.app W x)
          ((e.underlying.inv.app (Q.X q)).hom.app W y))

set_option backward.isDefEq.respectTransparency false in
/-- The tensor comparison commutes with the finite localization map and the
ring-sheaf representative comparison. Source: Stacks 06YU and 0GL1
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteTensorModel {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (t : TensorModel R)
    (d : finiteTensor A X ⋙ e.derived ≅
      (e.derived.prod e.derived) ⋙ t.functor)
    (totalIso : FiniteTensorTotal e) : Prop :=
  ∀ (P Q : CochainComplex (FiniteModules A X) ℤ)
      (hp : resolving R ((finiteComplexRealization e).obj P))
      (hq : resolving R ((finiteComplexRealization e).obj Q)),
    HEq (e.derived.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      e.equivalence.functor.mapDerivedCategoryFactors.hom.app
        (finiteTotal A X P Q) ≫
      DerivedCategory.Q.map (totalIso P Q).hom ≫
      tensorRepresentative (R := R) t
        ((finiteComplexRealization e).obj P)
        ((finiteComplexRealization e).obj Q) hp hq)
    (d.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      t.functor.map (CategoryTheory.Prod.mkHom
        (e.equivalence.functor.mapDerivedCategoryFactors.hom.app P)
        (e.equivalence.functor.mapDerivedCategoryFactors.hom.app Q)))

/-- Finite tensor transport is fixed on every total-complex pure summand and then
on all flat K-flat representatives by the two published tensor factorizations.
Source: Stacks 03EK, 06YU, 0GL1 (blueprint: lem-sf-open-tensor-normalization). -/
def FiniteTensorPin {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (t : TensorModel R)
    (d : finiteTensor A X ⋙ e.derived ≅
      (e.derived.prod e.derived) ⋙ t.functor) : Type _ :=
  { totalIso : FiniteTensorTotal e // finiteTensorPure e totalIso ∧
    finiteTensorModel e t d totalIso }

namespace FiniteTensorPin

variable {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {e : FiniteRealization A X R i} {t : TensorModel R}
    {d : finiteTensor A X ⋙ e.derived ≅ (e.derived.prod e.derived) ⋙ t.functor}

/-- The total-complex comparison retained in the finite tensor pin.
Source: Stacks 06YU (blueprint: lem-sf-open-tensor-normalization). -/
def totalIso (p : FiniteTensorPin e t d) : FiniteTensorTotal e := p.val

/-- The retained comparison preserves every pure summand.
Source: Stacks 03EK (blueprint: lem-sf-open-tensor-normalization). -/
theorem pure_summands (p : FiniteTensorPin e t d) : finiteTensorPure e p.totalIso :=
  p.property.1

/-- The retained comparison agrees with the derived representative equation.
Source: Stacks 06YU (blueprint: lem-sf-open-tensor-normalization). -/
theorem model (p : FiniteTensorPin e t d) : finiteTensorModel e t d p.totalIso :=
  p.property.2

/-- Assemble a finite tensor pin from the same three original fields.
Source: Stacks 03EK and 06YU (blueprint: lem-sf-open-tensor-normalization). -/
def mk (totalIso : FiniteTensorTotal e) (pure_summands : finiteTensorPure e totalIso)
    (model : finiteTensorModel e t d totalIso) : FiniteTensorPin e t d :=
  ⟨totalIso, pure_summands, model⟩

end FiniteTensorPin
```

```lean
structure FiniteComparisonsCore (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} {sq : OpenImmersionSquare gU j' j g}
    [_hj : IsOpenImmersion j] [_hj' : IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t) where
  realizeX : FiniteRealization A X
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
  realizeX' : FiniteRealization A X'
    ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A))
    (toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A)))
  realizeU : FiniteRealization A U
    (restrictRing .ordinary j
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)))
    (Functor.whiskerLeft (openInclusion .ordinary j).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  realizeU' : FiniteRealization A U'
    (restrictRing .ordinary j'
      ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A)))
    (Functor.whiskerLeft (openInclusion .ordinary j').op
      (toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A))))
  shriek : finiteShriek A j ⋙ realizeX.derived ≅ realizeU.derived ⋙
    o.opens.jShriek
  shriek' : finiteShriek A j' ⋙ realizeX'.derived ≅ realizeU'.derived ⋙
    o.opens.jShriek'
  pull : finitePull A g ⋙ realizeX'.derived ≅ realizeX.derived ⋙ o.gPull.derived
  pullU : finitePull A gU ⋙ realizeU'.derived ≅ realizeU.derived ⋙ o.gUPull.derived
  openPull : (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor ⋙ realizeU.derived ≅
    realizeX.derived ⋙ o.opens.jStar
  tensorX : finiteTensor A X ⋙
    realizeX.derived ≅ (realizeX.derived.prod realizeX.derived) ⋙ o.tensorX.functor
  tensorU : finiteTensor A U ⋙
    realizeU.derived ≅ (realizeU.derived.prod realizeU.derived) ⋙ o.tensorU.functor
  openPull' : finitePull A j' ⋙ realizeU'.derived ≅
    realizeX'.derived ⋙ o.opens.jStar'
  pull_pin : FinitePullPin realizeX realizeX' g
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A))
    o.gPull pull
  pullU_pin : FinitePullPin realizeU realizeU' gU (cornerCoefficient t) o.gUPull pullU
  open_pin : FiniteOpenPin j
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))
    realizeX realizeU o.opens.extension shriek
      (Functor.isoWhiskerRight
        (ProEtale.upperStar (ModuleCat.{u + 1} A)
          j).leftDerivedFunctorIsoMapDerivedCategory.symm
        realizeU.derived ≪≫ openPull)
  open'_pin : FiniteOpenPin j'
    ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A))
    realizeX' realizeU' o.opens.extension' shriek' openPull'
  tensorX_pin : FiniteTensorPin realizeX o.tensorX tensorX
  tensorU_pin : FiniteTensorPin realizeU o.tensorU tensorU
```

```lean
def finiteGammaLeft (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} {sq : OpenImmersionSquare gU j' j g}
    [_hj : IsOpenImmersion j] [_hj' : IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) (M : FiniteD A U) (N : FiniteD A X) :
    e.realizeX.derived.obj
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((@finiteShriek A _ U X j sq.isOpenImmersion).obj M)).obj N) ⟶
    o.opens.jShriek.obj (o.tensorU.functor.obj
      (e.realizeU.derived.obj M, o.opens.jStar.obj (e.realizeX.derived.obj N))) :=
  e.realizeX.derived.map
        (@finiteGamma A _ _ U X j sq.isOpenImmersion M N) ≫
      e.shriek.hom.app
        (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
          (((ProEtale.upperStar (ModuleCat.{u + 1} A)
            j).leftDerivedFunctor).obj N)) ≫
      o.opens.jShriek.map
        (e.tensorU.hom.app (M, ((ProEtale.upperStar (ModuleCat.{u + 1} A)
            j).leftDerivedFunctor).obj N)) ≫
      o.opens.jShriek.map (o.tensorU.functor.map
        (CategoryTheory.Prod.mkHom (𝟙 _) (e.openPull.hom.app N)))
```

## Users

The table includes the 19 consumers checked by the original downstream query and
276 potential consumers found by a fresh import-graph and interface-name scan.
The latter is conservative: common instance signatures also match unrelated uses.
Every moved declaration is still publicly reexported with its original name and
signature. None of these consumers uses the removed `FiniteTensorPin` recursors,
constructor, or projections; the finite pin still specifies the same total comparison
and two equations. Thus consumer statements retain their meaning and need no edits.
The 19 consumers marked compiled were checked against the overlay without edits;
the remaining rows record interface inspection, not additional compilation.

| module | unclaimed | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence | T2 | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Same public reexport; no pin recursor use; no edits. |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | P4 | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.SmoothPurityCompactProjectionData | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.SmoothPurityCompactProjectionFinitePresentation | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.SmoothPurityCompactProjectionTensorSquare | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerOperations | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerPresentation | unclaimed | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.SystemTensorMateArrows | H8 | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassChern | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.OpenTensorNormalization | X8 | Imports the factored data; proves the categorical reduction. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | S4 | Same public reexport; unchanged consumer compiled without edits. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Same public reexport; no pin recursor use; no edits. |
| WeilConjectures | unclaimed | Same public reexport; no pin recursor use; no edits. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same public reexport; no pin recursor use; no edits. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same public reexport; no pin recursor use; no edits. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same public reexport; no pin recursor use; no edits. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same public reexport; no pin recursor use; no edits. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same public reexport; no pin recursor use; no edits. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same public reexport; no pin recursor use; no edits. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same public reexport; no pin recursor use; no edits. |
| module | unclaimed | Same public reexport; no pin recursor use; no edits. |

## Status

landed 20261020T221404-L-4182007 2026-10-20 (merge of deliver/X8/Sheaf.SixFunctors.OpenTensorNormalization)
