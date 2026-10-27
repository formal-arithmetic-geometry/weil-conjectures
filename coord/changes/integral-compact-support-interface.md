# AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport interface

## Reason

Extract the existing categories, functors, adjunction mates and coherence predicates into
`Sheaf.SixFunctors.IntegralCompactSupportDefs`. Supporting normalization and base-change
lemmas can then use the interface without importing the theorem that calls them.
The entire public declaration block and its cached instance environment are preserved.
No functor, signature, universe, coefficient predicate or target statement changes. The original
module publicly imports the data module, so all original public imports and declarations
remain available to consumers. The independent reader should check the extraction and
public re-export; no consumer adaptation is needed.

## Old

In `Sheaf.SixFunctors.IntegralLocalizingCompactSupport`:

```lean
abbrev Ambient (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The actual total derived inverse image of module objects.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: det-prop-int-brown-construction). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) : Ambient Λ Y ⥤ Ambient Λ X :=
  moduleDerivedPullback Λ f

/-- The actual total right-derived direct image of module objects.
Source: blueprint sk-prop-int-brown-construction, displayed composite
(blueprint: det-prop-int-brown-construction). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) : Ambient Λ X ⥤ Ambient Λ Y :=
  moduleDerivedPushforward Λ f

/-- Exact, termwise extension by zero.
Source: blueprint sk-prop-int-brown-construction, displayed composite
(blueprint: det-prop-int-brown-construction). -/
abbrev extend {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Ambient Λ X ⥤ Ambient Λ Y :=
  (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- The existing compactification composite, with no new choice of compactification.
Source: blueprint sk-prop-int-brown-construction, displayed formula
(blueprint: det-prop-int-brown-construction). -/
abbrev image {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Ambient Λ X ⥤ Ambient Λ Y :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- The recorded finite-constant-model bounded constructible generators.
Source: blueprint sk-prop-int-brown-construction and sk-def-sfb-constructible
(blueprint: det-prop-int-brown-construction). -/
abbrev generators (X : Scheme.{u}) : ObjectProperty (Ambient Λ X) :=
  constantModelBoundedConstructible Λ X

/-- Loc of Dbc, formed by the recorded ordinary localizing-closure operation.
Source: blueprint sk-prop-int-brown-construction, first paragraph
(blueprint: det-prop-int-brown-construction). -/
def localizing (X : Scheme.{u}) : ObjectProperty (Ambient Λ X) :=
  CategoryTheory.localizingClosure (generators Λ X)

/-- The open adjunction with the actual total derived pullback, transported along
its canonical identification with the levelwise pullback.
Source: blueprint sk-prop-int-brown-construction, comparison construction
(blueprint: det-prop-int-brown-construction). -/
def openAdjunction {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    extend Λ j ⊣ pull Λ j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm

/-- The pullback-square comparison, using the given equality of scheme morphisms.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: det-prop-int-brown-construction). -/
def pullSquare {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : CommSq u' f' f v) :
    pull Λ v ⋙ pull Λ f' ≅ pull Λ f ⋙ pull Λ u' :=
  (leftDerivedUpperStarComp Λ f' v).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y => pull Λ h) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ u' f

/-- The proper direct-image exchange: unit, square transport, then counit.
This definition makes sense before asserting that the map is invertible.
Source: blueprint sk-prop-int-brown-construction, proof final paragraph
(blueprint: det-prop-int-brown-construction). -/
def pushExchange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : CommSq u' f' f v) :
    push Λ f ⋙ pull Λ v ⟶ pull Λ u' ⋙ push Λ f' :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (derivedUpperStarLowerStarAdjunction Λ f').unit ≫
    (Functor.squareTransport (push Λ f) (push Λ f') (pullSquare Λ sq)).hom ≫
    Functor.whiskerRight (derivedUpperStarLowerStarAdjunction Λ f).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The open exchange in its mate direction, again before asserting invertibility.
Source: blueprint sk-prop-int-brown-construction, proof final paragraph
(blueprint: det-prop-int-brown-construction). -/
def openExchange {X Z X' Z' : Scheme.{u}}
    {j : X ⟶ Z} {w : Z' ⟶ Z} {j' : X' ⟶ Z'} {u' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : CommSq u' j' j w) :
    pull Λ u' ⋙ extend Λ j' ⟶ extend Λ j ⋙ pull Λ w :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (openAdjunction Λ j).unit _ ≫
    (Functor.squareTransport (extend Λ j) (extend Λ j')
      (pullSquare Λ sq.flip)).hom ≫
    Functor.whiskerLeft _ (openAdjunction Λ j').counit ≫
    (Functor.rightUnitor _).hom

/-- Canonical composition of total derived pushforwards, conjugate to pullback
composition under the recorded derived adjunctions.
Source: blueprint sk-prop-int-brown-construction, compactification comparisons
(blueprint: det-prop-int-brown-construction). -/
def pushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push Λ f ⋙ push Λ g ≅ push Λ (f ≫ g) :=
  conjugateIsoEquiv
    ((derivedUpperStarLowerStarAdjunction Λ g).comp
      (derivedUpperStarLowerStarAdjunction Λ f))
    (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (leftDerivedUpperStarComp Λ f g)

/-- The restriction map which normalizes a proper-open refinement comparison.
It uses pullback composition followed by the actual proper adjunction counit.
Source: blueprint sk-prop-int-brown-construction, comparison proof
(blueprint: det-prop-int-brown-construction). -/
def refinementRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X) :
    (pull Λ d.i).obj ((push Λ r.hom).obj ((extend Λ c.i).obj K)) ⟶
      (pull Λ c.i).obj ((extend Λ c.i).obj K) :=
  ((eqToIso (congrArg (fun h : X ⟶ d.Z => pull Λ h) r.i_hom.symm) ≪≫
    leftDerivedUpperStarComp Λ c.i r.hom).hom.app _) ≫
      (pull Λ c.i).map
        ((derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app _)

/-- The normalized refinement comparison, once its proper-open isomorphism is given.
The latter will be required to satisfy the open-adjunction normalization in the theorem.
Source: blueprint sk-prop-int-brown-construction, comparison proof
(blueprint: det-prop-int-brown-construction). -/
def refinementIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : (extend Λ d.i).obj K ≅ (push Λ r.hom).obj ((extend Λ c.i).obj K)) :
    (image Λ c).obj K ≅ (image Λ d).obj K :=
  ((pushComp Λ r.hom d.g ≪≫
    eqToIso (congrArg (fun h : c.Z ⟶ Y => push Λ h) r.hom_g)).symm.app _) ≪≫
      (push Λ d.g).mapIso e.symm

/-- The compact-support base-change map: proper exchange followed by inverse open
exchange, with the latter inverse specified by an `IsIso` proof, never chosen freely.
Source: blueprint sk-prop-int-brown-construction, last paragraph
(blueprint: det-prop-int-brown-construction). -/
def baseChange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (h : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)) :
    image Λ c ⋙ pull Λ v ⟶ pull Λ u' ⋙ image Λ (c.ofIsPullback sq) :=
  @id _ (by
    letI := h
    exact (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (extend Λ c.i)
        (pushExchange Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (asIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)).inv
        (push Λ (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom)

variable (k : Type u) [Field k]

/-- The full category of the standing separated finite-type k-schemes. Bundling over
Spec k ensures that every morphism is a k-morphism, with no extra condition on it.
Source: blueprint sk-def-sfb-dc-setting, used in sk-prop-int-brown-construction
(blueprint: det-prop-int-brown-construction). -/
abbrev Spaces :=
  ObjectProperty.FullSubcategory (fun X : Over (Spec (.of k)) =>
    IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- Quasi-compact compactifications, precisely the recorded Nagata datum.
Source: blueprint sk-prop-int-brown-construction, second paragraph
(blueprint: det-prop-int-brown-construction). -/
abbrev Compactifications {X Y : Spaces k} (f : X ⟶ Y) :=
  Compactification.QuasiCompactObjects f.hom.left

/-- The source inclusion followed by the actual compactification composite. The
codomain is displayed in the ambient category; preservation below is what restricts it.
Source: blueprint sk-prop-int-brown-construction, displayed functor
(blueprint: det-prop-int-brown-construction). -/
abbrev candidate {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f) :=
  (localizing Λ X.obj.left).ι ⋙ image Λ c.obj

/-- Pull back the specified compactification. Quasi-compactness of its open immersion
is transported by the recorded pullback square, rather than assumed afresh.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: det-prop-int-brown-construction). -/
def baseCompactification {X Y X' Y' : Spaces k}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactifications k f)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left) :
    Compactifications k f' :=
  ⟨c.obj.ofIsPullback sq,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (c.obj.isPullback_i_ofIsPullback sq) c.property⟩

/-- The four preservation clauses. Exactness is stated by the ambient distinguished
triangles with all three vertices in Loc. Coproduct preservation means preserving every
ordinary ambient coproduct cocone on objects in Loc, in the indexing universe of the
recorded localizing closure. The last clause is preservation of the specified Dbc.
Source: blueprint sk-prop-int-brown-construction, displayed functor and next sentence
(blueprint: det-prop-int-brown-construction). -/
structure Preservation : Prop where
  maps_localizing : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (K : Ambient Λ X.obj.left), localizing Λ X.obj.left K →
      localizing Λ Y.obj.left ((image Λ c.obj).obj K)
  exact : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (T : Pretriangulated.Triangle (Ambient Λ X.obj.left)),
      localizing Λ X.obj.left T.obj₁ → localizing Λ X.obj.left T.obj₂ →
      localizing Λ X.obj.left T.obj₃ →
      T ∈ distTriang (Ambient Λ X.obj.left) →
        (image Λ c.obj).mapTriangle.obj T ∈
          distTriang (Ambient Λ Y.obj.left)
  coproducts : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (I : Type (u + 2)) (F : Discrete I ⥤ Ambient Λ X.obj.left),
      (∀ i : I, localizing Λ X.obj.left (F.obj (Discrete.mk i))) →
        PreservesColimit F (image Λ c.obj)
  maps_constructible : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (K : Ambient Λ X.obj.left), generators Λ X.obj.left K →
      generators Λ Y.obj.left ((image Λ c.obj).obj K)

/-- Natural comparison maps on Loc for all pairs of compactifications.
Source: blueprint sk-prop-int-brown-construction, independence clause
(blueprint: det-prop-int-brown-construction). -/
abbrev Comparisons :=
  ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f),
    candidate Λ k c ≅ candidate Λ k d

/-- Natural composition isomorphisms, for any choices for f, g and gf. Compatibility
with the compactification comparisons is required in `Coherence`.
Source: blueprint sk-prop-int-brown-construction, composition clause
(blueprint: det-prop-int-brown-construction). -/
abbrev Compositions :=
  ∀ {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactifications k f) (d : Compactifications k g)
    (e : Compactifications k (f ≫ g)),
      candidate Λ k c ⋙ image Λ d.obj ≅ candidate Λ k e

/-- Canonicity, identity, cocycle, composition and base-change compatibility for the
specified module-object compact-support functors. Normalization on a boundary refinement
uses the actual proper counit and open unit. The base-change map is the specified mate,
not an arbitrary isomorphism with the right source and target.

All maps are natural transformations on full subcategories of the same ambient derived
categories. Preservation of generators and of pullback, recorded in `constructible_pull`,
therefore restricts these very same maps and equations to Dbc.

Source: blueprint sk-prop-int-brown-construction, last three sentences
(blueprint: det-prop-int-brown-construction). -/
structure Coherence (h : Preservation Λ k) (φ : Comparisons Λ k)
    (μ : Compositions Λ k) : Prop where
  identity : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactifications k f),
    φ f c c = Iso.refl _
  cocycle : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d e : Compactifications k f),
    φ f c d ≪≫ φ f d e = φ f c e
  normalized : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing Λ X.obj.left).FullSubcategory),
      ∃ e : (extend Λ d.obj.i).obj K.obj ≅
          (push Λ r.hom).obj ((extend Λ c.obj.i).obj K.obj),
        (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction Λ r K.obj = (openAdjunction Λ c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso Λ r K.obj e
  composition_compatibility : ∀ {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c c' : Compactifications k f) (d d' : Compactifications k g)
    (e e' : Compactifications k (f ≫ g))
    (K : (localizing Λ X.obj.left).FullSubcategory),
      (image Λ d.obj).map ((φ f c c').hom.app K) ≫
          (φ g d d').hom.app
            ⟨(image Λ c'.obj).obj K.obj, h.maps_localizing c' K.obj K.property⟩ ≫
          (μ f g c' d' e').hom.app K =
        (μ f g c d e).hom.app K ≫ (φ (f ≫ g) e e').hom.app K
  constructible_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient Λ Y.obj.left),
    generators Λ Y.obj.left K →
      generators Λ X.obj.left ((pull Λ v.hom.left).obj K)
  localizing_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient Λ Y.obj.left),
    localizing Λ Y.obj.left K →
      localizing Λ X.obj.left ((pull Λ v.hom.left).obj K)
  base_change : ∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactifications k f),
      ∃ ho : IsIso (openExchange Λ (c.obj.isPullback_i_ofIsPullback sq).toCommSq),
        ∀ K : (localizing Λ X.obj.left).FullSubcategory,
          IsIso ((baseChange Λ c.obj sq ho).app K.obj)
  base_change_compatibility : ∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c d : Compactifications k f)
    (hc : IsIso (openExchange Λ (c.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange Λ (d.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (K : (localizing Λ X.obj.left).FullSubcategory),
      (pull Λ v.hom.left).map ((φ f c d).hom.app K) ≫
          (baseChange Λ d.obj sq hd).app K.obj =
        (baseChange Λ c.obj sq hc).app K.obj ≫
          (φ f' (baseCompactification k c sq) (baseCompactification k d sq)).hom.app
            ⟨(pull Λ u'.hom.left).obj K.obj, localizing_pull u' K.obj K.property⟩
```

## New

The same declarations now reside in `Sheaf.SixFunctors.IntegralCompactSupportDefs`:

```lean
abbrev Ambient (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The actual total derived inverse image of module objects.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: det-prop-int-brown-construction). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) : Ambient Λ Y ⥤ Ambient Λ X :=
  moduleDerivedPullback Λ f

/-- The actual total right-derived direct image of module objects.
Source: blueprint sk-prop-int-brown-construction, displayed composite
(blueprint: det-prop-int-brown-construction). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) : Ambient Λ X ⥤ Ambient Λ Y :=
  moduleDerivedPushforward Λ f

/-- Exact, termwise extension by zero.
Source: blueprint sk-prop-int-brown-construction, displayed composite
(blueprint: det-prop-int-brown-construction). -/
abbrev extend {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Ambient Λ X ⥤ Ambient Λ Y :=
  (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- The existing compactification composite, with no new choice of compactification.
Source: blueprint sk-prop-int-brown-construction, displayed formula
(blueprint: det-prop-int-brown-construction). -/
abbrev image {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Ambient Λ X ⥤ Ambient Λ Y :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- The recorded finite-constant-model bounded constructible generators.
Source: blueprint sk-prop-int-brown-construction and sk-def-sfb-constructible
(blueprint: det-prop-int-brown-construction). -/
abbrev generators (X : Scheme.{u}) : ObjectProperty (Ambient Λ X) :=
  constantModelBoundedConstructible Λ X

/-- Loc of Dbc, formed by the recorded ordinary localizing-closure operation.
Source: blueprint sk-prop-int-brown-construction, first paragraph
(blueprint: det-prop-int-brown-construction). -/
def localizing (X : Scheme.{u}) : ObjectProperty (Ambient Λ X) :=
  CategoryTheory.localizingClosure (generators Λ X)

/-- The open adjunction with the actual total derived pullback, transported along
its canonical identification with the levelwise pullback.
Source: blueprint sk-prop-int-brown-construction, comparison construction
(blueprint: det-prop-int-brown-construction). -/
def openAdjunction {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    extend Λ j ⊣ pull Λ j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm

/-- The pullback-square comparison, using the given equality of scheme morphisms.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: det-prop-int-brown-construction). -/
def pullSquare {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : CommSq u' f' f v) :
    pull Λ v ⋙ pull Λ f' ≅ pull Λ f ⋙ pull Λ u' :=
  (leftDerivedUpperStarComp Λ f' v).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y => pull Λ h) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ u' f

/-- The proper direct-image exchange: unit, square transport, then counit.
This definition makes sense before asserting that the map is invertible.
Source: blueprint sk-prop-int-brown-construction, proof final paragraph
(blueprint: det-prop-int-brown-construction). -/
def pushExchange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : CommSq u' f' f v) :
    push Λ f ⋙ pull Λ v ⟶ pull Λ u' ⋙ push Λ f' :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (derivedUpperStarLowerStarAdjunction Λ f').unit ≫
    (Functor.squareTransport (push Λ f) (push Λ f') (pullSquare Λ sq)).hom ≫
    Functor.whiskerRight (derivedUpperStarLowerStarAdjunction Λ f).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The open exchange in its mate direction, again before asserting invertibility.
Source: blueprint sk-prop-int-brown-construction, proof final paragraph
(blueprint: det-prop-int-brown-construction). -/
def openExchange {X Z X' Z' : Scheme.{u}}
    {j : X ⟶ Z} {w : Z' ⟶ Z} {j' : X' ⟶ Z'} {u' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : CommSq u' j' j w) :
    pull Λ u' ⋙ extend Λ j' ⟶ extend Λ j ⋙ pull Λ w :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (openAdjunction Λ j).unit _ ≫
    (Functor.squareTransport (extend Λ j) (extend Λ j')
      (pullSquare Λ sq.flip)).hom ≫
    Functor.whiskerLeft _ (openAdjunction Λ j').counit ≫
    (Functor.rightUnitor _).hom

/-- Canonical composition of total derived pushforwards, conjugate to pullback
composition under the recorded derived adjunctions.
Source: blueprint sk-prop-int-brown-construction, compactification comparisons
(blueprint: det-prop-int-brown-construction). -/
def pushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push Λ f ⋙ push Λ g ≅ push Λ (f ≫ g) :=
  conjugateIsoEquiv
    ((derivedUpperStarLowerStarAdjunction Λ g).comp
      (derivedUpperStarLowerStarAdjunction Λ f))
    (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (leftDerivedUpperStarComp Λ f g)

/-- The restriction map which normalizes a proper-open refinement comparison.
It uses pullback composition followed by the actual proper adjunction counit.
Source: blueprint sk-prop-int-brown-construction, comparison proof
(blueprint: det-prop-int-brown-construction). -/
def refinementRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X) :
    (pull Λ d.i).obj ((push Λ r.hom).obj ((extend Λ c.i).obj K)) ⟶
      (pull Λ c.i).obj ((extend Λ c.i).obj K) :=
  ((eqToIso (congrArg (fun h : X ⟶ d.Z => pull Λ h) r.i_hom.symm) ≪≫
    leftDerivedUpperStarComp Λ c.i r.hom).hom.app _) ≫
      (pull Λ c.i).map
        ((derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app _)

/-- The normalized refinement comparison, once its proper-open isomorphism is given.
The latter will be required to satisfy the open-adjunction normalization in the theorem.
Source: blueprint sk-prop-int-brown-construction, comparison proof
(blueprint: det-prop-int-brown-construction). -/
def refinementIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : (extend Λ d.i).obj K ≅ (push Λ r.hom).obj ((extend Λ c.i).obj K)) :
    (image Λ c).obj K ≅ (image Λ d).obj K :=
  ((pushComp Λ r.hom d.g ≪≫
    eqToIso (congrArg (fun h : c.Z ⟶ Y => push Λ h) r.hom_g)).symm.app _) ≪≫
      (push Λ d.g).mapIso e.symm

/-- The compact-support base-change map: proper exchange followed by inverse open
exchange, with the latter inverse specified by an `IsIso` proof, never chosen freely.
Source: blueprint sk-prop-int-brown-construction, last paragraph
(blueprint: det-prop-int-brown-construction). -/
def baseChange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (h : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)) :
    image Λ c ⋙ pull Λ v ⟶ pull Λ u' ⋙ image Λ (c.ofIsPullback sq) :=
  @id _ (by
    letI := h
    exact (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (extend Λ c.i)
        (pushExchange Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (asIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)).inv
        (push Λ (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom)

variable (k : Type u) [Field k]

/-- The full category of the standing separated finite-type k-schemes. Bundling over
Spec k ensures that every morphism is a k-morphism, with no extra condition on it.
Source: blueprint sk-def-sfb-dc-setting, used in sk-prop-int-brown-construction
(blueprint: det-prop-int-brown-construction). -/
abbrev Spaces :=
  ObjectProperty.FullSubcategory (fun X : Over (Spec (.of k)) =>
    IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- Quasi-compact compactifications, precisely the recorded Nagata datum.
Source: blueprint sk-prop-int-brown-construction, second paragraph
(blueprint: det-prop-int-brown-construction). -/
abbrev Compactifications {X Y : Spaces k} (f : X ⟶ Y) :=
  Compactification.QuasiCompactObjects f.hom.left

/-- The source inclusion followed by the actual compactification composite. The
codomain is displayed in the ambient category; preservation below is what restricts it.
Source: blueprint sk-prop-int-brown-construction, displayed functor
(blueprint: det-prop-int-brown-construction). -/
abbrev candidate {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f) :=
  (localizing Λ X.obj.left).ι ⋙ image Λ c.obj

/-- Pull back the specified compactification. Quasi-compactness of its open immersion
is transported by the recorded pullback square, rather than assumed afresh.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: det-prop-int-brown-construction). -/
def baseCompactification {X Y X' Y' : Spaces k}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactifications k f)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left) :
    Compactifications k f' :=
  ⟨c.obj.ofIsPullback sq,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (c.obj.isPullback_i_ofIsPullback sq) c.property⟩

/-- The four preservation clauses. Exactness is stated by the ambient distinguished
triangles with all three vertices in Loc. Coproduct preservation means preserving every
ordinary ambient coproduct cocone on objects in Loc, in the indexing universe of the
recorded localizing closure. The last clause is preservation of the specified Dbc.
Source: blueprint sk-prop-int-brown-construction, displayed functor and next sentence
(blueprint: det-prop-int-brown-construction). -/
structure Preservation : Prop where
  maps_localizing : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (K : Ambient Λ X.obj.left), localizing Λ X.obj.left K →
      localizing Λ Y.obj.left ((image Λ c.obj).obj K)
  exact : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (T : Pretriangulated.Triangle (Ambient Λ X.obj.left)),
      localizing Λ X.obj.left T.obj₁ → localizing Λ X.obj.left T.obj₂ →
      localizing Λ X.obj.left T.obj₃ →
      T ∈ distTriang (Ambient Λ X.obj.left) →
        (image Λ c.obj).mapTriangle.obj T ∈
          distTriang (Ambient Λ Y.obj.left)
  coproducts : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (I : Type (u + 2)) (F : Discrete I ⥤ Ambient Λ X.obj.left),
      (∀ i : I, localizing Λ X.obj.left (F.obj (Discrete.mk i))) →
        PreservesColimit F (image Λ c.obj)
  maps_constructible : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (K : Ambient Λ X.obj.left), generators Λ X.obj.left K →
      generators Λ Y.obj.left ((image Λ c.obj).obj K)

/-- Natural comparison maps on Loc for all pairs of compactifications.
Source: blueprint sk-prop-int-brown-construction, independence clause
(blueprint: det-prop-int-brown-construction). -/
abbrev Comparisons :=
  ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f),
    candidate Λ k c ≅ candidate Λ k d

/-- Natural composition isomorphisms, for any choices for f, g and gf. Compatibility
with the compactification comparisons is required in `Coherence`.
Source: blueprint sk-prop-int-brown-construction, composition clause
(blueprint: det-prop-int-brown-construction). -/
abbrev Compositions :=
  ∀ {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactifications k f) (d : Compactifications k g)
    (e : Compactifications k (f ≫ g)),
      candidate Λ k c ⋙ image Λ d.obj ≅ candidate Λ k e

/-- Canonicity, identity, cocycle, composition and base-change compatibility for the
specified module-object compact-support functors. Normalization on a boundary refinement
uses the actual proper counit and open unit. The base-change map is the specified mate,
not an arbitrary isomorphism with the right source and target.

All maps are natural transformations on full subcategories of the same ambient derived
categories. Preservation of generators and of pullback, recorded in `constructible_pull`,
therefore restricts these very same maps and equations to Dbc.

Source: blueprint sk-prop-int-brown-construction, last three sentences
(blueprint: det-prop-int-brown-construction). -/
structure Coherence (h : Preservation Λ k) (φ : Comparisons Λ k)
    (μ : Compositions Λ k) : Prop where
  identity : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactifications k f),
    φ f c c = Iso.refl _
  cocycle : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d e : Compactifications k f),
    φ f c d ≪≫ φ f d e = φ f c e
  normalized : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing Λ X.obj.left).FullSubcategory),
      ∃ e : (extend Λ d.obj.i).obj K.obj ≅
          (push Λ r.hom).obj ((extend Λ c.obj.i).obj K.obj),
        (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction Λ r K.obj = (openAdjunction Λ c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso Λ r K.obj e
  composition_compatibility : ∀ {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c c' : Compactifications k f) (d d' : Compactifications k g)
    (e e' : Compactifications k (f ≫ g))
    (K : (localizing Λ X.obj.left).FullSubcategory),
      (image Λ d.obj).map ((φ f c c').hom.app K) ≫
          (φ g d d').hom.app
            ⟨(image Λ c'.obj).obj K.obj, h.maps_localizing c' K.obj K.property⟩ ≫
          (μ f g c' d' e').hom.app K =
        (μ f g c d e).hom.app K ≫ (φ (f ≫ g) e e').hom.app K
  constructible_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient Λ Y.obj.left),
    generators Λ Y.obj.left K →
      generators Λ X.obj.left ((pull Λ v.hom.left).obj K)
  localizing_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient Λ Y.obj.left),
    localizing Λ Y.obj.left K →
      localizing Λ X.obj.left ((pull Λ v.hom.left).obj K)
  base_change : ∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactifications k f),
      ∃ ho : IsIso (openExchange Λ (c.obj.isPullback_i_ofIsPullback sq).toCommSq),
        ∀ K : (localizing Λ X.obj.left).FullSubcategory,
          IsIso ((baseChange Λ c.obj sq ho).app K.obj)
  base_change_compatibility : ∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c d : Compactifications k f)
    (hc : IsIso (openExchange Λ (c.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange Λ (d.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (K : (localizing Λ X.obj.left).FullSubcategory),
      (pull Λ v.hom.left).map ((φ f c d).hom.app K) ≫
          (baseChange Λ d.obj sq hd).app K.obj =
        (baseChange Λ c.obj sq hc).app K.obj ≫
          (φ f' (baseCompactification k c sq) (baseCompactification k d sq)).hom.app
            ⟨(pull Λ u'.hom.left).obj K.obj, localizing_pull u' K.obj K.property⟩
```

The original module publicly re-exports this module. Its eight original public imports
are the eight public imports of the extracted module. No functor or predicate changes.

## Users

The table is the union of the import closure and textual users reported by
`tools/downstream.py Sheaf.SixFunctors.IntegralLocalizingCompactSupport --uses
IntegralCompactSupport`, refreshed on 2026-10-25 after resumption (232 downstream modules and 16 textual-user modules). Every original qualified declaration
and its definitionally equal body remain available by the public re-export. This extraction has no
mathematical effect on any target or consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | J9 | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | D3 | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | K5 | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Identical interface through public re-export; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Identical interface through public re-export; no adaptation. |
| TargetsCheck | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.Statement | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Identical interface through public re-export; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Identical interface through public re-export; no adaptation. |

| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | Not queried; no adaptation | Identical interface through public re-export; no adaptation. |

## Status

landed 20261025T163606-L-709450 2026-10-25 (merge of deliver/D3/Sheaf.SixFunctors.IntegralLocalizingCompactSupport)
