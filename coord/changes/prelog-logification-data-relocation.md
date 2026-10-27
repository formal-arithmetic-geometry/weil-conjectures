# AlgebraicGeometry.PrelogPushoutPresentation and related logification data

## Reason

The item originally declared both the presentation data and the theorem needing those data.
New geometric subarguments must refer to the same predicates without importing their own
consumer and closing an import cycle. Move the 17 existing public definitions and structures
into `Sheaf.AlgebraicGeometry.PrelogLogificationData`; the original item publicly re-exports
that module. Every declaration name, universe, signature and definition body is preserved.
Only their docstrings now point to the new definition node. The old file-level transparency
relaxations are unnecessary and are removed; no module in this delivery enables them.

The original theorem retains its complete signature and all thirteen clauses. Its new proof
constructs the inverse images and both étale logifications and combines two genuine geometric
subarguments. This is a decomposition, not a completion of the full logarithmic argument.
No adopted source-library file changes.

## Old

Original item import header, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.ZariskiLogStructure
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.CoverLifting
```

The definitions below occurred in that item immediately before its theorem; their declaration
text is reproduced verbatim here to make the relocation reviewable:

```lean
/-- The existing quotient pushout, for an arbitrary ring-valued prelog map.
Source: ILO VI 1.1; VIII 3.3.2
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def prelogPairClass (A : CommRingCat.{u}) {P : Type u} [CommMonoid P]
    (β : P →* A) (p : P) (a : Aˣ) : divisorialChartPushout β.mrangeRestrict :=
  (divisorialChartCongruence β.mrangeRestrict).mk' (p, a)

/-- Naturality for maps from the sectionwise pushouts, expressed on their exhaustive
pair representatives. This specifies precisely the quotient-presheaf restriction maps.
Source: ILO VI 1.1; VIII 3.3.2
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogPairNatural {C : Type v} [Category.{w} C]
    (P : Cᵒᵖ ⥤ CommMonCat.{u}) (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (β : P ⟶ R ⋙ forget₂ CommRingCat CommMonCat) (H : Cᵒᵖ ⥤ CommMonCat.{u})
    (q : ∀ U : Cᵒᵖ,
      divisorialChartPushout (A := R.obj U) (β.app U).hom.mrangeRestrict →* H.obj U) : Prop :=
  ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (p : P.obj U) (a : (R.obj U)ˣ),
    H.map f (q U (prelogPairClass (R.obj U) (β.app U).hom p a)) =
      q V (prelogPairClass (R.obj V) (β.app V).hom (P.map f p) (Units.map (R.map f).hom a))

/-- The monoid-sheafification of the actual sectionwise pushout, together with its
structural map and prelog inclusion. The universal clause ranges over all monoid
sheaves, not just log structures. Thus it is exactly sheafification, including its unit.
Source: ILO VI 1.1; VIII 3.3.2
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
structure PrelogPushoutPresentation {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ CommMonCat.{u})
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) (β : P ⟶ R ⋙ forget₂ CommRingCat CommMonCat)
    (L : Sheaf J CommMonCat.{u}) (α : L.obj ⟶ R ⋙ forget₂ CommRingCat CommMonCat) where
  pairMap : ∀ U : Cᵒᵖ,
    divisorialChartPushout (A := R.obj U) (β.app U).hom.mrangeRestrict →* L.obj.obj U
  naturality : PrelogPairNatural P R β L.obj pairMap
  structural : ∀ (U : Cᵒᵖ) (p : P.obj U) (a : (R.obj U)ˣ),
    α.app U (pairMap U (prelogPairClass (R.obj U) (β.app U).hom p a)) =
      @id (R.obj U) (β.app U p) * a.val
  iota : P ⟶ L.obj
  iota_pair : ∀ (U : Cᵒᵖ) (p : P.obj U),
    iota.app U p = pairMap U (prelogPairClass (R.obj U) (β.app U).hom p 1)
  universal : ∀ (H : Sheaf J CommMonCat.{u})
    (q : ∀ U : Cᵒᵖ,
      divisorialChartPushout (A := R.obj U) (β.app U).hom.mrangeRestrict →* H.obj.obj U),
    PrelogPairNatural P R β H.obj q →
    ∃! f : L ⟶ H, ∀ (U : Cᵒᵖ)
      (z : divisorialChartPushout (A := R.obj U) (β.app U).hom.mrangeRestrict),
      f.hom.app U (pairMap U z) = q U z

/-- The open image of an étale object, with its canonical functoriality.
Source: ILO VIII §3; Stacks 02GP
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def prelogEtaleImage (X : Scheme.{u}) : X.Etale ⥤ X.Opens where
  obj W := ⟨Set.range W.hom, W.hom.isOpenMap.isOpen_range⟩
  map {V W} f := homOfLE (by
    rintro x ⟨y, rfl⟩
    exact ⟨f.left y, congr($(MorphismProperty.Over.w f) y)⟩)

/-- Pullback of regular functions to an étale object from its open image.
Source: ILO VIII §3
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def prelogImageFunctions {X : Scheme.{u}} (W : X.Etale) :
    Γ(X, (prelogEtaleImage X).obj W) ⟶ Γ(W.left, ⊤) :=
  W.hom.appLE ((prelogEtaleImage X).obj W) ⊤ (by
    intro y _
    exact ⟨y, rfl⟩)

/-- The canonical monoid inverse image and the induced prelog map. Its underlying
sheaf is the sheafification of the raw inverse-image diagram, normalized by pullback
of functions on open images. The universal property determines it up to unique
isomorphism, including the map from the raw presheaf.
Source: ILO VIII §3 and 3.3.2
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
structure PrelogEtaleInverseImage {X : Scheme.{u}} (P : ZariskiPrelogStructure X) where
  prelog : EtalePrelogStructure X
  unit : (prelogEtaleImage X).op ⋙ P.monoidSheaf.obj ⟶ prelog.monoidSheaf.obj
  structural : ∀ (W : X.Etale) (p : P.monoidSheaf.obj.obj
      (op ((prelogEtaleImage X).obj W))),
    prelog.alpha.app (op W) (unit.app (op W) p) =
      prelogImageFunctions W (P.alpha.app (op ((prelogEtaleImage X).obj W)) p)
  universal : ∀ H : Sheaf X.smallEtaleTopology CommMonCat.{u},
    Function.Bijective (fun f : prelog.monoidSheaf ⟶ H ↦ unit ≫ f.hom)

/-- The sheafified quotient by units, with its quotient map. For a log structure its
monoid units are precisely the inverse image of the structural units. Hence this
is the characteristic sheaf `(L / Oˣ)#`, with its specified quotient map.
Source: ILO VI 1.1; VIII 3.3.2
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
structure PrelogCharacteristicPresentation {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) (L K : Sheaf J CommMonCat.{u}) where
  quotientMap : L ⟶ K
  killsUnits : ∀ (U : Cᵒᵖ) (a : (L.obj.obj U)ˣ), quotientMap.hom.app U a.val = 1
  universal : ∀ (H : Sheaf J CommMonCat.{u}) (f : L ⟶ H),
    (∀ (U : Cᵒᵖ) (a : (L.obj.obj U)ˣ), f.hom.app U a.val = 1) →
    ∃! g : K ⟶ H, quotientMap ≫ g = f

/-- The canonical map of ordinary local functions to the strict local ring, using
an arbitrary neighborhood representative. The displayed germ equations below
characterize the local-ring map uniquely, so no unrelated ring map is substituted.
Source: ILO VIII §3 and the proof of the node, Step 7
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def IsPrelogLocalRingMap {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (ρ : X.presheaf.stalk (t default) →+* strictLocalRing X t) : Prop :=
  ∀ (U : X.Opens) (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk U.ι))
    (hx : t default ∈ U) (a : Γ(X, U)),
    ρ (X.presheaf.germ U (t default) hx a) =
      strictLocalGerm X t (Scheme.Etale.mk U.ι) w (U.topIso.inv a)

/-- A canonical map from the Zariski prelog sheaf to its Zariski logification.
Source: ILO VI 1.1; VIII 3.3.2
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogPushoutPresentation.ZariskiUniversal {X : Scheme.{u}}
    (P : ZariskiPrelogStructure X) (L : ZariskiLogStructure X)
    (q : PrelogPushoutPresentation (Opens.grothendieckTopology X.carrier)
      P.monoidSheaf.obj X.presheaf P.alpha L.monoidSheaf L.alpha) : Prop :=
  ∀ (K : ZariskiLogStructure X) (f : P.monoidSheaf.obj ⟶ K.monoidSheaf.obj),
    f ≫ K.alpha = P.alpha →
    ∃! g : {g : L.monoidSheaf ⟶ K.monoidSheaf // g.hom ≫ K.alpha = L.alpha},
      q.iota ≫ g.val.hom = f

/-- Universality of the étale logification among log structures, including every
compatible map of the given prelog sheaf.
Source: ILO VI 1.1; VIII 3.3.2
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogPushoutPresentation.EtaleUniversal {X : Scheme.{u}}
    (P : EtalePrelogStructure X) (L : EtaleLogStructure X)
    (q : PrelogPushoutPresentation X.smallEtaleTopology
      P.monoidSheaf.obj X.etaleStructurePresheaf P.alpha L.monoidSheaf L.alpha) : Prop :=
  ∀ (K : EtaleLogStructure X) (f : P.monoidSheaf.obj ⟶ K.monoidSheaf.obj),
    f ≫ K.alpha = P.alpha →
    ∃! g : {g : L.monoidSheaf ⟶ K.monoidSheaf // g.hom ≫ K.alpha = L.alpha},
      q.iota ≫ g.val.hom = f

/-- A normalized stalk presentation of the Zariski logification: the map adjoining
units is bijective after exactly the existing pushout congruence is imposed.
Source: ILO VI 1.1; VIII 3.3.2; node proof Steps 6--7
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogPushoutPresentation.ZariskiStalks {X : Scheme.{u}}
    (P : ZariskiPrelogStructure X) (L : ZariskiLogStructure X)
    (q : PrelogPushoutPresentation (Opens.grothendieckTopology X.carrier)
      P.monoidSheaf.obj X.presheaf P.alpha L.monoidSheaf L.alpha) : Prop :=
  ∀ x : X,
    ∃ e : divisorialChartPushout (P.stalkAlpha x).mrangeRestrict ≅
        L.toZariskiPrelogStructure.stalk x,
      (∀ (U : X.Opens) (hx : x ∈ U) (p : P.monoidSheaf.obj.obj (op U))
        (a : Γ(X, U)ˣ),
        e.hom (prelogPairClass (X.presheaf.stalk x) (P.stalkAlpha x) (P.germ U x hx p)
          (Units.map (X.presheaf.germ U x hx).hom a)) =
        L.toZariskiPrelogStructure.germ U x hx
          (q.pairMap (op U) (prelogPairClass Γ(X, U) (P.alpha.app (op U)).hom p a))) ∧
      ∀ (a : (X.presheaf.stalk x)ˣ),
        e.hom (prelogPairClass (X.presheaf.stalk x) (P.stalkAlpha x) 1 a) = L.unitsIn x a

/-- The inverse-image stalk identification and the local-unit extension formula,
including the same inverse-unit submonoid on both sides. The pushout over that
submonoid is the explicit quotient for `ρ ∘ β_x`, since `ρ` reflects units.
Source: ILO VIII §3 and 3.3.2; node proof Steps 5--7
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogPushoutPresentation.EtaleStalks {X : Scheme.{u}}
    (P : ZariskiPrelogStructure X) (E : PrelogEtaleInverseImage P)
    (L : EtaleLogStructure X)
    (q : PrelogPushoutPresentation X.smallEtaleTopology E.prelog.monoidSheaf.obj
      X.etaleStructurePresheaf E.prelog.alpha L.monoidSheaf L.alpha) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    ∃ (ρ : X.presheaf.stalk (t default) →+* strictLocalRing X t)
      (eP : E.prelog.stalk t ≅ P.stalk (t default))
      (eL : divisorialChartPushout
        (ρ.toMonoidHom.comp (P.stalkAlpha (t default))).mrangeRestrict ≅
          L.toEtalePrelogStructure.stalk t),
      IsPrelogLocalRingMap t ρ ∧
      (∀ a : X.presheaf.stalk (t default), IsUnit (ρ a) ↔ IsUnit a) ∧
      (∀ m : E.prelog.stalk t,
        E.prelog.stalkAlpha t m = ρ (P.stalkAlpha (t default) (eP.hom m))) ∧
      (∀ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (hx : t default ∈ (prelogEtaleImage X).obj W)
        (p : P.monoidSheaf.obj.obj (op ((prelogEtaleImage X).obj W))),
        eP.hom (E.prelog.germ t W w (E.unit.app (op W) p)) =
          P.germ ((prelogEtaleImage X).obj W) (t default) hx p) ∧
      (∀ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (p : E.prelog.monoidSheaf.obj.obj (op W)) (a : Γ(W.left, ⊤)ˣ),
        eL.hom (prelogPairClass (strictLocalRing X t)
          (ρ.toMonoidHom.comp (P.stalkAlpha (t default)))
          (eP.hom (E.prelog.germ t W w p))
          (Units.map (strictLocalGerm X t W w).hom a)) =
        L.toEtalePrelogStructure.germ t W w
          (q.pairMap (op W) (prelogPairClass Γ(W.left, ⊤) (E.prelog.alpha.app (op W)).hom p a))) ∧
      ∀ a : (strictLocalRing X t)ˣ,
        eL.hom (prelogPairClass (strictLocalRing X t)
          (ρ.toMonoidHom.comp (P.stalkAlpha (t default))) 1 a) =
          L.unitsIn t a

/-- Characteristic stalks of a Zariski logification, with the quotient normalization.
Source: ILO VI 1.1; VIII 3.3.2; node proof Step 8
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogCharacteristicPresentation.ZariskiStalks {X : Scheme.{u}}
    (P : ZariskiPrelogStructure X) (L : ZariskiLogStructure X)
    (K : TopCat.Sheaf CommMonCat.{u} X.carrier)
    (q : PrelogPushoutPresentation (Opens.grothendieckTopology X.carrier)
      P.monoidSheaf.obj X.presheaf P.alpha L.monoidSheaf L.alpha)
    (c : PrelogCharacteristicPresentation (Opens.grothendieckTopology X.carrier)
      L.monoidSheaf K) : Prop :=
  ∀ x : X, ∃ e : CommMonCat.of
      (Associates (divisorialChartPushout (P.stalkAlpha x).mrangeRestrict)) ≅
      CommMonCat.FilteredColimits.colimit ((OpenNhds.inclusion x).op ⋙ K.obj),
    ∀ (U : X.Opens) (hx : x ∈ U) (p : P.monoidSheaf.obj.obj (op U))
      (a : Γ(X, U)ˣ),
      e.hom (Associates.mk (prelogPairClass (X.presheaf.stalk x) (P.stalkAlpha x) (P.germ U x hx p)
        (Units.map (X.presheaf.germ U x hx).hom a))) =
      (CommMonCat.FilteredColimits.colimitCocone
        ((OpenNhds.inclusion x).op ⋙ K.obj)).ι.app (op ⟨U, hx⟩)
          (c.quotientMap.hom.app (op U)
            (q.pairMap (op U) (prelogPairClass Γ(X, U) (P.alpha.app (op U)).hom p a)))

/-- Characteristic stalks on the étale site. The local map and inverse-image stalk
isomorphism are normalized as in `EtaleStalks`; the quotient map is evaluated on the
same sectionwise pairs. Thus these are the displayed pushouts modulo displayed units.
Source: ILO VI 1.1; VIII 3.3.2; node proof Step 8
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogCharacteristicPresentation.EtaleStalks {X : Scheme.{u}}
    (P : ZariskiPrelogStructure X) (E : PrelogEtaleInverseImage P)
    (L : EtaleLogStructure X) (K : Sheaf X.smallEtaleTopology CommMonCat.{u})
    (q : PrelogPushoutPresentation X.smallEtaleTopology E.prelog.monoidSheaf.obj
      X.etaleStructurePresheaf E.prelog.alpha L.monoidSheaf L.alpha)
    (c : PrelogCharacteristicPresentation X.smallEtaleTopology L.monoidSheaf K) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (ρ : X.presheaf.stalk (t default) →+* strictLocalRing X t)
    (eP : E.prelog.stalk t ≅ P.stalk (t default)),
    IsPrelogLocalRingMap t ρ →
    (∀ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
      (hx : t default ∈ (prelogEtaleImage X).obj W)
      (p : P.monoidSheaf.obj.obj (op ((prelogEtaleImage X).obj W))),
      eP.hom (E.prelog.germ t W w (E.unit.app (op W) p)) =
        P.germ ((prelogEtaleImage X).obj W) (t default) hx p) →
    ∃ e : CommMonCat.of (Associates (divisorialChartPushout
        (ρ.toMonoidHom.comp (P.stalkAlpha (t default))).mrangeRestrict)) ≅
        pointedEtaleStalk K t,
      ∀ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (p : E.prelog.monoidSheaf.obj.obj (op W)) (a : Γ(W.left, ⊤)ˣ),
        e.hom (Associates.mk
          (prelogPairClass (strictLocalRing X t)
            (ρ.toMonoidHom.comp (P.stalkAlpha (t default)))
            (eP.hom (E.prelog.germ t W w p))
            (Units.map (strictLocalGerm X t W w).hom a))) =
          pointedEtaleGerm K t W w (c.quotientMap.hom.app (op W)
            (q.pairMap (op W)
              (prelogPairClass Γ(W.left, ⊤) (E.prelog.alpha.app (op W)).hom p a)))

/-- Restriction of the entire pushout presentation to a slice site. This includes
restriction to open subschemes, on either the Zariski or the étale site. The pair maps
and the prelog inclusion are exactly the restrictions of the original maps.
Source: ILO VIII §3; node proof Step 9, slice-sheafification comparison
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogPushoutPresentation.Restricts {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ CommMonCat.{u}}
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} {β : P ⟶ R ⋙ forget₂ CommRingCat CommMonCat}
    {L : Sheaf J CommMonCat.{u}} {α : L.obj ⟶ R ⋙ forget₂ CommRingCat CommMonCat}
    (q : PrelogPushoutPresentation J P R β L α) : Prop :=
  ∀ W : C,
    ∃ r : PrelogPushoutPresentation (J.over W) ((Over.forget W).op ⋙ P)
      ((Over.forget W).op ⋙ R) (Functor.whiskerLeft (Over.forget W).op β)
      (L.over W) (Functor.whiskerLeft (Over.forget W).op α),
      (∀ (U : (Over W)ᵒᵖ)
        (z : divisorialChartPushout (A := R.obj (op U.unop.left))
          (β.app (op U.unop.left)).hom.mrangeRestrict),
        r.pairMap U z = q.pairMap (op U.unop.left) z) ∧
      r.iota = Functor.whiskerLeft (Over.forget W).op q.iota

/-- Restriction of the characteristic quotient and its canonical quotient map to
slice sites, in particular to open subschemes.
Source: ILO VIII §3; node proof Steps 8--9
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogCharacteristicPresentation.Restricts {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} {L K : Sheaf J CommMonCat.{u}}
    (c : PrelogCharacteristicPresentation J L K) : Prop :=
  ∀ W : C, ∃ r : PrelogCharacteristicPresentation (J.over W) (L.over W) (K.over W),
    r.quotientMap.hom = Functor.whiskerLeft (Over.forget W).op c.quotientMap.hom

/-- The canonical comparison after inverse image and re-logification. The middle
map is the inverse image of the Zariski prelog inclusion, determined on raw sections.
The final isomorphism fixes both the prelog map and the structural map, hence units.
Source: ILO VIII 3.3.2; node proof Step 4
(blueprint: lem-trf-zariski-prelog-logification-comparison). -/
def PrelogLogificationComparison {X : Scheme.{u}} (P : ZariskiPrelogStructure X)
    (Z : ZariskiLogStructure X)
    (z : PrelogPushoutPresentation (Opens.grothendieckTopology X.carrier)
      P.monoidSheaf.obj X.presheaf P.alpha Z.monoidSheaf Z.alpha)
    (E : PrelogEtaleInverseImage P)
    (F : PrelogEtaleInverseImage Z.toZariskiPrelogStructure)
    (L N : EtaleLogStructure X)
    (l : PrelogPushoutPresentation X.smallEtaleTopology E.prelog.monoidSheaf.obj
      X.etaleStructurePresheaf E.prelog.alpha L.monoidSheaf L.alpha)
    (n : PrelogPushoutPresentation X.smallEtaleTopology F.prelog.monoidSheaf.obj
      X.etaleStructurePresheaf F.prelog.alpha N.monoidSheaf N.alpha) : Prop :=
  ∃ (a : E.prelog.monoidSheaf ⟶ F.prelog.monoidSheaf) (c : N.monoidSheaf ≅ L.monoidSheaf),
    E.unit ≫ a.hom = Functor.whiskerLeft (prelogEtaleImage X).op z.iota ≫ F.unit ∧
    a.hom ≫ F.prelog.alpha = E.prelog.alpha ∧
    c.hom.hom ≫ L.alpha = N.alpha ∧
    a.hom ≫ n.iota ≫ c.hom.hom = l.iota
```

## New

The original item exposes the relocated declarations through:

```lean
public import Sheaf.AlgebraicGeometry.PrelogLogificationData
```

`PrelogLogificationData.lean` contains exactly the declaration block above, with only the
blueprint tags in docstrings changed to `def-trf-prelog-logification-data`. It publicly imports
`Sheaf.AlgebraicGeometry.ZariskiLogStructure` and `Mathlib.CategoryTheory.Sites.Over`.
Thus the declarations are the same constants with the same signatures and bodies; their
module of definition changes. No replacement notion, alias, axiom, or choice of unspecified
data is introduced.

The old unused public imports of `Sheaf.CategoryTheory.Sites.GeometricMorphism` and
`Mathlib.CategoryTheory.Sites.PreservesSheafification` are removed. The other old private
imports were proof-plan inputs; the split DAG records the ones needed by the remaining
geometry. They are not necessary to elaborate the presentation definitions.

## Users

The first delivery found three consumers; the current-main search for this repair supersedes
that list, as recorded below.
The returned packet missed a new source back edge through `PrelogPushoutLogAxiom`.
`PrelogUnitPushoutPresentation` is now adapted only at its data import; the other consumers
stay unchanged. See `prelog-unit-pushout-data-import.md` for the exact one-line repair.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PrelogUnitPushoutPresentation | none recorded locally | Public import redirected to PrelogLogificationData to break the returned cycle; all declarations unchanged. |
| Sheaf.AlgebraicGeometry.MonoidChartCharacteristicFan | none recorded locally | Historical consumer checked unchanged in the first delivery; current main no longer imports the item. No adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLogPresentationComparison | none recorded locally | Consumer through PrelogUnitPushoutPresentation; compiled unchanged against the repaired import (7.5 s). |
| Sheaf.AlgebraicGeometry.PrelogPushoutLogAxiom | none recorded locally | Current proof imports the presentation; compiled unchanged against the repaired import (9.5 s). |
| Sheaf.AlgebraicGeometry.PrelogLogificationEtaleConstruction | G9 (new in packet) | Uses the current proved pushout result, compiled against the repaired dependency chain. |

The current source import graph has only PrelogUnitPushoutPresentation as a direct importer
of the original item. Its repaired data import removes that edge. The current full source
closure of the item is acyclic; both direct users of the adapted presentation are compiled
against it, as recorded in the import repair change record.

## Status

landed 20261026T104432-L-819761 2026-10-26 (merge of deliver/G9/Sheaf.AlgebraicGeometry.ZariskiPrelogLogificationComparison)
