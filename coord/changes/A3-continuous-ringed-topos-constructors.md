# CategoryTheory.continuousRingedTopos and CategoryTheory.restrictionRingedTopos (private)

## Reason

Reuse the existing generic constructors in the pro-etale coefficient-change proof without
importing unrelated etale derived-comparison theory. An unchanged copy of the item compiled
in 30.6 seconds; adding the old etale presentation import took 57.0 seconds before the new
argument. The continuous constructor now compiles in 6.5 seconds and restriction in 2.2 seconds.
A normal import of the small public interface also avoids the cost of importing all private
implementation declarations (the unchanged baseline then compiles in 40.0 seconds). This is a definition/API
repair: the canonical constructions move to two light generic modules, and the old private
names become abbreviations. No public signature or visibility changes. The constructions
and their mathematical meaning are unchanged; no target statement is affected.

The item also gives its constructed mate a private irreducible definition and reuses the
proved normalization in both of its proofs. This shares data inside the same file; it
changes no public definition or signature and has no external users.

## Old

```lean
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : D ⥤ C) [F.IsContinuous K J]
  (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : L ⊣ F.sheafPushforwardContinuous (Type u) K J)

private def directPair {X Y : Sheaf J (Type u)} {T : Sheaf K (Type u)}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj Y) :
    T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj (X ⊗ Y) :=
  ⟨{ app U := ↾(fun t ↦ (x.hom.app U t, y.hom.app U t))
     naturality := by
       intro U V f
       ext t
       change (x.hom.app V (T.obj.map f t), y.hom.app V (T.obj.map f t)) =
         (X.obj.map (F.op.map f) (x.hom.app U t),
           Y.obj.map (F.op.map f) (y.hom.app U t))
       exact Prod.ext (CategoryTheory.congr_fun (x.hom.naturality f) t)
         (CategoryTheory.congr_fun (y.hom.naturality f) t) }⟩

private theorem transpose_pair {X Y : Sheaf J (Type u)} {T : Sheaf K (Type u)}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj Y) :
    (adj.homEquiv T (X ⊗ Y)).symm (directPair F x y) =
      CartesianMonoidalCategory.lift ((adj.homEquiv T X).symm x)
        ((adj.homEquiv T Y).symm y) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst, ← adj.homEquiv_naturality_right_symm]
    rfl
  · rw [CartesianMonoidalCategory.lift_snd, ← adj.homEquiv_naturality_right_symm]
    rfl

private theorem transpose_binary
    {X Y Z : Sheaf J (Type u)} {T : Sheaf K (Type u)} (op : X ⊗ Y ⟶ Z)
    (x : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj Y)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj Z)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U)
      (x.hom.app U t, y.hom.app U t)) :
    ∀ U t, ((adj.homEquiv T Z).symm z).hom.app U t =
      op.hom.app U (((adj.homEquiv T X).symm x).hom.app U t,
        ((adj.homEquiv T Y).symm y).hom.app U t) := by
  have he : z = directPair F x y ≫
      (F.sheafPushforwardContinuous (Type u) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm, transpose_pair F L adj]
  intro U t
  rfl

private theorem transpose_constant
    {X : Sheaf J (Type u)} {T : Sheaf K (Type u)}
    (op : 𝟙_ (Sheaf J (Type u)) ⟶ X)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj X)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U) PUnit.unit) :
    ∀ U t, ((adj.homEquiv T X).symm z).hom.app U t = op.hom.app U PUnit.unit := by
  let w : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj (𝟙_ _) :=
    ⟨{ app U := ↾(fun _ ↦ PUnit.unit) }⟩
  have he : z = w ≫ (F.sheafPushforwardContinuous (Type u) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm]
  intro U t
  change op.hom.app U _ = _
  congr 1

open SheafOfModules.GeometricConstruction in
private noncomputable def continuousRingedTopos
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} K J).obj R) :
    RingedToposMorphism (base R) (base S) := by
  let φR : base S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K J).obj (base R) :=
    (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map φ
  let φs : rset S ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj (rset R) :=
    (sheafCompose K (forget CommRingCat.{u})).map φ
  let g := (adj.homEquiv (rset S) (rset R)).symm φs
  let P := SheafOfModules.pushforward.{u} (F := F) φR
  refine {
    inverse := L
    direct := F.sheafPushforwardContinuous (Type u) K J
    adj := adj
    leftExact := inferInstance
    ringMap := g
    ring_zero := ?_
    ring_one := ?_
    ring_add := ?_
    ring_mul := ?_
    modules := P
    additive := ?_
    underlying := Iso.refl _
    module_linear := ?_
  }
  · intro T z hz U t
    change T ⟶ rset S at z
    change ((L.map z) ≫ g).hom.app U t = (0 : R.obj.obj U)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm]
    let zeroR : 𝟙_ (Sheaf J (Type u)) ⟶ rset R :=
      ⟨{ app U := ↾(fun _ ↦ (0 : R.obj.obj U))
         naturality := by intro U V f; ext t; exact (R.obj.map f).hom.map_zero.symm }⟩
    apply transpose_constant F L adj zeroR (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 0
    have h : (show S.obj.obj V from z.hom.app V x) = 0 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_zero
  · intro T z hz U t
    change T ⟶ rset S at z
    change ((L.map z) ≫ g).hom.app U t = (1 : R.obj.obj U)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm]
    apply transpose_constant F L adj (ringOne R) (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 1
    have h : (show S.obj.obj V from z.hom.app V x) = 1 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_one
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Add.add (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (ringAdd R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') + (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') + (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_add _ _)
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Mul.mul (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (ringMul R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') * (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') * (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_mul _ _)
  · exact ⟨by intro M N a b; ext U x; rfl⟩
  · intro M T a x y z hz U t
    change T ⟶ rset S at a
    change T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj ((mset R).obj M)
      at x y z
    let ax : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj ((mset R).obj M) :=
      CartesianMonoidalCategory.lift a x ≫ action S (P.obj M)
    have hAdd := transpose_binary F L adj (addition R M) ax y z
      (fun V x' ↦ hz V x') U t
    have hSmul := transpose_binary F L adj (action R M) (a ≫ φs) x ax
      (fun V x' ↦ rfl) U t
    change ((adj.homEquiv T _).symm z).hom.app U t = _
    rw [hAdd, hSmul]
    rw [adj.homEquiv_naturality_left_symm]
    rfl

end

private noncomputable def restrictionRingedTopos
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (c : S ⟶ R) : RingedToposMorphism R S where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := (sheafCompose J (forget RingCat.{u})).map c
  ring_zero := by
    intro T z hz U t
    change (c.hom.app U).hom (z.hom.app U t) = 0
    rw [hz U t]
    exact (c.hom.app U).hom.map_zero
  ring_one := by
    intro T z hz U t
    change (c.hom.app U).hom (z.hom.app U t) = 1
    rw [hz U t]
    exact (c.hom.app U).hom.map_one
  ring_add := by
    intro T x y z hz U t
    change (c.hom.app U).hom (z.hom.app U t) =
      (c.hom.app U).hom (x.hom.app U t) + (c.hom.app U).hom (y.hom.app U t)
    rw [hz U t]
    exact (c.hom.app U).hom.map_add _ _
  ring_mul := by
    intro T x y z hz U t
    change (c.hom.app U).hom (z.hom.app U t) =
      (c.hom.app U).hom (x.hom.app U t) * (c.hom.app U).hom (y.hom.app U t)
    rw [hz U t]
    exact (c.hom.app U).hom.map_mul _ _
  modules := SheafOfModules.restrictScalars c
  additive := inferInstance
  underlying := Iso.refl _
  module_linear := by
    intro M T a x y z hz U t
    exact hz U t
end CategoryTheory
```

## New

```lean
namespace CategoryTheory

private noncomputable abbrev continuousRingedTopos := @siteContinuousRingedTopos
private noncomputable abbrev restrictionRingedTopos := @siteRestrictionRingedTopos

end CategoryTheory
```

The full constructor bodies and their proved operation lemmas occur unchanged in
`Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage` and
`Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage`, with constructor names
`siteContinuousRingedTopos` and `siteRestrictionRingedTopos`. Each module adds a proved
public existence theorem exposing its module-functor equality. The old module replaces
its proof-only GeometricModuleConstruction import with proof-only imports of both new
modules. The old public presentation theorem and its proof are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation | unclaimed | Private constructors become aliases; proof-only import changes. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction | A3 | New proof uses the extracted constructors on small pro-etale sites. |

`tools/downstream.py --uses continuousRingedTopos` and the corresponding restriction
query found only the etale presentation itself. Its sole direct module consumer is
`Sheaf.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic`; it uses only the
unchanged public presentation theorem. The added restriction module needs no GeometricModuleConstruction import.
No other consumer requires adaptation. The unchanged direct consumer was compiled
against the adapted module and passed in 12.4 seconds.

## Status

landed 20261018T133832-L-2674607 2026-10-18 (merge of deliver/A3/Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction)
