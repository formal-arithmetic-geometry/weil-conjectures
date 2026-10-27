# scalarExchangeLeft and scalarExchangeRight

## Reason

Preserve the actual three-factor route definitions while naming their generic
categorical words before specializing to internal derived categories. The kernel
otherwise repeatedly reduces the large derived-category and functor endpoint
instances when checking the specialization of the proved categorical mate lemma.
The word constructors are real composites, definitionally the original formulas.
All original signatures, hypotheses, attributes and visibility are unchanged.
No target meaning changes, no data is selected from an existence theorem, and
kernel checking remains enabled. No timeout limit is increased.

## Old

```lean
def scalarExchangeLeft (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (J : DerivedCategory (Modules Λ X)) :
    (L Λ' c).obj ((D φ Y).obj ((F Λ f).obj J)) ⟶
      (F Λ' f').obj ((D φ X').obj ((L Λ a).obj J)) :=
  (L Λ' c).map ((rho φ f (b f)).app J) ≫
    (scalarAmbientExchange Λ' sq).app ((D φ X).obj J) ≫
    (F Λ' f').map ((b a).hom.app J)
```

```lean
def scalarExchangeRight (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (J : DerivedCategory (Modules Λ X)) :
    (L Λ' c).obj ((D φ Y).obj ((F Λ f).obj J)) ⟶
      (F Λ' f').obj ((D φ X').obj ((L Λ a).obj J)) :=
  (b c).hom.app ((F Λ f).obj J) ≫
    (D φ C).map ((scalarAmbientExchange Λ sq).app J) ≫
    (rho φ f' (b f')).app ((L Λ a).obj J)
```

## New

```lean
def scalarExchangeLeft (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (J : DerivedCategory (Modules Λ X)) :
    (L Λ' c).obj ((D φ Y).obj ((F Λ f).obj J)) ⟶
      (F Λ' f').obj ((D φ X').obj ((L Λ a).obj J)) :=
  mateRouteLeft (L Λ' c) (rho φ f (b f)) (scalarAmbientExchange Λ' sq)
    (b a).hom J
```

```lean
def scalarExchangeRight (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (J : DerivedCategory (Modules Λ X)) :
    (L Λ' c).obj ((D φ Y).obj ((F Λ f).obj J)) ⟶
      (F Λ' f').obj ((D φ X').obj ((L Λ a).obj J)) :=
  mateRouteRight (D φ C) (b c).hom (scalarAmbientExchange Λ sq)
    (rho φ f' (b f')) J
```

The two word constructors are:

```lean
namespace CategoryTheory

/-- The left route in a square of mates, with endpoint types kept abstract.
Source: Stacks 0E47 (blueprint: lem-sfb-scalar-geometric-exchange-rectangle). -/
def mateRouteLeft
    {A₀ A₁ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {rf : A₁ ⥤ A₀} {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁}
    {rfb : B₁ ⥤ B₀} {ab : B₁ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    {a : A₁ ⥤ A₃} {T₃ : A₃ ⥤ B₃}
    (cb : B₀ ⥤ B₂) (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb)
    (eb : rfb ⋙ cb ⟶ ab ⋙ rgb) (la : T₁ ⋙ ab ⟶ a ⋙ T₃) (J : A₁) :
    cb.obj (T₀.obj (rf.obj J)) ⟶ rgb.obj (T₃.obj (a.obj J)) :=
  cb.map (r.app J) ≫ eb.app (T₁.obj J) ≫ rgb.map (la.app J)

/-- The right route in a square of mates, with endpoint types kept abstract.
Source: Stacks 0E47 (blueprint: lem-sfb-scalar-geometric-exchange-rectangle). -/
def mateRouteRight
    {A₀ A₁ A₂ A₃ B₀ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₂] [Category* B₃]
    {rf : A₁ ⥤ A₀} {c : A₀ ⥤ A₂} {rg : A₃ ⥤ A₂}
    {a : A₁ ⥤ A₃} {T₀ : A₀ ⥤ B₀} {T₃ : A₃ ⥤ B₃}
    {cb : B₀ ⥤ B₂} {rgb : B₃ ⥤ B₂}
    (T₂ : A₂ ⥤ B₂) (lc : T₀ ⋙ cb ⟶ c ⋙ T₂)
    (e : rf ⋙ c ⟶ a ⋙ rg) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb) (J : A₁) :
    cb.obj (T₀.obj (rf.obj J)) ⟶ rgb.obj (T₃.obj (a.obj J)) :=
  lc.app (rf.obj J) ≫ T₂.map (e.app J) ≫ t.app (a.obj J)

end CategoryTheory
```

## Users

The read-only `tools/downstream.py` search on 2026-10-23 finds the item itself
as the sole textual user of both route definitions. The only downstream importers
are `Sheaf.Paper.FlatCoefficientSquareNormalization` (R9) and
`Sheaf.Paper.InternalScalarMateProjection` (J3); neither mentions either route.
No downstream adaptation is required. The generic word constructors are owned by
the existing item node, along with its route definitions.

## Status

landed 20261024T015051-L-2318376 2026-10-24 (merge of deliver/J6/Sheaf.Paper.ScalarGeometricExchangeRectangle)
