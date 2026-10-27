# semilinear_compositor_coherence proof scope

## Reason

The preflight interface scanner classifies additional section commands as an
interface change. This delivery adds only proved private helpers, local
irreducibility settings, scoped instance suppression, and proof imports.
No existing declaration signature, definition, public import, or exported
instance changes. `open` and `variable` affect only elaboration in this file.
The local attributes and options are not exported to importers.

## Old

Existing public signature, verbatim:

```lean
theorem semilinear_compositor_coherence
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n) :
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ T),
      (G R φ f).map ((gComp R φ g h).inv.app M ≫
          (eqToIso (congrArg (G R φ) egh)).hom.app M) ≫
        (gComp R φ f l).inv.app M ≫ (eqToIso (congrArg (G R φ) efl)).hom.app M =
      (gComp R φ f g).inv.app ((G R φ h).obj M) ≫
        (eqToIso (congrArg (G R φ) efg)).hom.app ((G R φ h).obj M) ≫
        (gComp R φ k h).inv.app M ≫ (eqToIso (congrArg (G R φ) ekh)).hom.app M) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ X),
      (P R φ h).map ((pComp R φ f g).hom.app M ≫
          (eqToIso (congrArg (P R φ) efg)).hom.app M) ≫
        (pComp R φ k h).hom.app M ≫ (eqToIso (congrArg (P R φ) ekh)).hom.app M =
      (pComp R φ g h).hom.app ((P R φ f).obj M) ≫
        (eqToIso (congrArg (P R φ) egh)).hom.app ((P R φ f).obj M) ≫
        (pComp R φ f l).hom.app M ≫ (eqToIso (congrArg (P R φ) efl)).hom.app M) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion m]
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ X),
      (J R φ h).map ((jComp R φ f g).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Z // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Z) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ g, inferInstance⟩ ⟨k, inferInstance⟩ efg))).hom.app M) ≫
        (jComp R φ k h).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨k ≫ h, inferInstance⟩ ⟨m, inferInstance⟩ ekh))).hom.app M =
      (jComp R φ g h).hom.app ((J R φ f).obj M) ≫
        (eqToIso (congrArg
          (fun a : {a : Y ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (Y ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨g ≫ h, inferInstance⟩ ⟨l, inferInstance⟩ egh))).hom.app
          ((J R φ f).obj M) ≫
        (jComp R φ f l).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ l, inferInstance⟩ ⟨m, inferInstance⟩ efl))).hom.app M) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ Y),
      (gComp R φ (𝟙 X) f).inv.app M ≫
          (eqToIso (congrArg (G R φ) (Category.id_comp f))).hom.app M =
        (gId R φ X).hom.app ((G R φ f).obj M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ Y),
      (gComp R φ f (𝟙 Y)).inv.app M ≫
          (eqToIso (congrArg (G R φ) (Category.comp_id f))).hom.app M =
        (G R φ f).map ((gId R φ Y).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X),
      (pComp R φ (𝟙 X) f).hom.app M ≫
          (eqToIso (congrArg (P R φ) (Category.id_comp f))).hom.app M =
        (P R φ f).map ((pId R φ X).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X),
      (pComp R φ f (𝟙 Y)).hom.app M ≫
          (eqToIso (congrArg (P R φ) (Category.comp_id f))).hom.app M =
        (pId R φ Y).hom.app ((P R φ f).obj M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Derived R φ X),
      (jComp R φ (𝟙 X) f).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
              ⟨𝟙 X ≫ f, inferInstance⟩ ⟨f, inferInstance⟩ (Category.id_comp f)))).hom.app M =
        (J R φ f).map ((jId R φ X).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Derived R φ X),
      (jComp R φ f (𝟙 Y)).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ 𝟙 Y, inferInstance⟩ ⟨f, inferInstance⟩ (Category.comp_id f)))).hom.app M =
        (jId R φ Y).hom.app ((J R φ f).obj M))
```

Original section commands:

```lean
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.VaryingRing
attribute [local irreducible] gComp pComp jComp gId pId jId
```

## New

The public signature above is preserved verbatim. Its `sorry` is replaced by a
complete proof. Additional commands in the file are:

```lean
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] gComp pComp jComp gId pId jId adj moduleAdj moduleJAdj
  jAdj
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local irreducible] modulePComp modulePId moduleGComp moduleJComp
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] moduleGId moduleJId derivedJId
```

Each private helper also scopes removal of `CategoryTheory.catToReflQuiver`
with `attribute [-instance] ... in` to avoid recursive category synthesis.
All such commands are local to their declaration or section. Five redundant
private Mathlib imports are removed; three private Sheaf imports reuse
proved generic fibre-product, exact-derived-functor and mate equations.
Three private WeilConjectures imports provide the categorical comparison APIs.
The repair removes duplicate helpers and reuses the existing private declarations
with `import all`; it exports no helpers.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence | W2 | Complete proof, unchanged public signature |
| Sheaf.Paper.SystemCompatibleCompositorNormalization | unclaimed | Imports the same theorem; no adaptation or signature change |

`tools/downstream.py Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence
--uses semilinear_compositor_coherence` lists the single downstream module
above and finds no external textual uses of the theorem name. No target
statement or definition changes, so target meaning is preserved.

## Status

landed 20261024T191529-L-421432 2026-10-24 (merge of deliver/W2/Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence)
