# AlgebraicGeometry.Scheme.Modules.meromorphicModule_generic_product

## Reason

Preflight requires a change record for added `open`, `attribute` and option commands,
even when they only affect proof elaboration in this file. The added tensor notation
scope, local monoidal-category instance and declaration-local transparency options
support the private tensor and fraction-map constructions. No existing public
signature, definition, instance, attribute or public import changes. No target meaning
changes and no consumer adaptation is necessary.

## Old

The original theorem signature, verbatim:

```lean
theorem meromorphicModule_generic_product (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hweak : ∀ x : X, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      Ideal.WeakAss (X.presheaf.stalk x) → x ∈ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite) :
    (∃ e : meromorphicModule X (unit X) ≅
        ∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
          (pushforward (X.fromSpecStalk η.val)).obj (unit (Spec (X.presheaf.stalk η.val)))),
      ∀ η : {x : X // x ∈ genericPoints X},
        toMeromorphicModule X (unit X) ≫ e.hom ≫ Pi.π _ η =
          SheafOfModules.unitToPushforwardObjUnit (X.fromSpecStalk η.val).toRingCatSheafHom) ∧
    Nonempty ((meromorphicModule X (unit X) ⊗ F) ≅ meromorphicModule X F) ∧
    (∃ e : meromorphicModule X F ≅
        ∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
          (pushforward (X.fromSpecStalk η.val)).obj
            (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val)))),
      ∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U) (m : Γ(F, U)),
        (toMeromorphicModule X F ≫ e.hom ≫ Pi.π _ η).val.app (op U) m =
          tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
            (X.fromSpecStalk η.val ⁻¹ᵁ U) (F.presheaf.germ U η.val hη m))
```

The original context contains this opening:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
```

The proof body is `by sorry`.

## New

The return on `9d06ff05c60` is repaired by removing the duplicate private
`meromorphicRestriction_mk` and applying the public
`exists_meromorphicRestriction` theorem's `choose_spec` directly at its two use sites.
The original matching formula in `MeromorphicModule` is private; its visibility
and all other declarations in that module are unchanged.

The theorem signature above remains verbatim. Its proof is complete from the new
affine section lemma; all added helpers in this module are private and proved.
The added proof-context commands are:

```lean
open scoped TensorProduct
attribute [local instance] presheafMonoidalCategory
```

Eight private declarations use this declaration-local elaboration option:

```lean
set_option backward.isDefEq.respectTransparency false in
```

The scope opening controls parsing only in this file. The instance attribute is
explicitly local. Each transparency option applies only to the following private
declaration. No new public notation or global instance is exported. All added
imports in the item are private proof imports. The new public theorem and its one
remaining sorry are in `Sheaf.AlgebraicGeometry.MeromorphicGenericAffine`, with the
new node `lem-sc-meromorphic-affine-generic-sections`; this is the affine calculation,
not a change to the original theorem.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.MeromorphicGenericProduct
--uses meromorphicModule_generic_product` lists the two downstream modules below.
Only the first explicitly uses the theorem. Current claim records show both are
unclaimed. No consumer is edited: the existing public API remains identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MeromorphicGenericProduct | B5 | Proof and private helpers added. |
| Sheaf.AlgebraicGeometry.MeromorphicSheafGenericProduct | unclaimed | Same theorem signature; no adaptation. |
| Sheaf.AlgebraicGeometry.RegularMeromorphicSectionExists | unclaimed | Same public API; no adaptation. |

## Status

landed 20261023T230428-L-3425328 2026-10-23 (merge of deliver/B5/Sheaf.AlgebraicGeometry.MeromorphicGenericProduct)
