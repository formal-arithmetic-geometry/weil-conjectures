# AlgebraicGeometry.descent_pullback_canonical_iso

## Reason

The preflight conservatively classifies new section/variable commands and a
scoped linter option as an interface change. They organize proved private
helpers and suppress one warning in the unchanged existing signature, respectively.
No public signature, declaration visibility, definition or global instance changes.
The `Comparison` section is closed before the public theorem. The linter setting
uses `in` and applies only to that theorem; it changes no elaboration or kernel rule.
No downstream adaptation is necessary. No target meaning is changed.

## Old

The public signature is:

```lean
theorem descent_pullback_canonical_iso (S : Scheme.{v}) :
    ∃ (pull : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b), Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
      (q : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
          ((pull a b r hr).obj D).V.left ⟶ D.V.left)
      (hq : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
          q a b r hr D ≫ D.V.hom = ((pull a b r hr).obj D).V.hom ≫ r),
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
        IsPullback (q a b r hr D) ((pull a b r hr).obj D).V.hom D.V.hom r ∧
          Over.DescentDatum.IsBaseChange (hr) (hq a b r hr D) D.datum
            ((pull a b r hr).obj D).datum) ∧
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r : T ⟶ X) (hr : r ≫ a = b)
          (D E : Over.DescentDataCategory a) (m : D ⟶ E),
        ((pull a b r hr).map m).hom.left ≫ q a b r hr E =
          q a b r hr D ≫ m.hom.left) ∧
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r₀ r₁ : T ⟶ X) (h₀ : r₀ ≫ a = b) (h₁ : r₁ ≫ a = b),
        ∃ e : pull a b r₀ h₀ ≅ pull a b r₁ h₁,
          ∀ D : Over.DescentDataCategory a,
            (e.hom.app D).hom.left ≫ q a b r₁ h₁ D =
              (D.datum.transport
                (((pull a b r₀ h₀).obj D).V.hom ≫ r₀)
                (((pull a b r₀ h₀).obj D).V.hom ≫ r₁)
                (by rw [Category.assoc, Category.assoc, h₀, h₁])
                (Over.homMk (q a b r₀ h₀ D) (hq a b r₀ h₀ D))).left) ∧
      (∀ ⦃X T U : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S) (c : U ⟶ S)
          (r : T ⟶ X) (t : U ⟶ T) (hr : r ≫ a = b) (ht : t ≫ b = c)
          (hrt : (t ≫ r) ≫ a = c),
        ∃ e : pull a c (t ≫ r) hrt ≅ pull a b r hr ⋙ pull b c t ht,
          ∀ D : Over.DescentDataCategory a,
            (e.hom.app D).hom.left ≫ q b c t ht ((pull a b r hr).obj D) ≫
              q a b r hr D = q a c (t ≫ r) hrt D)
```

Its proof was `by sorry`. There was no `Comparison` section or scoped linter option.

## New

The public signature remains verbatim:

```lean
theorem descent_pullback_canonical_iso (S : Scheme.{v}) :
    ∃ (pull : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b), Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
      (q : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
          ((pull a b r hr).obj D).V.left ⟶ D.V.left)
      (hq : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
          q a b r hr D ≫ D.V.hom = ((pull a b r hr).obj D).V.hom ≫ r),
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
        IsPullback (q a b r hr D) ((pull a b r hr).obj D).V.hom D.V.hom r ∧
          Over.DescentDatum.IsBaseChange (hr) (hq a b r hr D) D.datum
            ((pull a b r hr).obj D).datum) ∧
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r : T ⟶ X) (hr : r ≫ a = b)
          (D E : Over.DescentDataCategory a) (m : D ⟶ E),
        ((pull a b r hr).map m).hom.left ≫ q a b r hr E =
          q a b r hr D ≫ m.hom.left) ∧
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r₀ r₁ : T ⟶ X) (h₀ : r₀ ≫ a = b) (h₁ : r₁ ≫ a = b),
        ∃ e : pull a b r₀ h₀ ≅ pull a b r₁ h₁,
          ∀ D : Over.DescentDataCategory a,
            (e.hom.app D).hom.left ≫ q a b r₁ h₁ D =
              (D.datum.transport
                (((pull a b r₀ h₀).obj D).V.hom ≫ r₀)
                (((pull a b r₀ h₀).obj D).V.hom ≫ r₁)
                (by rw [Category.assoc, Category.assoc, h₀, h₁])
                (Over.homMk (q a b r₀ h₀ D) (hq a b r₀ h₀ D))).left) ∧
      (∀ ⦃X T U : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S) (c : U ⟶ S)
          (r : T ⟶ X) (t : U ⟶ T) (hr : r ≫ a = b) (ht : t ≫ b = c)
          (hrt : (t ≫ r) ≫ a = c),
        ∃ e : pull a c (t ≫ r) hrt ≅ pull a b r hr ⋙ pull b c t ht,
          ∀ D : Over.DescentDataCategory a,
            (e.hom.app D).hom.left ≫ q b c t ht ((pull a b r hr).obj D) ≫
              q a b r hr D = q a c (t ≫ r) hrt D)
```

Its proof is complete. Added only private declarations, a closed section with
its local variables, and `set_option linter.unusedVariables false in` immediately
before this theorem. Its existing public import is unchanged; its new construction
import is proof-only. Removed only a redundant proof-only import of DescentDatum.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DescentPullbackCanonicalIso --uses
AlgebraicGeometry.descent_pullback_canonical_iso` found 224 transitive importers
and the following two source users. All importers keep the same public interface;
there are no adapted modules. The existing user's application still obtains the
same functors, projections, base-change properties and comparisons.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DescentPullbackCanonicalIso | G2 | private proof helpers only; unchanged public theorem |
| Sheaf.AlgebraicGeometry.FpqcRefinementFullyFaithful | unclaimed in this clone | unchanged theorem application and signature; no adaptation |

## Status

landed 20261012T144112-L-2095736 2026-10-12 (merge of deliver/G2/Sheaf.AlgebraicGeometry.DescentPullbackCanonicalIso)
