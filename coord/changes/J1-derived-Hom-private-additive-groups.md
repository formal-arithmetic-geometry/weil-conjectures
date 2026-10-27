# WeilConjectures.bilinearAdd, bilinearPost and bilinearPre

## Reason

These private additive helpers are used only on morphism groups of preadditive
categories. Specializing their additive structures to groups avoids normalizing
two independently synthesized monoid instances through the concrete derived
category model. Their formulas stay unchanged. No public signature, definition
body, attribute or import changes. Local irreducibility attributes also keep the
chosen derived localization model and the Hom construction abstract during
elaboration; all exported instances retain their original priorities.
The tensor comparison applies a proved generic semilinear composition lemma,
generalizing `RationalRestrictionComparisonCoherence.tensorIso_localize` from
one coefficient ring to two. This keeps the composition calculation abstract
rather than expanding derived Hom structures at every arrow. The stage-object
proof uses an explicit object equation rather than a large dependent rewrite.
All of these helpers remain in the same file and are checked in its one compile.

## Old

```lean
private def bilinearAdd {R : Type*} [CommSemiring R]
    {M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] (b : M →ₗ[R] N →ₗ[R] P) :
    M →+ N →+ P :=
  LinearMap.toAddMonoidHom'.comp b.toAddMonoidHom

private def bilinearPost {M N P Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    (b : M →+ N →+ P) (f : P →+ Q) : M →+ N →+ Q where
  toFun x := f.comp (b x)
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

private def bilinearPre {M N P M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [AddCommMonoid M'] [AddCommMonoid N']
    (b : M →+ N →+ P) (f : M' →+ M) (g : N' →+ N) : M' →+ N' →+ P where
  toFun x := (b (f x)).comp g
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp
```

## New

```lean
private def bilinearAdd {R : Type*} [CommSemiring R]
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (b : M →ₗ[R] N →ₗ[R] P) :
    M →+ N →+ P :=
  LinearMap.toAddMonoidHom'.comp b.toAddMonoidHom

private def bilinearPost {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (b : M →+ N →+ P) (f : P →+ Q) : M →+ N →+ Q where
  toFun x := f.comp (b x)
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

private def bilinearPre {M N P M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N']
    (b : M →+ N →+ P) (f : M' →+ M) (g : N' →+ N) : M' →+ N' →+ P where
  toFun x := (b (f x)).comp g
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp
```

## Users

Read-only `tools/downstream.py Sheaf.Paper.DerivedPullbackTensorHom --uses
bilinearAdd bilinearPost bilinearPre` finds the two modules below. The second uses
`import all` to access these private helpers. Every call in both modules supplies
morphism groups of a preadditive category, so no caller changes are needed. The
unchanged second module compiled against the revised item with `lcompile.py` in
42.0 s, with no warnings or errors. Its temporary validation copy is not included
in the packet. The item itself compiled cleanly in 57.4 s.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedPullbackTensorHom | J1 | Private helper specialization and new rational Hom proof. |
| Sheaf.Paper.RationalRestrictionComparisonCoherence | unclaimed | Existing Hom-group calls retain their types; no adaptation. |

## Status

landed 20261026T065953-L-3317984 2026-10-26 (merge of deliver/J1/Sheaf.Paper.DerivedPullbackTensorHom)
