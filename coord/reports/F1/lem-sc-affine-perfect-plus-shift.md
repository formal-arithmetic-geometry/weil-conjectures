## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePerfectPlusShift` states the affine perfect
extension lemma from Stacks Tag 08EI. It binds an affine scheme `X`, a quasi-compact open
`U` via `hU : IsCompact (U : Set X)`, derived-category instances on `X`, all opens of
`X`, `U`, and all opens of `U`, a perfect object `F` on `U`, and its perfectness proof.
The conclusion gives a perfect `E` on `X` and an isomorphism after restriction and the
canonical open-site equivalence to `F ⊞ F⟦(1 : ℤ)⟧`. The proof is `sorry`, as required.

The statement uses `AlgebraicGeometry.schemeDerivedCategory` from
`Sheaf.AlgebraicGeometry.DerivedCategory` and `AlgebraicGeometry.Scheme.IsPerfect` from
`Sheaf.AlgebraicGeometry.PerfectComplex`. Schemes, opens, `IsAffine`, `IsCompact`,
`HasDerivedCategory`, shifts, biproducts, and the restriction/equivalence are Mathlib
notions. Every hypothesis and conclusion clause is rendered directly by the binders and
conclusion shown in the node's `lean.statement` field.

Edge cases checked: `U = ⊥` and `U = ⊤` are allowed; `F` may be zero; the shift is by
integer `1`; no nonemptiness or separatedness hypothesis was added.

Searches: `msearch.py leanfinder` for affine perfect extension after adjoining a shift
(found only generic derived-category declarations); `msearch.py loogle PerfectComplex`
(no hits); grep of Mathlib and `WeilConjectures` for affine perfect extension (no exact
match); `rg` over `lean/Sheaf` found only the dependency definitions and related lifting
lemmas. No existing exact declaration was found.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. `X` is affine, `U` is a quasi-compact open,
`F` is perfect on `U`, and the conclusion is a perfect `E` on `X` restricting to
`F ⊞ F[1]`; all clauses match. The localized restriction and canonical open equivalence
make the source and target categories explicit. No mismatch was found.

## Second reading by F1

I reread Tag 08EI (Lemma 36.13.8) at `perfect.tex:3398` and matched the node's
statement clause by clause against `AffinePerfectPlusShift.lean`.

* The scheme object is `(X : Scheme.{u})`; `[IsAffine X]` is the affine
  hypothesis.
* The open object is `(U : X.Opens)` and its quasi-compactness is exactly
  `hU : IsCompact (U : Set X)`.
* The `HasDerivedCategory` binders for `X`, every `X.Opens`, `U.toScheme`, and
  every `U.toScheme.Opens` supply the instances required by the recorded
  `schemeDerivedCategory` and `Scheme.IsPerfect` definitions; they add no
  mathematical hypothesis on `X`, `U`, or `F`.
* `(F : schemeDerivedCategory U.toScheme)` and
  `(hF : Scheme.IsPerfect U.toScheme F)` render the perfect object on `U`.
* The conclusion is `∃ E : schemeDerivedCategory X`, followed by
  `Scheme.IsPerfect X E` and a `Nonempty` isomorphism. Its source is derived
  restriction by `SheafOfModules.overFunctor` followed by the canonical
  `Scheme.Modules.overEquiv U`; its target is exactly `F ⊞ F⟦(1 : ℤ)⟧`.
  The quantifier order and orientation therefore agree with the node and source.

The empty open (`U = ⊥`), full open (`U = ⊤`), zero `F`, and arbitrary universe
levels remain admitted by the binders. No nonemptiness, separatedness,
Noetherian, characteristic, or extra finiteness assumption was added. The shift
is explicitly by integer `1`, including the `n = 0` and zero-object cases.

I searched Mathlib and the project with `msearch.py` (LeanFinder and Loogle
queries for affine perfect extension and `PerfectComplex`), `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`, and checked the upstream source names; only
generic derived-category and the two dependency declarations were found. No
existing exact declaration is available. I also read the dependency declarations:
`AlgebraicGeometry.schemeDerivedCategory` is the shared sheaf-module derived
category, and `AlgebraicGeometry.Scheme.IsPerfect` has precisely the global and
all-open derived-category binders used here.

No mismatch was found, so no Lean or node statement was changed. The module
compiles cleanly with `scompile.py`; its sole proof remains the required `sorry`.
