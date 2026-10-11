## Worker report

The module states `CategoryTheory.exists_stacksGaloisObject_hom_of_isConnected`,
the existence claim of Stacks Project Lemma 0BN2, with `sorry` as its proof.
The local Stacks `.tex` checkout is absent on this machine; I read the lemma
and proof at https://stacks.math.columbia.edu/tag/0BN2.

Clause mapping:

- A category `C` and fibre functor `F` are `{C : Type u} [Category.{v} C]
  (F : C ⥤ Type w)`.
- The hypothesis that `(C,F)` is a Galois category is
  `(hG : IsStacksGaloisCategory F)`.
- The object `X` and its connectedness are `(X : C) [IsConnected X]`.
- The Galois object is `(Z : C)` with `IsStacksGaloisObject F Z`.
  This definition is connectedness plus equality of the cardinalities of
  `Aut Z` and `F.obj Z`; the transitivity equivalence is clause (6) of
  `stacksGaloisCategory_axioms`.
- The morphism to `X` is `(_ : Z ⟶ X)` in the existential. The description
  of the construction by a component of `X^n` is proof information and is
  given step by step in the theorem docstring.

Dependencies: `Sheaf.CategoryTheory.Galois.StacksGaloisCategory` provides
`CategoryTheory.IsStacksGaloisCategory`;
`Mathlib.CategoryTheory.Galois.Basic` provides
`CategoryTheory.PreGaloisCategory.IsConnected`;
`Sheaf.CategoryTheory.Galois.StacksGaloisAxioms` provides
`CategoryTheory.IsStacksGaloisObject` and
`CategoryTheory.stacksGaloisCategory_axioms`. The module imports the latter,
which imports the former two. I read their complete signatures and docstrings.

Edge cases: the statement does not posit a positive fibre cardinality. For a
connected `X`, nonemptiness of `F.obj X` follows from the Stacks axioms and
clause (3) of `stacksGaloisCategory_axioms`; the `n = 0` case is therefore
handled by the theorem rather than excluded by a binder. The singleton fibre
case `n = 1` is included. No choice of a fixed finite index type or universe
of `X` is imposed beyond the universes of the recorded definitions.

Searches: `msearch leanfinder` with "Galois category every connected object
receives a morphism from a Galois object" found Mathlib's
`PreGaloisCategory.exists_hom_from_galois_of_connected`, but it assumes
Mathlib's `GaloisCategory` and a `FiberFunctor`, not the Stacks predicate.
`msearch loogle` with that name and `IsStacksGaloisObject` found no matching
Stacks theorem. `msearch grep` for `exists_hom_from_galois_of_connected` and
`IsStacksGaloisObject` in `CategoryTheory/Galois` found only the Mathlib
theorem and its use. `rg` in `WeilConjectures` and `lean/Sheaf`, and `grep -rn`
for `lem-galois-object-exists` in `WeilConjectures`, found the recorded
Stacks definitions but no existing theorem for this node.

Server compile: clean, exit 0.

## Earlier second reading (a previous round; superseded)

Pending independent review by the second worker. The second worker must
replace this note with a clause-by-clause comparison before delivery.

## Second reading by C1

I independently opened `dag/nodes/sec-curve-estimates/lem-galois-object-exists.json`,
the Stacks source at `pione.tex`, and
`lean/Sheaf/CategoryTheory/Galois/StacksGaloisObjectExists.lean`.
The node's statement and the Lean signature agree item by item:

- The category is `C : Type u` with `[Category.{v} C]`, and the fibre functor is
  `(F : C ⥤ Type w)`.
- The Galois-category hypothesis is the explicit
  `(hG : IsStacksGaloisCategory F)`.
- The connected object is `(X : C) [IsConnected X]`; this is exactly
  `CategoryTheory.PreGaloisCategory.IsConnected`, the Mathlib match recorded by
  `def-galois-connected-object`.
- The conclusion is the same existential order: a category object `Z`, a morphism
  `Z ⟶ X`, and `IsStacksGaloisObject F Z`.
- `IsStacksGaloisObject` is the dependency declaration's connectedness plus
  `Nat.card (Aut Z) = Nat.card (F.obj Z)`; clause (6) of
  `stacksGaloisCategory_axioms` supplies the node's equivalent transitivity wording.

The source Lemma 0BN2 assumes only a Galois category and a connected `X`, exactly
the hypotheses above. Its proof is reflected in the declaration docstring: set
`n = #F(X)`, decompose `X^n`, choose a component containing a distinct tuple, use
the diagonal argument to show every tuple there is distinct, then use the
stabilizer in `S_n` to obtain transitivity and compose with the first projection.
No clause, hypothesis, or quantifier was changed; no mismatch was found and no
Lean file change was needed.

Edge cases were checked against the source and signature. Connectedness excludes
the initial object, so the axioms give `F.obj X` nonempty and hence `n >= 1`; the
`n = 0` case is therefore correctly not introduced as an extra hypothesis. The
singleton fibre (`n = 1`) is included. The component index type may be empty in
the general finite-coproduct axiom, while the selected component exists here
because the chosen fibre tuple is present. No empty category, zero object,
characteristic, or universe is excluded beyond the binders shown in the node.

Searches for an existing declaration were repeated. LeanFinder searched
`Galois category every connected object receives a morphism from a Galois object`
and returned Mathlib's `PreGaloisCategory.exists_hom_from_galois_of_connected`,
which uses Mathlib's separate `GaloisCategory`/`FiberFunctor` setting. Loogle
searched `CategoryTheory.PreGaloisCategory.IsGalois,
CategoryTheory.IsStacksGaloisObject` and found no Stacks theorem. Grep searched
Mathlib `CategoryTheory/Galois`, `WeilConjectures/`, and `lean/Sheaf/` for
`exists_hom_from_galois_of_connected`, `IsStacksGaloisObject`, and the node id;
only the Mathlib candidate and the recorded Stacks declarations were found.
The local Stacks source was also read directly at the cited lemma. Thus there is
no existing exact declaration and no second definition. The module compiled cleanly
with `scompile.py`; this second reading made no code or node changes.
