## Worker report

The module `Sheaf.RingTheory.GlobalCompleteIntersectionPrincipalLocalization` states
`Algebra.isGlobalCompleteIntersection_localizationAway`. It imports the recorded definition
`Algebra.IsGlobalCompleteIntersection` from `Sheaf.RingTheory.CompleteIntersectionOverField`
and Mathlib's `Localization.Away`.

The binders render the node statement as follows: `k : Type u` with `[Field k]` is the field;
`T : Type v` with `[CommRing T] [Algebra k T]` is the commutative k-algebra; `hT` is the
hypothesis that T is a global complete intersection; and `g : T` is the element being inverted.
The conclusion `IsGlobalCompleteIntersection k (Localization.Away g)` is the assertion that the
principal localization is a global complete intersection over k. Mathlib supplies the commutative
ring and algebra structures on `Localization.Away g`, with the k-algebra structure induced by
`k → T → T_g`.

The proof is `sorry` as required at stage 2. Its docstring records the four proof clauses from
the node: the zero-localization case; extraction of a polynomial presentation and dimension
invariance through the principal open; adjoining an inverse variable and computing the kernel;
and counting variables, equations, and dimension.

Dependency declarations used:

* `Algebra.IsGlobalCompleteIntersection` — `Sheaf.RingTheory.CompleteIntersectionOverField`.
* `Localization.Away` — Mathlib `Mathlib/RingTheory/Localization/Away.lean` (the dependency
  node records `IsLocalization.Away` for its universal characterization).

Edge cases checked: `g = 0` (the localization may be the zero ring, covered by the zero-ring
clause), `g = 1` (localization is T), and the zero ring T (already covered by the definition).
The universes are explicit and permit arbitrary field and algebra sizes.

Searches made: `rg -n "IsGlobalCompleteIntersection|GlobalCompleteIntersection|localizationAway" lean/Sheaf`
found only the dependency definition and unrelated localization lemmas; the corresponding grep
in `WeilConjectures/` found no declaration. The stage-1 node records LeanFinder, Loogle,
LeanSearch, and Mathlib grep searches, all with no exact theorem match (only standard-smooth
localization analogues and generic localization declarations). No existing declaration states
this theorem.

## Earlier second reading (a previous round; superseded)

I reread the node and module side by side. The field, commutative ring, algebra, global-complete-
intersection hypothesis, and element `g` are each explicit binders, and the conclusion uses
exactly `Localization.Away g`, matching the node's `T_g` and its induced k-algebra structure.
No hypothesis or conclusion clause is added or omitted. The dependency declaration is imported
rather than copied. The zero, unit, and zero-ring cases listed above ensure the statement does not
exclude the edge cases covered by the definition.

## Second reading by F1

I opened the node and its source citation (Stacks Algebra, Lemma 00SA, part (1),
with Definition 00S9 for the meaning of global complete intersection) and matched every
part of the statement against the Lean declaration. The objects and hypotheses are:

* The field `k` is rendered by `(k : Type u) [Field k]`.
* The commutative `k`-algebra `T` is rendered by `(T : Type v) [CommRing T] [Algebra k T]`.
* The global complete intersection hypothesis is exactly `(hT : IsGlobalCompleteIntersection k T)`, using `Algebra.IsGlobalCompleteIntersection` from `Sheaf.RingTheory.CompleteIntersectionOverField`.
* The element to invert is exactly `(g : T)`.
* The conclusion is exactly `IsGlobalCompleteIntersection k (Localization.Away g)`;
  Mathlib supplies the induced ring and `k`-algebra structures on this localization.
  `Localization.Away` is the recorded Mathlib declaration for
  `def-weil-ring-localization-away`.

The quantifier order is `k`, `T` and its instances, `hT`, then `g`, followed by the
conclusion, matching the node's “let ... then ...” statement. There are no additional
hypotheses, finiteness assumptions, characteristic restrictions, or universe restrictions.
The source's zero-localization convention is inherited through the exact definition used
in `hT` and the conclusion. I checked `g = 0`, `g = 1`, the zero ring `T`, and empty
presentation index types (`Fin 0`) against that definition; the Lean statement excludes
none of these cases. The explicit universe levels `u` and `v` allow arbitrary sizes.

The theorem body contains only `sorry`, and its docstring records the four proof steps from
the node (zero case; presentation and dimension; adjoining an inverse and the kernel;
variable/equation count), with the blueprint identifier and source place. There is no
hollow definition or private replacement of a dependency. The module compiled cleanly with
`scompile.py`; no mismatch was found and no Lean change was needed.

For the duplicate-definition check I searched the project and slopmaster2 sources with
`rg` for `IsGlobalCompleteIntersection` and the theorem name, and ran `msearch.py`'s
LeanFinder search for “global complete intersection localization away”. The only project
declaration is the dependency definition; Mathlib results are standard-smooth localization
analogues and generic localization APIs, with no exact theorem. Thus this statement module
is required.
