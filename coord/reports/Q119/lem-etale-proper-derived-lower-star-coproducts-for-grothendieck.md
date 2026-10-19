## Worker report

This repair addresses the returned review's H3 and H8 points. The retained packet had
made the coefficient category arbitrary Grothendieck abelian and had replaced the
source proof by retirement metadata. The source lemma is instead the finite-coefficient
proper direct-image lemma. The module
`Sheaf.AlgebraicGeometry.ProperDerivedLowerStarGrothendieckCoproducts` now states
`AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar_of_isProper_grothendieck`
with proof `sorry`.

The corrected Lean statement is:

```lean
theorem preservesCoproducts_rightDerivedLowerStar_of_isProper_grothendieck
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]
    [IsLocallyNoetherian Z] [CompactSpace Z]
    [IsLocallyNoetherian Y] [CompactSpace Y] :
    (∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) g)) ∧
    Nonempty
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) g ⋙
          _root_.DerivedCategory.Plus.ι ≅
        _root_.DerivedCategory.Plus.ι ⋙
          rightDerivedLowerStar (ModuleCat.{u + 1} A) g) := by
  sorry
```

The coefficient clause is rendered by `(A : Type (u + 1)) [CommRing A] [Finite A]` and
`ModuleCat.{u + 1} A`; this is a finite commutative coefficient ring and its module
sheaves. The scheme clause is rendered by `{Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]`
plus `[IsLocallyNoetherian Z] [CompactSpace Z] [IsLocallyNoetherian Y]
[CompactSpace Y]`. `IsProper g` supplies the proper finite-type morphism notion used by
the source. The first conclusion quantifies over every explicitly universe-bound
`I : Type w` and uses `PreservesColimitsOfShape (Discrete I)` on the canonical
`rightDerivedLowerStar (ModuleCat A) g`, so it includes the empty family and all
set-indexed coproducts in the unbounded derived categories. The second conclusion is
the source's bounded-below comparison, rendered as the displayed `Nonempty` natural
isomorphism between `rightDerivedLowerStarPlus` followed by
`DerivedCategory.Plus.ι` and the restriction of the unbounded functor.

The proof docstring now records the source-based route. First, `pqf-lem-proper-basic`
gives quasi-compactness, quasi-separatedness, and finite type, and
`lem-fin-finite-type-fibre-dimension-bound` gives a common fibre-dimension bound,
allowing empty fibres. Second, finiteness of `A` gives a positive annihilating integer;
therefore every module sheaf is torsion. `lem-kun-proper-torsion-cd-bound` gives the
higher-direct-image vanishing above the resulting finite bound, and
`lem-sbc-higher-direct-image-forget-comparison` transfers it from abelian sheaves to
module sheaves. Third, `lem-exc-direct-image-coproducts` gives preservation of every
coproduct for the unbounded derived functor, including the empty family. The
bounded-below comparison is the canonical right-derived-functor comparison from the
direct-image construction. No part of this route is presented as proved in stage 2.

The statement dependencies are `def-weil-proper-morphism`, `pqf-def-locnoeth`,
`def-weil-pbc-quasi-compact-scheme`, `def-weil-pbc-derived-categories`, and
`def-weil-pbc-direct-image`. The proof dependencies are
`pqf-lem-proper-basic`, `lem-fin-finite-type-fibre-dimension-bound`,
`def-weil-pbc-torsion-etale-sheaf`, `lem-kun-proper-torsion-cd-bound`,
`lem-sbc-higher-direct-image-forget-comparison`, and
`lem-exc-direct-image-coproducts`; each is an existing DAG declaration or recorded
Mathlib/upstream declaration. The existing source node
`lem-amb-proper-coproducts` was read and its finite-ring/Noetherian statement and
three-step proof were used as the repair model.

Edge cases checked: `I = Empty` (initial coproduct), singleton and finite `I`, and
arbitrary infinite `I`; empty schemes and empty geometric fibres; the zero finite ring;
and unbounded complexes with no lower cohomological bound. No characteristic,
constructibility, invertibility, or finite-Tor hypothesis was added.

Searches: `msearch.py leanfinder` for “proper derived direct image preserves arbitrary
coproducts on etale module sheaves” found only generic colimit declarations; `loogle`
for derived right-derived coproduct preservation found no exact theorem; grep and `rg`
for `rightDerivedLowerStar`/proper coproducts found the finite-coefficient project
module and the existing source node, but no arbitrary-Grothendieck theorem. The source
and all recorded dependency declarations were read. The repaired file compiled with
`scompile.py` on 2026-10-18.

## Statement corrected

The old statement (recorded verbatim in `statement_change.old_statement`) asserted the
result for an arbitrary Grothendieck abelian coefficient category and arbitrary schemes.
The cited source lemma assumes a finite commutative coefficient ring, proper finite-type
maps between Noetherian schemes, and includes the bounded-below comparison. The node
was corrected to those hypotheses and clauses. Its only citer is
`lem-coef-cartesian-section-adjoint-mates`, which still holds: its coefficient levels
are finite rings and its proper finite-type maps are between finite-type schemes over an
algebraically closed finite field, hence satisfy the corrected Noetherian hypotheses.
No citer was edited.

## Second reading by Q119

I reread the corrected node, its Lean file, the source lemma
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-amb-proper-coproducts.md`,
and the citer. The Lean binders now match finite commutative `A`, proper `g`, locally
Noetherian and quasi-compact `Z,Y`; the first conjunct is arbitrary set-indexed
unbounded coproduct preservation and the second is the bounded-below comparison. The
proof remains entirely postponed (`sorry`), while its docstring gives the finite-fibre,
torsion cohomological-dimension, finite-amplitude, and comparison route. The citer's
finite-level use remains valid under the corrected scope. The repaired file compiles
cleanly via `scompile.py`.

## Maintainer correction for landing (2026-10-18)

This section supersedes the proposed new module and declaration above. The source-based
statement correction is retained. The final Lean binding is existing project declaration
`AlgebraicGeometry.Etale.proper_rightDerivedLowerStar_preservesCoproducts`, module
`Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`, branch `newtargets-dag`,
with `existing: true` and no `file`. The duplicate proposed module
`ProperDerivedLowerStarGrothendieckCoproducts.lean` must be omitted by the merge tool's
new-to-existing record conversion. No replacement Lean module is required.

The exact existing theorem was read in the group clone and independently retrieved with
`scompile.py --source`. It is already present on the immutable delivery's parent. Its
binders are finite commutative `A : Type (u + 1)`, schemes `V,T : Scheme.{u}`, proper
`r`, and local Noetherian and quasi-compact hypotheses on both schemes. Its first
conjunct quantifies over `I : Type w`, independently of `u`, and preserves the colimits
of `Discrete I` for the ordinary unbounded derived direct image. Its second conjunct
is precisely the natural isomorphism identifying the bounded-below direct image with
the restriction of the unbounded one. These agree with the corrected node clause by
clause. All edge cases listed in the worker report remain included.

Findings repaired: H4, duplication of an exact existing project statement; H2, the
original `lean.statement` split the last composite over two lines whereas the file
put it on one line. The supplied record uses the existing theorem's signature verbatim.
The existing theorem's docstring also gives the finite-fibre bound, torsion bound,
forgetful comparison, unbounded acyclic-resolution argument, and bounded-below
compatibility. Its proof remains `sorry`, appropriate to stage 2.

Independent searches used `rg` in Mathlib, upstream WeilConjectures, the group side
library and DAG. The decisive exact match is already recorded by `lem-amb-proper-coproducts`.
LeanSearch for “proper etale derived direct image preserves arbitrary coproducts finite
commutative ring” returned eight unrelated generic declarations. Loogle for the
`PreservesColimitsOfShape` / `rightDerivedLowerStar` pattern reported an unknown identifier;
that result is not evidence of absence.

The immutable delivered file compiled through `scompile.py Q119
lem-etale-proper-derived-lower-star-coproducts-for-grothendieck <snapshot-file>`:
sandbox 4.8 s, library 2.7 s, exit 0, no warnings. The existing replacement theorem's
module was separately reproduced through the same wrapper: sandbox 4.1 s, library
4.4 s, exit 0, no warnings. Both used the 60-second per-file limit and private overlay.
The installed wrapper uses the server overlay despite the earlier local-overlay wording;
no direct SSH command, live Lean edit or global build was performed by the reviewer.

The original statement is preserved verbatim in `statement_change.old_statement` (checked
against the immutable parent). All direct citers were enumerated: there is exactly one,
`lem-coef-cartesian-section-adjoint-mates`. Its steps 2 and 5 apply this result to finite
rings `A_n` and proper compactification maps between Noetherian schemes, so `holds: true`
is correct. There is no second citer to inspect. None of the item's statement or proof
dependencies occurs on the route-pivot dropped list; no item-specific repair note exists
at the inspected shared ref. The new proof differs from the pre-pivot retirement paragraph
and uses the ordinary derived route.
