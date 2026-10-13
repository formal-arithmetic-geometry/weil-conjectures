## What changed

Proved `AlgebraicGeometry.horizontal_ordinary_inverse_fixed_pasting` from the new forward
ordinary identity by explicit left/right inverse cancellation. Added private categorical
cancellation and QCoh inverse-component lemmas. Constructed the upper comparison, base
comparison and ordinary transfer square as real definitions in
`Sheaf.AlgebraicGeometry.HorizontalOrdinaryForwardFixedPasting`; their factors are the
previous inline data. The item publicly imports that module because its refactored
statement names the constructions. The statement has exactly the same hypotheses and
mathematical conclusion; the natural-language node statement stays unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.horizontal_ordinary_inverse_fixed_pasting` (node
`lem-sc-horizontal-ordinary-inverse-fixed-pasting`). Added one hole:
`AlgebraicGeometry.horizontal_ordinary_forward_fixed_pasting` (node
`lem-sc-horizontal-ordinary-forward-fixed-pasting`). This is a decomposition, net zero
holes: the forward theorem has no ordinary invertibility hypotheses, and the inversion,
full-faithfulness reflection, functorial inverse cancellation and horizontal component
calculation are proved here. All three comparison definitions contain actual data and
no sorry. No other sorry is added.

## No longer needed

The original public imports supply declarations used by the signatures and constructions.
The old direct proof dependencies `def-pc-derived-base-change-map`,
`lem-pc-ringed-spaces-derived-pullback-composition`, and
`lem-sc-horizontal-duality-mate-comparisons` are no longer direct proof dependencies
of the inverse theorem: their work is now carried by the forward-pasting theorem and
its comparison definitions. They remain transitively needed and are not pruned from
the targets' closure. No module is claimed
pruned. No supplied right adjoint to either projection direct image is used.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-03e3a (head 03e3a649f), both B2 points: made the upper
comparison node self-contained by defining A, P, Q, e and the first projections
v1, v2 and u exactly as requested. Made the forward-pasting node self-contained
by defining e, the second projections p and q, the first projection u, and
the functor notation L(m) and R(m), with the requested dependency citations.

The original inline fixed comparisons combined with duplicate horizontal/QCoh functor
names cause kernel normalization to exceed 60 seconds, even after every tactic closes.
Naming the exact constructions with explicit functor signatures makes the item compile in
about four seconds. This changes the interface representation, not the statement's
meaning. The existing caller requires its normalization proof to recognize those names.
The Mathlib LeanSearch service returned Internal Server Error; LeanFinder, Loogle and
source grep were also tried. No shorter fixed-comparison theorem was found.

## New nodes

`lem-sc-horizontal-ordinary-forward-fixed-pasting` is the uninverted geometric equation,
the first two steps of the old plan, with a complete source-based proof in its docstring.
`def-sc-horizontal-ordinary-transfer`, `def-sc-horizontal-ordinary-upper-comparison`, and
`def-sc-horizontal-ordinary-base-comparison` record the three explicit constructions in
that module. They use only the already pinned families and adjunctions. The unit route
is unchanged, and no unit or chapter file is edited.

Change record: `coord/changes/horizontal_ordinary_inverse_fixed_pasting.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting` (unclaimed): the original
fails against the new interface at its final `rfl` (line 218); it compares a mate square
and inline horizontal comparisons with `horizontalOrdinaryTransfer`,
`horizontalOrdinaryUpperComparison` and `horizontalOrdinaryBaseComparison`. Its old simp
arguments `← hk` and `TwoSquare.mk` are consequently unused. The adaptation adds three private rfl equations for the constructions and includes them
in the existing simp list. Every existing declaration signature and visibility is
retained. Only those three necessary private equations and the final simp list change. The caller
compiles in 25 seconds; the item compiles in five seconds.

## Earlier second reading (a previous round; superseded)

1. Compared both existing modules with the repository versions before delivery. The
   inverse theorem's only signature changes are those declared in
   `coord/changes/horizontal_ordinary_inverse_fixed_pasting.md`: three existing inline
   constructions receive names, and definitionally equal QCoh functor names replace
   the horizontal names. Checked every construction factor and equality orientation;
   all hypotheses and the conclusion are preserved. The adapted caller's existing
   signatures, visibility and docstrings are byte for byte unchanged. No target or
   pre-existing definition changes. The tool's counterfactual compilation confirmed
   that the original caller compiles against baseline, fails at its final rfl against
   the changed dependency, and the adapted caller compiles. Its three private rfl
   equations and their use in the existing simp list are precisely the forced edits.

2. Compiled the three modules in dependency order using lcompile.py, without errors
   or warnings. Inspected all declaration bodies: the sole new sorry is the named
   `AlgebraicGeometry.horizontal_ordinary_forward_fixed_pasting`; there are no hollow
   definitions or forbidden declarations. The delivery tool's all-declaration axiom
   probe passed. An additional scratch #print axioms check covers the three new
   definitions and the forward, inverse and caller theorems; only permitted axioms
   and sorryAx from open dependencies occur. The cancellation proof uses the two
   correct inverse directions: beta followed by tau, and sigma followed by gamma.

3. Read the forward statement, its complete docstring argument and node. It is the
   uninverted geometric compatibility step, without any base-change isomorphism
   hypothesis; it is a strict part of the inverse argument, which separately proves
   component isomorphism reflection, the inverse of the successive composite, and
   cancellation. Identity arrows reduce to the coherent comparison/triangle laws;
   zero complexes and empty schemes introduce no exception. Its three construction
   definitions contain explicit data, with no arbitrary witness of mere existence.
   Independently searched LeanFinder for counit transposes of composite base change,
   Loogle for conjugateEquiv, and rg for ordinary/horizontal pasting and conjugate
   counit formulas. Found generic mate tools, underived comparisons, the proved
   ambient DerivedBaseChangeHorizontalPasting and DerivedBaseChangePasting, and the
   still-open RectangleQCohOrdinaryCompatibility with differently oriented comparison
   hypotheses. None closes this fixed QCoh transfer equation by direct application.
   Checked the sources online: Stacks Tags 0ATM, 08HY and 0D5S support the forward
   pasting, counit definition and pullback composition used in the proposed proof.
   The fixed-transfer identification requires an additional restriction/mate
   calculation, so the remaining hole was not closed in a few minutes.

4. The real inverse cancellation is the shortest reduction found from the forward
   ordinary identity. Public imports expose names required by signatures and explicit
   definitions; added plain imports for the two proved ambient pasting declarations
   named in the remaining forward node's plan. Completed No longer needed by naming
   all three old proof dependencies no longer used directly. They remain transitive
   dependencies; no module is claimed pruned. Read
   dag/units/sk-thm-picard-duality.json: its realized entries are unchanged and neither
   theorem realizes a unit-level step here. The reduction remains below the unit
   route, preserving the ordinary-pasting then inversion argument.

5. Checked node declarations and signatures against Lean, proof_deps against the
   union of the proof steps' uses, and proof_origin against the written route.
   The inverse node records forward pasting followed by actual inverse cancellation;
   the forward node records the remaining geometric calculation. Added missing
   derived-category stmt_deps citations on the new comparison definition nodes and
   lean_audit none records on the three new definition nodes. No unit or chapter
   record was changed.

Second reading changed only the two proof-dependency imports, new-node metadata,
verbatim signature formatting in the nodes/change record, and the completeness of
the pruning/review report. The existing proofs were retained.
This remains a decomposition: one original hole closed, one strictly lower hole added,
net zero; it is not a completed proof of the whole import closure.

## Forced adaptations

### Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting
Original against changed dependencies failed:
```
≫ g) hβh ≫ₕ
              (mateEquiv adjc adjd).symm
                ((horizontalMateRightAdjointIso (pullbackLeftPullbackSndIso f g h) (pullback.snd f (h ≫ g))
                      (pullback.snd (pullback.snd f g) h) ⋯ c d adjc adjd).inv ≫
                  d.leftUnitor.inv)).app
          E =
      (qcInverseBaseChange f g hβ ≫ₕ qcInverseBaseChange (pullback.snd f g) h hβ₂).app E ≫
        (horizontalMateComp h g).hom.app ((horizontalMatePushforward f).obj E) ↔
    (qcDirectImage (pullback.snd (pullback.snd f g) h)).map ((horizontalOrdinaryUpperComparison f g h).hom.app E) ≫
        (qcInverseBaseChange f (h ≫ g) hβh ≫ₕ
              horizontalOrdinaryTransfer (pullbackLeftPullbackSndIso f g h) (pullback.snd f (h ≫ g))
                (pullback.snd (pullback.snd f g) h) ⋯).app
          E =
      (qcInverseBaseChange f g hβ ≫ₕ qcInverseBaseChange (pullback.snd f g) h hβ₂).app E ≫
        (horizontalOrdinaryBaseComparison g h).hom.app ((qcDirectImage f).obj E)
/tmp/forced-adaptation-55mdnh_0/lean/Sheaf/AlgebraicGeometry/HorizontalInverseSquareFixedPasting.lean:216:30: warning: This simp argument is unused:
  ← hk

Hint: Omit it from the simp argument list.
  [apply] simp only [s, r, κ, τ, σ, TwoSquare.mk] at ho ⊢

Note: Simp arguments with `←` have the additional effect of removing the other direction from the simp set, even if the simp argument itself is unused. If the hint above does not work, try replacing `←` with `-` to only get that effect and silence this warning.

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-55mdnh_0/lean/Sheaf/AlgebraicGeometry/HorizontalInverseSquareFixedPasting.lean:216:36: warning: This simp argument is unused:
  TwoSquare.mk

Hint: Omit it from the simp argument list.
  [apply] simp only [s, r, κ, τ, σ, ← hk] at ho ⊢

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

(with the modules compiled into /tmp/forced-adaptation-55mdnh_0/.lbuild) [27.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by D2

1. Compared every existing delivered module with the repository using diff and the
   declaration scanner. Verdict: no accidental signature or visibility change. The
   inverse theorem's text changes only as declared in the change record: its three
   inline constructions have names and definitionally equal QCoh functor names replace
   horizontal names. Checked the definitions factor by factor against the original
   lets. No hypothesis, conclusion, target or pre-existing definition changes meaning.
   The caller's existing signatures are unchanged; its three private rfl equations and
   additional simp arguments are the forced normalization adaptation. The downstream
   search finds only that caller as an external direct user of the inverse theorem.

2. Compiled the delivered set in import order with lcompile.py: forward 4.3 seconds,
   inverse 5.0 seconds, caller 22.5 seconds, with no errors or warnings. Verdict: the
   new inverse proof is valid conditional on the forward theorem. Read the categorical
   cancellation, fully faithful isomorphism reflection and horizontal inverse-component
   calculation; their directions are beta followed by tau and sigma followed by gamma.
   Recompiled the scratch axiom checks for all three definitions and all three public
   theorems: only propext, Classical.choice, Quot.sound and sorryAx occur. The two
   comparison definitions need no sorryAx; transfer's sorryAx comes from inherited
   adjunction dependencies. Its data are explicit composites and uniqueness comparisons,
   not an arbitrary witness of a mere existence statement. No forbidden declaration or
   sorry inside a definition occurs. The sole added hole is the reported forward theorem.

3. Read the new forward theorem, its docstring and its node against
   [Stacks 0ATM](https://stacks.math.columbia.edu/tag/0ATM),
   [08HY](https://stacks.math.columbia.edu/tag/08HY),
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S) and
   [0ATR](https://stacks.math.columbia.edu/tag/0ATR). Verdict: the uninverted pasting
   identity is true and is a strict part of the old argument; it drops the three
   base-change invertibility hypotheses and leaves the actual inversion work proved
   in the item. The supplied comparison arguments are constrained to equal the explicit
   constructions. Identity arrows use the coherent identity and triangle laws; empty
   schemes and zero objects require no nonvanishing or existence condition. Independently
   searched LeanFinder for Beck-Chevalley composition through pullback adjunction counits,
   Loogle for rightAdjointUniq and counit, and grep for horizontal base change and
   conjugate counits, plus rg on the local rectangle/horizontal modules. Generic
   rightAdjointUniq_hom_app_counit and conjugateEquiv_counit are useful tools; the
   proved ambient pasting laws still require restriction and transfer identification.
   RectangleQCohOrdinaryCompatibility remains sorry and has different comparison
   hypotheses. No direct replacement or proof closable in a few minutes was found.

4. Checked the proof from its outer hole downwards and read the old proof_deps and
   sk-thm-picard-duality realized record. Verdict: the real cancellation proof follows
   forward ordinary pasting followed by inversion, below the unit route. All three
   omitted old direct dependencies are listed in No longer needed; they remain
   transitive dependencies. No module is pruned. Public imports supply signature and
   construction names; the two ambient-pasting imports in the forward module are plain
   proof-plan imports. No unit or chapter file changes. This is one hole closed and
   one lower hole added, a decomposition with net zero holes, not a complete proof of
   the import closure.

5. Checked each node's Lean declaration and signature, sources, creation and blueprint
   fields, and proof_deps against the union of proof-step uses. Verdict: the inverse
   node agrees with forward pasting followed by reflection and cancellation; the forward
   node records the remaining geometric calculation. The existing node changes only
   lean, proof, proof_deps and proof_origin. Repaired two copied construction proof
   descriptions: the base comparison is just horizontalMateComp, and the upper comparison
   is its three explicit pullback factors; neither uses the transfer's inverse unit.

Second reading changed only those two DAG proof descriptions and this report. Retained
all Lean statements, definitions and proofs. Closed
AlgebraicGeometry.horizontal_ordinary_inverse_fixed_pasting; added
AlgebraicGeometry.horizontal_ordinary_forward_fixed_pasting; no further hole was closed
or introduced by this reading.

## Forced adaptations

### Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting
Original against changed dependencies failed:
```
≫ g) hβh ≫ₕ
              (mateEquiv adjc adjd).symm
                ((horizontalMateRightAdjointIso (pullbackLeftPullbackSndIso f g h) (pullback.snd f (h ≫ g))
                      (pullback.snd (pullback.snd f g) h) ⋯ c d adjc adjd).inv ≫
                  d.leftUnitor.inv)).app
          E =
      (qcInverseBaseChange f g hβ ≫ₕ qcInverseBaseChange (pullback.snd f g) h hβ₂).app E ≫
        (horizontalMateComp h g).hom.app ((horizontalMatePushforward f).obj E) ↔
    (qcDirectImage (pullback.snd (pullback.snd f g) h)).map ((horizontalOrdinaryUpperComparison f g h).hom.app E) ≫
        (qcInverseBaseChange f (h ≫ g) hβh ≫ₕ
              horizontalOrdinaryTransfer (pullbackLeftPullbackSndIso f g h) (pullback.snd f (h ≫ g))
                (pullback.snd (pullback.snd f g) h) ⋯).app
          E =
      (qcInverseBaseChange f g hβ ≫ₕ qcInverseBaseChange (pullback.snd f g) h hβ₂).app E ≫
        (horizontalOrdinaryBaseComparison g h).hom.app ((qcDirectImage f).obj E)
/tmp/forced-adaptation-6m0bfn0a/lean/Sheaf/AlgebraicGeometry/HorizontalInverseSquareFixedPasting.lean:216:30: warning: This simp argument is unused:
  ← hk

Hint: Omit it from the simp argument list.
  [apply] simp only [s, r, κ, τ, σ, TwoSquare.mk] at ho ⊢

Note: Simp arguments with `←` have the additional effect of removing the other direction from the simp set, even if the simp argument itself is unused. If the hint above does not work, try replacing `←` with `-` to only get that effect and silence this warning.

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-6m0bfn0a/lean/Sheaf/AlgebraicGeometry/HorizontalInverseSquareFixedPasting.lean:216:36: warning: This simp argument is unused:
  TwoSquare.mk

Hint: Omit it from the simp argument list.
  [apply] simp only [s, r, κ, τ, σ, ← hk] at ho ⊢

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

(with the modules compiled into /tmp/forced-adaptation-6m0bfn0a/.lbuild) [23.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
