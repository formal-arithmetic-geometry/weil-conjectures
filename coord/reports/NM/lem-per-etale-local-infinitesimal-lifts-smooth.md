## Worker report

This repair records `existing: true` for
`AlgebraicGeometry.smooth_of_etale_local_infinitesimal_lifts` in the published
module `Sheaf.AlgebraicGeometry.EtaleLocalInfinitesimalSmoothCriterion`.
The live `lem-sfb-etale-local-infinitesimal-lifts-smooth` owns this module.
Its statement is string-equal to the assigned dropped lem-per node, verified
by comparing the current JSON records. Only the assigned node's `lean` field
changes; no Lean file, dependency, definition or statement is added or changed.
The recorded signature is extracted verbatim from the published source.

### Clause-by-clause correspondence

- Schemes V and W and their morphism: `{V W : Scheme.{u}} (f : V ⟶ W)`.
- Locally of finite presentation: `[LocallyOfFinitePresentation f]`.
- Every pair of affine test schemes and every test immersion:
  `∀ (T₀ T : Scheme.{u}) (i : T₀ ⟶ T) [IsAffine T₀] [IsAffine T]`.
- Closed immersion with square-zero defining ideal: `IsFirstOrderThickening i`.
  The recorded definition is exactly `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`.
  No choice of a separate ideal or extra nonemptiness condition is introduced.
- The given two maps: `(a₀ : T₀ ⟶ V) (b : T ⟶ W)`.
- The commuting square `f a₀ = b i`: `a₀ ≫ f = i ≫ b`.
- Existence of a family of test schemes, maps to T, and local lifts:
  `∃ (J : Type u) (Tj : J → Scheme.{u}) (v : ∀ j : J, Tj j ⟶ T)
  (a : ∀ j : J, Tj j ⟶ V), ...`.
- Each covering morphism is étale: `∀ j : J, Etale (v j)`.
- Joint surjectivity: `∀ t : T, ∃ (j : J) (x : Tj j), v j x = t`.
- Each lift lies over b: `∀ j : J, a j ≫ f = v j ≫ b`.
- Each lift restricts to a₀:
  `∀ j : J, pullback.snd i (v j) ≫ a j = pullback.fst i (v j) ≫ a₀`.
  The pullback is `T₀ ×_T Tj j`; `snd` maps to `Tj j` and `fst` to `T₀`.
- The conclusion is exactly `Smooth f`.

There is no affine condition on the covering schemes and no separatedness,
Noetherian, finite-cover, characteristic, uniqueness, or choice-of-lift assumption.
Both schemes and affine tests use `Scheme.{u}`, as in the recorded formal-smoothness
definition. The cover index lives in `Type u`: a jointly surjective cover can be
reduced by choosing one member and a preimage for each point of T, so larger
indexing sets are not needed. No independent smaller test universe is used.

### Dependencies read and used

The statements and bindings of all six `stmt_deps` were read, followed by their
source docstrings and full declarations:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-sbc-first-order-thickening`:
  `WeilConjectures.AlgebraicGeometry.Thickening`,
  `AlgebraicGeometry.IsFirstOrderThickening`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, and `.snd`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`. The additional relative-dimension clause of this
  dependency is not used by the item.

These are public imports. The already stated proof dependencies are ordinary
imports: `WeilConjectures.AlgebraicGeometry.FormallySmooth`
(`AlgebraicGeometry.FormallySmooth`),
`WeilConjectures.CategoryTheory.Sites.Torsor`
(`CategoryTheory.Sheaf.Torsor`, `nonempty_equiv_H_one_torsor`),
`Sheaf.AlgebraicGeometry.EtaleLocalLiftDerivationAction`
(`AlgebraicGeometry.Scheme.InfinitesimalLifts.exists_derivationAction`), and
`WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift`
(`AlgebraicGeometry.Etale.etale_affine_qcoherent_ulift`).
Smoothness itself is already a public import. There is no missing proof import
and no import cycle identified.

The declaration docstring follows all six proof steps of the node: the
quasi-coherent derivation module and sheaf of lifts; local lifts trivialize the
pseudo-torsor; affine étale H¹ vanishes; torsor classification gives a global
section; every test square therefore lifts; locally finite presentation plus
formal smoothness gives smoothness. Read directly in the local Stacks source:
`more-morphisms.tex` definitions/formal criterion (02H0/02H6),
`spaces-more-morphisms.tex` lift-torsor proof (04AM), and
`etale-cohomology.tex` quasi-coherent cohomology comparison (03P2).

### Edge cases

- Empty T is permitted. A first-order thickening has the same points, so T₀ is
  then empty too. `J` may be empty and joint surjectivity is vacuous.
- For nonempty T, the explicit joint-surjectivity clause forces a nonempty cover;
  there is no accidental vacuous witness.
- Zero ideal / identity thickening is included by the existing square-zero
  predicate; the restriction equation retains the given a₀ rather than discarding it.
- Empty V is allowed: squares with a map from T₀ into V force T₀ and T empty;
  the conclusion is the expected smoothness of an empty source.
- Empty W and arbitrary characteristic are allowed; no field or characteristic
  binder occurs. A nonempty source cannot map to an empty target.
- Nonaffine covering members are allowed, and restriction uses the actual scheme
  fibre product, so the affine hypothesis is only on the original test square.

### Searches for an existing statement

All four remote searches used
`python3 /home/ubuntu/weil-launcher-all/batch2/msearch.py NM
lem-per-etale-local-infinitesimal-lifts-smooth ...` on 2026-10-24;
raw summaries are in the sandbox's `searches.jsonl`.

- LeanFinder query: "A locally finitely presented morphism of schemes is smooth if
  every first order infinitesimal lifting problem has solutions etale locally on
  the affine test scheme". Eight hits: smoothness definitions, the standard-smooth
  chart criterion, and consequences of smoothness. None asserts this criterion.
- Loogle query: `AlgebraicGeometry.Smooth, AlgebraicGeometry.LocallyOfFinitePresentation`.
  Three hits: smooth implies lfp, smooth locus is all iff smooth, and the flat
  smooth-fibre criterion. None supplies the stated lifting hypothesis.
- Mathlib grep query: `formallySmooth|formally_smooth|infinitesimal.*smooth`,
  subdirectory `AlgebraicGeometry`. Eight hits in `Morphisms/Smooth.lean` and
  `SmoothFiber.lean`, involving stalk ring maps or smooth fibres; no étale-local
  lifting criterion. Read the relevant signatures in the local source.
- LeanSearch query: "Infinitesimal lifting criterion for smooth morphisms of
  schemes where square zero lifts exist etale locally". Eight hits, including
  `Algebra.FormallySmooth.lift`, `exists_lift`, `of_split`, `of_comp_surjective`,
  and ring-level formally étale and derivation facts. Their global algebra lift
  hypotheses differ from this scheme-level étale-local condition.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `smooth_of_etale_local_infinitesimal_lifts|etale.local.*infinitesimal|infinitesimal.*lifts`:
  found logarithmic lifting conditions, the unique-lift étale criterion, and
  the derivation-action dependency, but no exact criterion.
- Direct item-id search in `lean/WeilConjectures`: no match. A broader source
  search for smooth/lift and étale-local-smooth patterns also found no equivalent
  declaration. The retired declaration mentioned by `lean_removed` is absent;
  the repaired module is owned by the live lem-sfb node, using the current dependency modules.

### Validation

The live replacement module was compiled, passed dry-run preflight, and delivered
as `f29c1f52223`. The maintainer merged it at 04:54 UTC on 2026-10-24, recorded in
coord/ledger.md. This repair reread its full published source with scompile.py
--source and the now-landed node record. The delivery wrapper performs the server
module-mode #check for this existing binding, then preflight. There is no new
Lean module to compile or review in this alias packet.

## Repair of returned delivery c3adc7338948

H4 and route pivot: the theorem was moved to the live reachable
`lem-sfb-etale-local-infinitesimal-lifts-smooth` in the non-dropped module
`Sheaf.AlgebraicGeometry.EtaleLocalInfinitesimalSmoothCriterion`, delivered at
`f29c1f52223` and now merged. Both its module and theorem docstrings carry that
live blueprint id. Its proof's Step 1 cites the live lift-torsor node. Its
mathematically accepted signature and sorry proof were retained unchanged.

The dropped `lem-per-etale-local-infinitesimal-lifts-smooth` now takes
`existing: true` for that published declaration, as the return permits and the
Q83 precedent does for the lift-torsor node. The old dropped module
`Sheaf.AlgebraicGeometry.EtaleLocalInfinitesimalLiftsSmooth` is not recreated.
The replacement module is absent from the exact-line dropped-module list.
No proof or statement dependency is added to the dropped node, and all current
main metadata is preserved. The previous withdrawal packet did not provide this
alias; this packet is a real `lean` change against current main.

The initial combined repair packet was correctly refused because existing:true
cannot target an unpublished sibling. Publication and alias delivery have now
been sequenced, respecting that check. No script was modified or bypassed.
No independent worker was started; the maintainer reviews the repair.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
