## Worker report

The module `Sheaf.AlgebraicGeometry.NodalStalkCompletionReduction` states
`AlgebraicGeometry.nodal_stalk_completion_reduction`, with its entire proof `sorry`.
It introduces no definitions, axioms, or extra nodes. The source is Stacks,
`curves.tex`, Tag 0CBX, `lemma-formal-local-structure-nodal-family`, first proof
paragraph (read locally, lines 4942 onward). The node isolates the completion
reduction before the split-node hypothesis is used. The current blueprint unit
`sk-i-curve-zero` and its ancestor `lem-trf-local-term-locality` were also read;
this is a historical local-algebra input, not the unit's own statement.

Here are abbreviations for this report only (the Lean statement writes them out):
`A0 = S.presheaf.stalk (f t)`, `B0 = T.presheaf.stalk t`,
`D = (f.fiber (f t)).presheaf.stalk (f.asFiber t)`;
`m0`, `n0`, `d0` are their Mathlib maximal ideals;
`A = AdicCompletion m0 A0`, `B = AdicCompletion n0 B0`,
`Dhat = AdicCompletion d0 D`; `iA`, `iB`, `iD` are their `algebraMap`s;
`m = m0.map iA`, `n = n0.map iB`;
`k = S.residueField (f t)`, `f0 = (f.stalkMap t).hom`,
`q0 = (f.fiberStalkMap t).hom`, `Q = B ⧸ m.map φ`,
`q = Ideal.Quotient.mk (m.map φ)`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes, morphism, and point are `{T S : Scheme.{u}} (f : T ⟶ S) (t : T)`.
  The base point is always the term `f t`; no independent point or equality is added.
- Local finite type is `[LocallyOfFiniteType f]`. No quasi-compactness, global
  Noetherianity of the schemes, or global flatness is assumed.
- Flatness at this particular point is `hflat : (f.stalkMap t).hom.Flat`.
  This is precisely flatness of the target stalk over the base stalk.
- The base stalk hypothesis is `[IsNoetherianRing (S.presheaf.stalk (f t))]`.
- The induced residue-field isomorphism is
  `hresidue : IsIso (f.residueFieldMap t)`; it is the actual map induced by `f0`.
- The completions, the maps to them, and extended ideals use `AdicCompletion`,
  `algebraMap`, and `Ideal.map`, literally at the specified stalk maximal ideals.
- `B0` is Noetherian: first conjunct `IsNoetherianRing (T.presheaf.stalk t)`.
  The following `∀ [IsNoetherianRing (T.presheaf.stalk t)], ...` is INSIDE the
  conclusion. It makes this proved fact available to instance synthesis on `B`.
  It is not a hypothesis of the lemma or a restriction of its application.
  Proof irrelevance makes this formulation equivalent to using the derived instance.
- Both completions are Noetherian and local: the four explicit conjuncts
  `IsNoetherianRing A`, `IsNoetherianRing B`, `IsLocalRing A`, `IsLocalRing B`.
  Their actual local-ring instances come from Mathlib's completion theorem.
- Their specified maximal ideals: the two equalities
  `IsLocalRing.maximalIdeal A = m` and `IsLocalRing.maximalIdeal B = n`.
- Completeness: `IsAdicComplete m A` and `IsAdicComplete n B`, using these
  extended ideals rather than accidentally using ideals of the uncompleted rings.
- Both residue fields are canonically `k`: the equivalences
  `eA : k ≃+* IsLocalRing.ResidueField A` and
  `eB : k ≃+* IsLocalRing.ResidueField B` satisfy, for every `a : A0`,
  `eA (residue A0 a) = residue A (iA a)` and
  `eB (residue A0 a) = residue B (iB (f0 a))`.
  These identify the actual canonical maps, not just abstractly isomorphic fields.
- The induced map is `φ : A →+* B`, with `IsLocalHom φ ∧ φ.Flat`.
  Its compatibility square is `φ.comp iA = iB.comp f0`.
  At every `r : ℕ`, `x : A`, and representative `a : A0`, equality
  `AdicCompletion.evalₐ m0 r x = Ideal.Quotient.mk (m0 ^ r) a` implies
  `AdicCompletion.evalₐ n0 r (φ x) = Ideal.Quotient.mk (n0 ^ r) (f0 a)`.
  Quotient surjectivity and extensionality of completion determine `φ` uniquely;
  it is the canonical completion map, not an arbitrary extension on original germs.
- The actual scheme fibre and its point are `f.fiber (f t)` and `f.asFiber t`.
  The actual projection map on stalks is the dependency's `f.fiberStalkMap t`.
- The quotient is `B ⧸ m.map φ`, exactly `B/mB` for the completed-base ideal `m`.
- The canonical `k`-algebra isomorphism is stated as ring maps
  `cQ : k →+* Q`, `cD : k →+* Dhat`, and `e : Q ≃+* Dhat`, with
  `e.toRingHom.comp cQ = cD`. A ring equivalence commuting with coefficient
  homomorphisms is exactly an algebra equivalence for their `toAlgebra` structures.
  These structures are not arbitrary: for every `a : A0`,
  `cQ (residue A0 a) = q (φ (iA a))` and
  `cD (residue A0 a) = iD (q0 (f0 a))`.
  The residue map `A0 → k` is onto, so these equalities uniquely determine both
  coefficient maps. The latter is the coefficient map from the scheme fibre's
  projection to `Spec k`, by its cartesian square. No coefficient-field section of
  the mixed-characteristic complete local ring is being assumed.
- Compatibility with the quotient from `B0`: for every `b : B0`,
  `e (q (iB b)) = iD (q0 b)`.
- Compatibility with completion: for every `r : ℕ`, `x : B`, `b : B0`, the
  equality `evalₐ n0 r x = Ideal.Quotient.mk (n0 ^ r) b` implies
  `evalₐ d0 r (e (q x)) = Ideal.Quotient.mk (d0 ^ r) (q0 b)`.
  These are precisely the finite-level maps induced by the stalk quotient, and
  determine the completed projection. The transition maps are those built into
  Mathlib's `AdicCompletion`, so no independent, uncoordinated family is chosen.

Dependency declarations used (their signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  `LocallyOfFiniteType.stalkMap` (the essentially finite type stalk lemma).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and its
  stalk interpretation; the pointwise assumption uses `RingHom.Flat` directly.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`, `Scheme.Hom.residueFieldMap`, `residue_residueFieldMap`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, `AdicCompletion.evalₐ`, its algebra structure and `algebraMap`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` (flatness through `toAlgebra`).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `asFiber`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `LocallyRingedSpace.Hom` and
  locality of its stalk map (the first proof step).
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType.isNoetherianRing`.
- `Mathlib.RingTheory.Localization.Submodule`: `IsLocalization.isNoetherianRing`.
- `WeilConjectures.RingTheory.AdicCompletionNoetherian`:
  `AdicCompletion.isNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.LocalRing`: the local-ring instance,
  `AdicCompletion.maximalIdeal_eq_map`, `residueField_map_bijective`,
  `isAdicComplete_self`. All are the recorded local-completion dependencies.
- `WeilConjectures.RingTheory.FlatCompletion`: `flat_adicCompletion_of_flat_local`.
- `Sheaf.AlgebraicGeometry.FibreStalkQuotient`: `Scheme.Hom.fiberStalkMap` and
  `Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`.
- `WeilConjectures.RingTheory.LocalCompletionQuotient`:
  `AdicCompletion.exists_local_completion_quotient`.

The already landed definition node `def-trf-fibre-stalk-map` is added to
`stmt_deps`: it owns `AlgebraicGeometry.Scheme.Hom.fiberStalkMap`, recorded as
`existing: true` in `Sheaf.AlgebraicGeometry.FibreStalkQuotient` by N6 on 2026-10-23.
Its definition and full signature were checked against the actual declaration.
The theorem node `lem-sbc-scheme-fibre-stalk-quotient` remains in `proof_deps`,
where its surjectivity and kernel conclusion are used by the proof plan, but is
not a statement dependency. No source statement, proof, proof dependencies, or
dependency node was changed. There are no unusable interfaces or statement disputes.

Edge cases checked: schemes may be empty (then there is no input `t`); no global
Noetherianity or global flatness is silently required. The identity morphism gives
`B/mB = k` and the completion of the field fibre. If `A0` is a field then `m0=0`
and the result is the completion of `B0`, as required. Positive-dimensional and
mixed-characteristic bases are allowed: no embedding `k → A` or `k → B` occurs.
Non-rational points are allowed when their given residue extension is isomorphic.
At `r=0` both finite quotients are zero rings, so the coordinate statements are
valid; positive levels express the nontrivial compatibility. No characteristic,
relative dimension, nodal, split-node, or closed-point hypothesis was added.
All universe and term variables are explicit; `autoImplicit` is disabled.

Searches on 2026-10-24:

- `msearch.py ... leanfinder`, query "For a flat locally finite type morphism of
  schemes completion of stalks is flat and its closed fibre is the completed fibre
  stalk": 8 hits, including `Flat.stalkMap`, `Flat.iff_flat_stalkMap`, and
  `LocallyOfFiniteType.stalkMap`; none states the completed closed-fibre result.
- `msearch.py ... loogle`, query `AdicCompletion, RingHom.Flat`: 0 hits.
- `msearch.py ... grep`, query
  `completion.*[Ff]iber|[Ff]iber.*completion|flat.*[Cc]ompletion`, subdirectory
  `RingTheory`: 3 hits in `Smooth/Flat.lean` and
  `AdicCompletion/AsTensorProduct.lean`. They give flatness over the original
  ring, not the completed base and scheme-fibre comparison.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `completedStalk`, `stalkCompletion`, `flatCompletion`, `completionMap`,
  `localCompletion`, `fiberStalk`, and the proposed theorem name.
  `grep -rn` of the exact item id in `lean/WeilConjectures` found no match.
  Existing fibre-stalk and local completion modules were reused. The nearby
  `AlgebraicGeometry.completedStalkMap` in
  `Sheaf.TraceFormula.CompletedStalkIsomorphismEtale` is the map only, not this
  statement, and its theorem assumes global local Noetherianity. It is not
  imported: our coordinate characterization states the induced map directly,
  without duplicating a map definition or importing an unrelated downstream result.

Validation uses only the prescribed `scompile.py`, one file on the server; the
first version compiled cleanly. The final version, including both explicit local
ring conjuncts, also compiled cleanly during `deliver2.py --no-push`. The dry run
reported `OK (dry run): commit 5f7eedefbdd passes the preflight and compiles;
nothing pushed`. No errors or unexpected warnings remain.

## Second reading by Q48

Author's second pass, not an independent review (the dispatcher brief assigns
independent review to the maintainer). Reopened the node and full generated Lean
signature. Confirmed all four hypotheses, the derived rather than assumed target
Noetherianity, both maximal ideal equalities, both completeness statements, and
both canonical residue identifications. Added explicit `IsLocalRing` conjuncts for
both completions so this clause is visibly present even though Mathlib already
synthesizes those instances from the earlier derived Noetherianity. Checked that
`m.map φ` extends the ideal in the completed base, that `q0` uses the genuine fibre
point, and that the final compatibility quantifies over completed elements and
EVERY finite level, rather than merely over original germs. Checked that the
coefficient maps are uniquely prescribed on `A0 → k`; their commuting equality
expresses `k`-linearity, including mixed characteristic. No statement correction,
new node, dependency repair, or further mismatch was found.

## Repair of return at 298a934b2307

H2 repaired: replaced `lem-sbc-scheme-fibre-stalk-quotient` with the already landed
`def-trf-fibre-stalk-map` in the item's `stmt_deps`. The statement needs only the
plain definition `Scheme.Hom.fiberStalkMap`; the accompanying theorem's conclusion
is used only in the proof. Checked the definition node's existing record and read
its actual declaration in `Sheaf.AlgebraicGeometry.FibreStalkQuotient`.
The theorem remains in `proof_deps`. The Lean file and `lean.statement` are
byte-for-byte unchanged from the returned delivery. No new node is introduced.
The sandbox node was compared with current main before repair; only the pending
Lean record and the added statement dependency differed. The delivery wrapper
rebases this repaired packet on current main. The maintainer's independent review
confirmed all hypotheses, conclusions, canonical maps, and edge cases; the sole
returned defect was the owner of the definition dependency, corrected here.
Re-running the prescribed compilation, dry run, and delivery validates the repair.
