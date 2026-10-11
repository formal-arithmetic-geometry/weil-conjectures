## Worker report

The module `Sheaf.AlgebraicGeometry.PseudoCoherentQCoh` states
`AlgebraicGeometry.Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent`, with `sorry` as
its entire proof. No definitions, dependency modules, or new nodes are needed. The item
copy changes only `lean`.

Source read: https://stacks.math.columbia.edu/tag/08E5, lemma-pseudo-coherent, final
assertion; https://stacks.math.columbia.edu/tag/08EE, first sentence of the proof invoking
that lemma. The local literature checkout is absent on this machine, so the full statements
and proofs were read on the official Stacks website. Tag 08E5 currently has number 36.10.1;
the node's proof_origin says 36.13.5, but the stable tag and label identify the correct lemma.
This numbering metadata fault does not change the statement and is not edited.

Hypothesis and clause correspondence:

- “Let Y be a scheme”: `(Y : Scheme.{u})`, Mathlib's locally affine locally ringed space,
  read with its docstring in `Mathlib/AlgebraicGeometry/Scheme.lean:42`; the morphism
  declaration `Scheme.Hom` was also read at line 74.
- “object E of D(O_Y)”: `(E : schemeDerivedCategory Y)`. This is exactly the recorded
  `def-pc-derived-category` carrier, `DerivedCategory` of
  `SheafOfModules.{u} (moduleRings Y.toRingedSpace)`.
- “pseudo-coherent”: `(hE : IsPseudoCoherent Y E)`, exactly the scheme-local definition
  recorded by `def-pur-pseudo-coherent-complex`. Its full body quantifies over each point,
  an open neighbourhood, a bounded-above cochain complex of finite free module sheaves,
  and an isomorphism with the derived restriction of E.
- “belongs to D_QCoh(O_Y), meaning all cohomology sheaves are quasi-coherent”:
  `schemeDerivedQCohProperty Y E`. Its full body is `∀ n : ℤ`, the object obtained from
  `DerivedCategory.homologyFunctor ... n` applied to E satisfies
  `SheafOfModules.IsQuasicoherent`. Thus all degrees, including negative ones, are covered.
- The two `HasDerivedCategory.{w}` instance binders provide the ambient derived category
  and its restrictions to every open, as required by the recorded pseudo-coherent
  definition. They are the shared localization structures, not geometric conditions on Y.
  Universes `u w` are explicitly declared; no implicit variables are auto-bound.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (def-pc-scheme).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`
  and `AlgebraicGeometry.schemeDerivedQCohProperty` (def-pc-derived-category). Read their
  full signatures, docstrings, and bodies in the repository's module.
- `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent` (def-pur-pseudo-coherent-complex). Read its
  full signature, docstring, and body. This is the single direct import, which also brings
  in the derived-category definitions and scheme type.

The theorem docstring reproduces the node's proof: local finite-free models; their
quasi-coherent terms; quasi-coherence of kernels and cokernels by the recorded proof
nodes; locality; the definition of D_QCoh. No proof is supplied in this stage.

Edge cases checked mathematically against the definitions: the empty scheme is allowed
(the pseudo-coherent pointwise condition is vacuous and module sheaves have vacuous local
quasi-coherence); the zero complex is allowed (all ranks can be zero); bounds and ranks
are not fixed globally; cohomology runs over all integers. No affine, quasi-compact,
separated, Noetherian, bounded-below, or characteristic hypothesis is introduced. Nothing
in the source restricts these cases. There is no statement dispute or correction.

Searches actually run, all on 2026-10-11:

- `msearch.py ... leanfinder "pseudo-coherent derived object has quasi-coherent cohomology
  sheaves"`: eight hits, generic derived support/TStructure and sheaf cohomology
  declarations plus `SheafOfModules.isQuasicoherent`; none states the implication.
- `msearch.py ... loogle "PseudoCoherent, IsQuasicoherent"`: zero hits, unknown identifier
  `PseudoCoherent`.
- `msearch.py ... leansearch "pseudo coherent complex has quasi coherent cohomology"`:
  unavailable, Internal Server Error; not counted as a negative search result.
- `msearch.py ... grep "pseudo.?coherent|PseudoCoherent"`: zero Mathlib hits. Direct `rg`
  with the same pattern over the pinned Mathlib also found none.
- Direct `rg` with the same pattern over `WeilConjectures`: one prose mention in
  `AlgebraicGeometry/Cohomology/DirectImage.lean:604`, no declaration.
- `grep -rn "lem-sc-pseudo-coherent-qcoh"` over `WeilConjectures`: no hits.
- `python3 tools/lean_names_upstream.py show lem-sc-pseudo-coherent-qcoh`: only index
  statistics, no declaration attached to this item.
- `rg` over `lean/Sheaf` for `IsPseudoCoherent|isPseudoCoherent`: existing scheme
  definition and ring-level definitions/theorems, no theorem for scheme quasi-coherent
  cohomology. The ring predicates have different carriers and are not reused here.
- Full new declaration name search over Mathlib, `WeilConjectures`, and `lean/Sheaf`:
  no existing declaration with this name.

Validation: server compilation and `deliver2.py --no-push` are run before READY. The
second reading is reserved for the independent reader, and no delivery is pushed here.

## Second reading by J1

I reread the node, its Stacks source, the dependency declarations, and the Lean file.
The statement items match as follows:

- The scheme `Y` is `(Y : Scheme.{u})`; this is Mathlib's scheme object, with no extra
  geometric hypothesis. Verdict: matches.
- The object `E` of `D(𝒪_Y)` is `(E : schemeDerivedCategory Y)`, using the recorded
  `AlgebraicGeometry.schemeDerivedCategory`. Verdict: matches.
- The pseudo-coherence hypothesis is `(hE : IsPseudoCoherent Y E)`, the recorded
  scheme-local bounded-above finite-free definition. Verdict: matches.
- Membership in `D_QCoh(𝒪_Y)` is the conclusion
  `schemeDerivedQCohProperty Y E`; its definition quantifies over every `n : ℤ` and
  requires `IsQuasicoherent` cohomology. Verdict: matches every cohomological degree.
- The two `HasDerivedCategory.{w}` binders are the localization instances required by
  the cited definitions (the second ranges over every open `U : Y.Opens`). They impose
  no Noetherian, finiteness, separation, characteristic, or affine condition. Verdict:
  technically required by the dependency signatures, with no geometric strengthening.

The source is Stacks Tag 08E5, whose final assertion says that a pseudo-coherent object
is in `D_QCoh`; Tag 08EE invokes exactly that assertion. The empty scheme and zero object
are covered (the pointwise condition and zero complex are allowed); bounds and finite
ranks may vary locally; `n = 0`, negative degrees, and all characteristics are covered.
No universe is left implicit: `u` and `w` are declared and the index of cohomology is
`ℤ`.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with LeanFinder/Loogle/grep and
found no existing declaration for this implication; only the dependency definitions and
generic quasi-coherence results occur. No dependency was unusable and no new definition
node was needed. The module compiled cleanly with `scompile.py`; no mismatch was found,
so no Lean or node statement was changed in this second reading.
