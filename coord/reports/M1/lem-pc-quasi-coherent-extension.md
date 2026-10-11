## Worker report

The module `Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension` states
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_shortExact`, with `sorry` as its
only proof. It adds no definitions, dependency modules, or statement corrections.

Clause-by-clause correspondence:

- A scheme X: the explicit universe declaration `universe u` and binder
  `{X : Scheme.{u}}`; no affineness, finiteness, separation, or field hypothesis.
- The three O_X-modules and their two arrows: `(S : ShortComplex X.Modules)`, with
  `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g`, and `S.zero`. Mathlib's `X.Modules` is
  definitionally `SheafOfModules.{u} X.ringCatSheaf`, the specialization of the
  dependency's general module-sheaf category to the structure sheaf of X.
- The sequence `0 → F₁ → F₂ → F₃ → 0` is short exact: `(hS : S.ShortExact)`.
  The definition requires exactness in the middle, a monomorphism S.f, and an
  epimorphism S.g, precisely the two endpoint zero terms and middle exactness.
- F₁ quasi-coherent: `[S.X₁.IsQuasicoherent]`.
- F₃ quasi-coherent: `[S.X₃.IsQuasicoherent]`.
- F₂ quasi-coherent: the conclusion `S.X₂.IsQuasicoherent`.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`; Scheme extends a locally ringed space with
  affine neighbourhoods at every point. Scheme.Hom is not needed in this statement.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, specialized through
  `AlgebraicGeometry.Scheme.Modules` in `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
  The structure and morphism signatures and the inherited abelian instance were read.
- `pqf-def-coherent`: imported its recorded module
  `Sheaf.AlgebraicGeometry.Coherent`. Its documentation explicitly identifies the
  node's quasi-coherent clause with Mathlib `SheafOfModules.IsQuasicoherent`, from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. The recorded
  `AlgebraicGeometry.RingedSpace.IsCoherent` realizes the coherent clause, which this
  item does not use. The quasi-coherence class is locally a presentation by free
  modules, equivalent on schemes to the affine-local associated-module formulation;
  no second predicate or dependency module is needed.
- Also read `CategoryTheory.ShortComplex` and `ShortComplex.ShortExact` in
  `Mathlib.Algebra.Homology.ShortComplex.Basic` and `.ShortExact`.

Source: local `literature/stacks-project/schemes.tex` is absent on this machine, so
read [Stacks Tag 01IE](https://stacks.math.columbia.edu/tag/01IE) directly. Its affine
extension case and the affine-local definition of quasi-coherence give the node's
statement for an arbitrary scheme. The declaration docstring carries all three DAG
proof steps: restriction to affines, the principal-open lifting/gluing argument and
adjunction comparison, and locality. No reliance on the middle term already being
quasi-coherent occurs in that argument.

Edge cases checked before writing: the empty scheme is allowed; zero end terms and
the all-zero sequence are allowed; modules need not be finitely generated; there is
no base ring or characteristic restriction. There is no nonemptiness hypothesis.
The arbitrary scheme universe u matches Mathlib's ordinary category of O_X-modules;
there is no independently quantified smaller universe of test objects. The short
exactness hypothesis is substantive (it includes both mono and epi), not an identity
morphism property which holds automatically. All variables and universes are bound.

Searches for an existing theorem (2026-10-11):

- `msearch.py ... leansearch "quasi-coherent sheaves closed under extensions short
  exact sequence"`: service unavailable, Internal Server Error; no verdict inferred.
- `msearch.py ... leanfinder "An extension of quasi-coherent modules on a scheme is
  quasi-coherent in a short exact sequence"`: eight hits, the abelian instances,
  quasi-coherence predicate and its data; no extension-closure result.
- `msearch.py ... loogle "SheafOfModules.IsQuasicoherent"`: twelve hits, including
  presentations, finite presentation, restriction, pushforward and locality, but no
  short-exact extension result.
- `msearch.py ... grep
  "[Qq]uasi.*([Ee]xtension|[Ss]hort[Ee]xact)|([Ee]xtension|[Ss]hort[Ee]xact).*[Qq]uasi"`:
  two unrelated quasi-isomorphism results in HomologySequenceLemmas.
- `rg` of `IsQuasicoherent` in Mathlib Modules/ and Sheaf/Quasicoherent.lean:
  definitions, tilde, restriction, affine comparison and locality, no extension closure.
- `rg` of `quasi.coherent.extension|isQuasicoherent.*(short|extension)|ShortExact.*[Qq]uasi`
  in WeilConjectures/ and lean/Sheaf/: only unrelated extension-of-a-module-to-a-larger-
  open text in Compactification, no matching theorem. `grep -rn` for the exact item id
  in WeilConjectures/ gave no hits. A further `rg IsQuasicoherent` in WeilConjectures/
  showed the existing predicate's uses in descent, tilde, vector bundles and Picard.
- Full proposed declaration name checked in `dag/lean_names_upstream.json`, Mathlib,
  WeilConjectures/ and lean/Sheaf/: no collision.

Validation: `scompile.py M1 lem-pc-quasi-coherent-extension` compiled the module on the
server in 2.6 seconds, exit 0, with no errors or warnings. The Lean signature was read
back using `tools/stage2_delivery.py signature` before recording it in the node.
There are no statement disputes or node faults.

## Second reading by M1

Independent reading of the node, its three statement dependencies, their declarations,
and the delivered Lean file found no mathematical or typing mismatch. No Lean or node
change was needed; this section records the second reading.

Objects, hypotheses and conclusion (H3):

- Scheme X: `{X : Scheme.{u}}` renders exactly an arbitrary scheme. I read
  `Scheme.local_affine` in Mathlib's Scheme.lean: a locally ringed space with affine
  neighbourhoods. Verdict: same object as def-pc-scheme, with no affine, Noetherian,
  separation, base-field, or finite-type restriction.
- Three O_X-module sheaves and the two arrows: `S : ShortComplex X.Modules` packages
  `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g`, and `S.zero : S.f ≫ S.g = 0`.
  I read Scheme.Modules in Modules/Sheaf.lean and SheafOfModules and its Hom in
  ModuleCat/Sheaf.lean. The carrier is `SheafOfModules.{u} X.ringCatSheaf`;
  morphisms are module-presheaf morphisms. This is the structure-sheaf specialization
  of def-weil-sheaf-of-modules-category, not the quasi-coherent subcategory. Verdict: exact.
- Short exactness including the two zero endpoints: `hS : S.ShortExact`.
  Reading ShortComplex/ShortExact.lean shows its fields are `S.Exact`, `Mono S.f`,
  and `Epi S.g`. The abelian category instance in Modules/Sheaf.lean needs no extra
  user hypothesis. Verdict: exactly the short exact sequence in the node.
- F₁ quasi-coherent: `[S.X₁.IsQuasicoherent]`. Verdict: exact.
- F₃ quasi-coherent: `[S.X₃.IsQuasicoherent]`. Verdict: exact, with no assumption
  that the middle term is already quasi-coherent.
- F₂ quasi-coherent: conclusion `S.X₂.IsQuasicoherent`. Verdict: the whole and only
  conclusion of the node. Class-valued Prop binders do not change quantifier order
  or add mathematical structure beyond the two stated hypotheses.

For the last three clauses I opened pqf-def-coherent and its recorded Coherent.lean.
Its quasi-coherent clause explicitly uses Mathlib SheafOfModules.IsQuasicoherent,
while the newly defined RingedSpace.IsCoherent serves the different coherent clause.
I independently read IsQuasicoherent (local presentations by free modules), and
Scheme.Modules.isQuasicoherent_iff_isIso_fromTildeΓ in Modules/Tilde.lean. The latter
confirms its agreement on affine schemes with the associated-module formulation in
pqf-def-coherent. There is no missing notion, private predicate, or unusable dependency
requiring a delivery module. There are no new nodes or dependency modules to review.

Source reading: schemes.tex is absent locally. I fetched the upstream Stacks
schemes.tex read-only and read the full lemma-extension-quasi-coherent statement,
proof, and surrounding section introduction. I also read the rendered Tags
[01IE](https://stacks.math.columbia.edu/tag/01IE) and
[01IA](https://stacks.math.columbia.edu/tag/01IA). The section has no hidden
Noetherian or finiteness assumptions. Tag 01IE gives two-out-of-three on an affine
scheme; this node specifically takes its extension case and applies locality on an
affine cover. The Lean correctly states that node rather than all three cases.
The docstring carries all three DAG steps, including the principal-open lifting
ideal, finite gluing argument, adjunction comparison on a basis, and final locality.
It does not use the counit-isomorphism criterion on an unproved quasi-coherent middle
term. No statement correction or citer review is necessary.

Edge cases: the empty scheme and zero module sheaves are admitted; no Nonempty
binder excludes them. There is no indexing set, n, or characteristic parameter.
The node does not require finite generation, and neither does the Lean. `universe u`
is bound explicitly and shared by Scheme and its ordinary module sheaves, with no
independently smaller test-object universe or vacuous hypothesis. The zero ring
and arbitrary base-ring characteristics are admitted through arbitrary schemes.

Independent H4 searches (different wording from the first worker):

- LeanFinder: "On a scheme the full subcategory of quasicoherent modules is closed
  under extensions in the abelian category of all module sheaves". Eight hits:
  abelian instances and quasi-coherence definitions/data; no extension theorem.
- Loogle: `CategoryTheory.ShortComplex.ShortExact, SheafOfModules.IsQuasicoherent`.
  Zero hits. An initial unqualified ShortComplex query was rejected as an unknown
  identifier, and was not treated as evidence.
- LeanSearch: "Quasicoherent module sheaves on schemes form an extension closed
  subcategory". Service unavailable (Internal Server Error); no verdict inferred.
- `rg` case-insensitively for quasicoherent with extension, ShortExact or Serre in
  Mathlib AlgebraicGeometry and ModuleCat, source WeilConjectures, and project
  lean/Sheaf. Only unrelated extension-to-a-larger-open comments in
  Compactification/FiniteTypeExtension and FiniteTypeDirected. No matching theorem.
- Exact declaration name and item id searched in dag/lean_names_upstream.json,
  source WeilConjectures, and project lean/Sheaf: no declaration collision.

H5-H9: no definitions, hollow data, or proved auxiliary statements occur; the sole
proof is `sorry`. Both docstrings cite Stacks 01IE and the blueprint id. Imports use
allowed paths and supply the recorded quasi-coherence dependency and short exactness.
All Lean lines are within 100 characters, and all variables and universes are bound.
The node's lean.statement agrees verbatim with the theorem signature. No mismatch
was found and no correct Lean was rewritten.
