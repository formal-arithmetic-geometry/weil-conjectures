## Worker report

The item is already stated by the sorry-free upstream declaration
`AlgebraicGeometry.Compactification.isCofiltered_of_field` in
`WeilConjectures.Compactification.CategoryBaseChange`. No new module is written. The node copy
changes only its `lean` record and records the existing declaration on branch `slopmaster2`.
The declaration has no `sorry` and its source file prints only the permitted axioms.

The source is the blueprint node
`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-comp-category/prop-compactification-refinement.md`,
node order 415. The upstream declaration's docstring explicitly identifies the same blueprint
node and says that compactifications of a separated morphism of finite-type schemes over a field
are nonempty and cofiltered.

Hypothesis and conclusion correspondence:

- The field `K` is the explicit binder `{K : Type u} [Field K]`.
- The finite-type `K`-scheme structures on `X` and `Y` are the displayed structure maps
  `pX : X ⟶ Spec (.of K)` and `pY : Y ⟶ Spec (.of K)`, with exactly
  `[LocallyOfFiniteType pX] [QuasiCompact pX]` and
  `[LocallyOfFiniteType pY] [QuasiCompact pY]`. For a field, these are the recorded
  finite-type-over-`K` hypotheses.
- The morphism is `(f : X ⟶ Y)`, and `(hf : f ≫ pY = pX)` says that it is a `K`-morphism.
- `[IsSeparated f]` renders the separatedness hypothesis.
- `IsCofiltered (Compactification f)` renders the complete conclusion. Mathlib's
  `CategoryTheory.IsCofiltered` class requires a `Nonempty` object, a common predecessor for
  every pair of objects, and an equalizing predecessor for every pair of parallel arrows.
  Thus it gives the node's nonemptiness, common refinement for two objects (and finite families by
  iteration), and equalization of parallel refinements. The category and its objects and arrows
  are the recorded declarations `AlgebraicGeometry.Compactification.Compactification` and
  `AlgebraicGeometry.Compactification.Refinement`, so no private second definition is introduced.

The dependency declarations read and used are:

- `def-weil-compactifications-refinements`: `AlgebraicGeometry.Compactification.Refinement` and
  `AlgebraicGeometry.Compactification.category` in
  `WeilConjectures.Compactification.Refinement`.
- `thm-nagata-compactification`: `AlgebraicGeometry.NagataCompactification` in
  `WeilConjectures.Compactification.NagataCompactification`, which supplies the nonempty
  compactification in the upstream proof.
- `def-weil-scheme-morphism-properties`: this is a convention/collector node; its named
  properties are rendered by the Mathlib and upstream declarations cited by the dependency
  records, rather than by a separate declaration of its own.

The full upstream signature was read at
`WeilConjectures/Compactification/CategoryBaseChange.lean`, lines 271--287, and the complete
`IsCofiltered` definition was read in Mathlib's
`Mathlib/CategoryTheory/Filtered/Basic.lean`, lines 577--596. The upstream theorem is
sorry-free in the current `slopmaster2` checkout; its file also records the axiom census
`propext`, `Classical.choice`, and `Quot.sound`.

Edge cases checked: `IsCofiltered` includes the nonempty case (so the empty source scheme is
covered whenever the stated hypotheses hold); pair refinements include identical objects and
identity arrows; the parallel-arrow clause includes equal arrows and does not require a
separate monomorphism assumption. The theorem keeps arbitrary universe `u` and does not add
Noetherian, quasi-separated, or finite-type assumptions beyond those displayed structure maps.

Searches made for an existing declaration:

- `msearch.py ... leanfinder "cofiltered category of compactifications separated finite type morphism over field"`:
  returned general affine-transition-limit results and no compactification theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Compactification.isCofiltered_of_field IsCofiltered"`:
  returned no hits (`AlgebraicGeometry.Compactification.isCofiltered_of_field` is unknown to
  Loogle's Mathlib index).
- `msearch.py ... grep "isCofiltered_of_field" /home/ubuntu/weil-src-slopmaster2/WeilConjectures`:
  found the declaration and its docstring at `CategoryBaseChange.lean:48,271--303`.
- `msearch.py ... grep "Compactification" /home/ubuntu/weil-newtargets-shared/lean/Sheaf`:
  found the existing side-project module `Sheaf.AlgebraicGeometry.CompactificationCategory`,
  but it states a different combined proposition and does not duplicate this exact upstream
  theorem.
- Direct `rg` over `WeilConjectures` and `lean/Sheaf`, plus the DAG search for
  `isCofiltered_of_field`, found no other declaration for this node.

No statement correction, new node, dependency module, or `STATEMENT-DISPUTED` issue is present.

## Second reading by NQ

I independently read the sandbox node and its `lean` record, the upstream theorem and
its definitions, and the actual blueprint source on the project server. The blueprint
file is absent from this read-only local clone; I read it over SSH at the precise
`source.document` path, together with the enclosing unit's `_section.md`. The node's
statement agrees verbatim with that source. This node cites a blueprint source, not a
Stacks tag. Its enclosing unit assumes a qcqs base and a separated finite-type map;
here the base is Y, and the field/finite-type hypotheses imply qcqs. No additional
standing hypothesis is needed.

The complete object, hypothesis, and conclusion checklist is as follows.

- Field K: `{K : Type u} [Field K]`. Pass: arbitrary field, with no characteristic
  assumption or algebraic-closure assumption.
- Finite-type K-schemes X and Y: `{X Y : Scheme.{u}}`, structure maps
  `(pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))`, and the two pairs
  `[LocallyOfFiniteType pX] [QuasiCompact pX]` and
  `[LocallyOfFiniteType pY] [QuasiCompact pY]`. Pass: finite type is exactly these
  pairs, as the collector dependency's finite-type node records and Mathlib's
  `Morphisms/FiniteType.lean` explains. The explicit-map encoding is appropriate
  for this recorded upstream API and its K-linearity equation.
- Separated finite-type K-morphism f: `(f : X ⟶ Y)`,
  `(hf : f ≫ pY = pX)`, and `[IsSeparated f]`. Pass: hf is precisely K-linearity.
  The apparent omission of finite-type instances for f is harmless, not a stronger
  theorem: from hf, the proof obtains `LocallyOfFiniteType (f ≫ pY)` and
  `QuasiCompact (f ≫ pY)`, then `locallyOfFiniteType_of_comp f pY` and
  `QuasiCompact.of_comp f pY` supply both required properties of f. Thus the
  displayed hypotheses are equivalent to the node's hypotheses.
- Objects of Comp(f): `Compactification f` from upstream `Compactification.Defs`.
  Pass: fields `Z`, `i`, `g`, `comm`, `isOpenImmersion`, and `isProper` give exactly
  an ambient scheme, the two maps, f = i ≫ g, an open immersion, and a proper map.
  No density is imposed. The ambient K-structure is the composite g ≫ pY.
  The more general definition omits quasi-compactness of i; here
  `Compactification.quasiCompact_openImmersion` derives it from finite type of f,
  so the qc-open convention of the proof dependency also agrees.
- Morphisms of Comp(f): the recorded dependency's `Compactification.Refinement`
  and `Compactification.category` in upstream `Compactification.Refinement`.
  Pass: `hom : c.Z ⟶ d.Z`, `i_hom : c.i ≫ hom = d.i`, and
  `hom_g : hom ≫ d.g = c.g` give exactly a Y-morphism respecting the open maps.
  Properness is automatic, by `Refinement.isProper`, since the source is proper
  and the target separated over Y. The category instance uses scheme identity
  and composition. No alternative category or extra morphism condition occurs.
- Nonempty category: `IsCofiltered (Compactification f)`, whose `nonempty` field
  is `Nonempty (Compactification f)`. Pass. I opened upstream
  `NagataCompactification.lean`: its construction takes separatedness, local
  finite type, quasi-compactness, and a qcqs target, and returns this same
  `Compactification f`. The field theorem derives all of those assumptions.
- Common refinement of every finite family: `IsCofilteredOrEmpty.cone_objs`,
  inherited by `IsCofiltered`, gives arrows e → c and e → d. Pass: induction
  gives every finite family, using nonemptiness for the empty family; it does not
  require a bound on the universe of a finite indexing set.
- Equalization of every pair of parallel refinements:
  `IsCofilteredOrEmpty.cone_maps` gives e and h : e → c with
  h ≫ r = h ≫ s. Pass: direction, quantifiers, and equality match the node.

I read these class fields in Mathlib `CategoryTheory/Filtered/Basic.lean:577–596`,
not just the name `IsCofiltered`. The three statement dependencies have usable
interfaces: the refinements/category declarations above; the Nagata construction;
and the convention-only collector `def-weil-scheme-morphism-properties`, which
deliberately introduces no separate declaration. The proof dependency's
`Sheaf.AlgebraicGeometry.CompactificationCategory` was also opened: it is a larger
combined proposition, not a replacement definition or an exact existing match.

Edge cases: empty X is allowed, with no nonemptiness assumption on either scheme.
Empty Y permits precisely the usual maps to the empty scheme, so no extra case is
lost. Empty finite families are covered by the nonempty field; singletons by
identity; equal parallel arrows need no extra condition. Any field characteristic
is permitted. There is no coefficient, degree n, or zero-object parameter here.
The universe u is bound globally in the upstream module, and all field and scheme
binders use it consistently with `Spec`; this imposes no independent small test
universe. Compactifications need not be a small category. No unbound variable or
universe occurs in the recorded signature.

Independent H4 searches (with different wording from the first reader):

- LeanFinder: `proper factorizations of a scheme morphism through open embeddings
  have common predecessors and equalizers`. Returned open-immersion lift,
  scheme-equalizer, gluing, and affine-limit lemmas, not this statement.
- Loogle: `"compactification"`. No hits.
- Mathlib grep: `compactification|common.refinement|cofiltered`, under
  AlgebraicGeometry. Only affine-transition-limit and etale-point cofilteredness
  hits; no compactification statement.
- LeanSearch: the category of proper factorizations of a separated finite-type
  scheme morphism with an open embedding is nonempty and cofiltered. Service
  unavailable (Internal Server Error), recorded by msearch; no verdict inferred.
- Direct rg of upstream and `lean/Sheaf` for common refinements, cofilteredness,
  and compactifications found `CategoryBaseChange.isCofiltered_of_field` and the
  general `Cofiltered`/`CommonRefinement` APIs, plus the combined side proposition.
  I opened their signatures. The existing theorem selected by the first reader
  is the exact field specialization and must be reused.

No mismatch was found, and I changed no Lean signature, mathematical statement,
dependency, or definition. No new nodes or dependency modules are needed. H5/H6
are satisfied by reusing an existing declaration, with no new data or proofs.
The upstream docstring identifies this blueprint node and states its complete
conclusion; the source proof and existing proof were read. Existing-source
docstrings and formatting were not rewritten. The second reading adds this audit
and an unshipped scratch check, compiled only through scompile.py; delivery also
checks the existing declaration through that wrapper.

Verification: scompile.py compiled `scratchpad/ExistingAudit.lean` cleanly in its
local overlay (7.0 seconds) and confirmed it against the library (8.8 seconds).
The printed theorem type has exactly the binders audited above, and `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound`. A literal comparison
also confirmed that `lean.statement` is verbatim the upstream signature, including
the final `:=`.
