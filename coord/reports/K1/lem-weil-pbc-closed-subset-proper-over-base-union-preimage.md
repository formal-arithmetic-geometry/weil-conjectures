## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ClosedSubsetProperOverBaseUnionPreimage.lean` states
`AlgebraicGeometry.Scheme.isClosedSubsetProperOver_union_preimage`. It imports the existing
`Scheme.IsClosedSubsetProperOver` definition from
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`.

The first conjunct renders clause (1): for every natural number `n`, every family
`Z : Fin n → TopologicalSpace.Closeds X`, and every `i`, the hypothesis
`IsClosedSubsetProperOver sX (Z i)` is required; the conclusion is
`IsClosedSubsetProperOver sX (⨆ i, Z i)`, the finite union (including `n = 0`).
The second conjunct renders clause (2): `sX : X ⟶ S` is locally of finite type; `f : X ⟶ Y`
is proper; `sY : Y ⟶ S` is locally of finite type; and `f ≫ sY = sX`. For every closed
`Z : TopologicalSpace.Closeds Y` proper over `S` via `sY`, the conclusion is properness over
`S` via `sX` of the closed preimage `Z.preimage (f := f.base) f.continuous`.

Dependency declarations used: `Scheme.IsClosedSubsetProperOver` from
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`; `LocallyOfFiniteType` from
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`.

Edge cases checked: the `Fin 0` family gives the bottom closed set (empty union), and the
preimage uses the continuous underlying map `f.base` supplied by `f.continuous`. The module
compiled cleanly with the expected `sorry` warning.

Searches made: `msearch.py ... leanfinder "finite union closed subsets proper over base preimage proper morphism"`
returned only generic properness and finite-preimage declarations, with no closed-subset notion;
`msearch.py ... loogle "TopologicalSpace.Closeds preimage IsProper"` returned no hits;
`msearch.py ... grep "IsClosedSubsetProperOver|proper over base" AlgebraicGeometry` returned no
additional declaration. Repository `rg` searches found only the existing definition module and no
matching theorem in the source checkout.

## Second reading by K1

Read independently against the sandbox node, all three statement-dependency nodes,
their recorded declarations, and the complete delivered module. Verdict: exact statement;
no mathematical, signature, or docstring repair needed. This reading adds only this report.

Source check: the local `literature/stacks-project/coherent.tex` is absent on this machine.
Read the upstream [Stacks coherent.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex),
labels `section-proper-over-base`, `lemma-closed-proper-over-base`,
`definition-proper-over-base`, `lemma-functoriality-closed-proper-over-base` (3), and
`lemma-union-closed-proper-over-base`, with their proofs. The section imposes no general
Noetherian, separated-base, field, or characteristic assumption. The locally-of-finite-type
requirements belong to the definition and the two lemmas and are present in Lean.

Object, hypothesis, and conclusion checklist (each verdict: matches):

1. Arbitrary base scheme S and scheme X: `{X S : Scheme.{u}}`.
2. Structure morphism X to S: `(sX : X ⟶ S)`.
3. X locally of finite type over S: `[LocallyOfFiniteType sX]`.
4. A finite list of closed subsets of X: `∀ (n : ℕ)
   (Z : Fin n → TopologicalSpace.Closeds X)`. Its elements are closed by their type;
   `Fin n` enumerates precisely n subsets and permits repeats.
5. Each member proper over S: `(∀ i, IsClosedSubsetProperOver sX (Z i))`.
6. Clause (1), their union proper over S: `IsClosedSubsetProperOver sX (⨆ i, Z i)`.
   Opened Mathlib `Topology/Sets/Closeds.lean`: `coe_sSup` gives closure of the union,
   `coe_sup` gives binary union, and `coe_bot` gives the empty set. For `Fin n`, the
   union is already closed (`isClosed_iUnion_of_finite`, `Topology/Basic.lean:191`),
   so this supremum is exactly the finite set union, with no stronger conclusion.
7. Clause (2), another S-scheme and its structure map:
   `∀ {Y : Scheme.{u}} ... (sY : Y ⟶ S)`.
8. Y locally of finite type over S: `[LocallyOfFiniteType sY]`.
9. Proper morphism X to Y: `(f : X ⟶ Y) ... [IsProper f]`.
10. Morphism over S: `f ≫ sY = sX →`. The composition order is the categorical
    notation for sY composed with f. This expresses the S-morphism in the source.
11. Closed subset of Y, proper over S: `∀ (Z : TopologicalSpace.Closeds Y),
    IsClosedSubsetProperOver sY Z →`.
12. Clause (2), closed inverse image proper over S:
    `IsClosedSubsetProperOver sX (Z.preimage (f := f.base) f.continuous)`.
    Opened `Closeds.preimage`: its carrier is exactly `f.base ⁻¹' Z`; continuity
    supplies closedness. No extra assumption on closedness of the inverse image.
13. Both clauses asserted: the outer conjunction. Sharing X, S and sX between
    clauses is equivalent to the node's two universally quantified assertions.

Dependency audit: opened `ClosedSubsetProperOverBase.lean`, where
`Scheme.IsClosedSubsetProperOver f Z` is exactly
`IsProper ((IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)`.
Opened `ReducedInducedClosedSubscheme.lean`: its recorded theorem specifies this same
vanishing-ideal subscheme as reduced, with image Z and uniqueness over X. Opened
Mathlib's actual `vanishingIdeal` and the subscheme-immersion declaration; the data
are constructed rather than supplied by sorry. The named characterization theorem is
postponed, as allowed. Opened `Morphisms/FiniteType.lean:43` and `Proper.lean:42`:
`LocallyOfFiniteType` is the affine ring-map condition recorded by its node, and
`IsProper` extends separatedness, universal closedness and local finite type.
Universal closedness supplies quasi-compactness, so properness agrees with its DAG
node's finite-type definition. The sole import supplies all these declarations.
No missing notion, private copy, new definition node or dependency module is needed.

Edge cases: `n = 0` has the unique empty family and bottom supremum; its hypothesis
is vacuous and its conclusion asserts properness of the empty closed subset.
`n = 1` and repeated subsets are included. X, Y, S and Z may be empty; no nonempty
binder excludes these. The empty reduced subscheme is cut out by the unit ideal
(Mathlib `vanishingIdeal_bot`). There is no module zero object in this statement.
No field or characteristic restriction is present. `u` is declared and arbitrary,
and all schemes lie in the shared scheme category used by the dependency; no finite
index family needs an independent index universe. Every variable is bound explicitly.

Independent H4 searches, recorded in `searches.jsonl`:

- LeanFinder: `scheme reduced closed subscheme finite union inverse image proper support`.
  Eight hits on ideal-sheaf supports and zero loci; no matching properness theorem.
- Loogle: `"IsProper", "union"`. Four hits about proper semilinear sets, a different notion.
- Mathlib grep: `IsClosedSubsetProperOver|reduced.*proper|proper.*preimage`
  in AlgebraicGeometry. Only geometric integrality and compact-preimage results;
  no matching theorem.
- LeanSearch: `Finite union of closed subsets with proper reduced induced subschemes
  over a base, and inverse image under a proper scheme morphism`.
  Service unavailable (Internal Server Error); no successful-search verdict claimed.
- Direct `rg` over source `WeilConjectures`, project `lean/Sheaf`, and Mathlib
  AlgebraicGeometry using `properOver`, `proper over`, `closed.*union`,
  `preimage.*proper`, and `IsClosedSubsetProperOver`. The existing project definition
  and its universally-closed-image sibling are relevant but neither states this item;
  upstream uses concern proper schemes, graph images or unrelated supports.
  Checked the proposed full name and predicate in `dag/lean_names_upstream.json`
  and the upstream source: no collision or existing exact declaration.

H5/H6/H8/H9: no definition is delivered; the sole theorem proof is `by sorry`.
The module and declaration docstrings name both source tags and this blueprint id;
the declaration's seven numbered proof steps match the node's seven steps, including
empty union, finite coproduct, image, scheme-theoretic preimage, its point-set image,
and composition to the base. Namespace, header, sole used import and line lengths
meet the conventions. No file-local notation, instance, let binder or hidden data.
The node has no statement correction; no corrected citer audit is applicable.
The node's `lean.statement` equals the file's signature verbatim before `:=`.

Validation: `scompile.py K1 lem-weil-pbc-closed-subset-proper-over-base-union-preimage`
with the full sandbox module path compiled on the server in 1.7 seconds, exit 0,
without errors or warnings. No mismatches found; Lean and node left unchanged.
