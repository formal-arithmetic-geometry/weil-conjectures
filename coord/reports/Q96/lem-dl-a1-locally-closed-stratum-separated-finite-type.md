## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyClosedStratumSeparatedFiniteType` states
`AlgebraicGeometry.locallyClosedStratum_separated_finiteType`. Its only proof is `sorry`.
It introduces no definitions and leaves the node unchanged except for `lean`.

The underlying closed subset of the open scheme is written
`⟨U.ι ⁻¹' S, hclosed⟩`. Its canonical reduced induced closed subscheme and inclusion
are the existing `(vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subscheme` and `.subschemeι`.
In the following correspondence, `i` and `a` are explanatory names only: the Lean
statement spells out `i = (vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subschemeι` and
`a = i ≫ U.ι` without auxiliary definitions or let binders.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| A scheme T over Spec k and its structure map | `(T : Scheme.{u}) [T.Over (Spec (.of k))]`; map `T ↘ Spec (.of k)` |
| The structure map is separated | `[IsSeparated (T ↘ Spec (.of k))]` |
| The structure map is of finite type | Both `[LocallyOfFiniteType (T ↘ Spec (.of k))]` and `[QuasiCompact (T ↘ Spec (.of k))]`, exactly the recorded finite-type notion |
| A locally closed subset S of T | `(S : Set T) (hS : IsLocallyClosed S)` |
| An open subscheme U of T | `(U : T.Opens)`, whose inclusion is `U.ι` |
| U contains S | `(hSU : S ⊆ (U : Set T))` |
| S is closed in U | `(hclosed : IsClosed (U.ι ⁻¹' S))` |
| i is the reduced induced closed subscheme in U | The canonical vanishing-ideal subscheme and `.subschemeι`, as specified above |
| a is u composed with i | The actual composite `i ≫ U.ι` everywhere |
| a is an immersion | `IsImmersion (i ≫ U.ι)` |
| The image of a is S | `Set.range (i ≫ U.ι) = S` |
| The specified composite structure map is separated | `IsSeparated (i ≫ U.ι ≫ T ↘ Spec (.of k))` |
| The specified composite structure map is of finite type | `LocallyOfFiniteType (i ≫ U.ι ≫ T ↘ Spec (.of k))` and `QuasiCompact (i ≫ U.ι ≫ T ↘ Spec (.of k))` |
| If S is empty then its reduced stratum is the empty scheme | `S = ∅ → Nonempty ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subscheme ≅ Scheme.empty)` |

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated`, supplied through its
  recorded module `Mathlib.AlgebraicGeometry.Morphisms.Proper` and defined in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`. Only separatedness is assumed;
  properness and universal closedness are not hypotheses.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `def-weil-locally-closed-subset`: `IsLocallyClosed`, in
  `Mathlib.Topology.Defs.Basic` (the node's mathlib_match; no lean record is needed).
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, in
  `Mathlib.AlgebraicGeometry.OpenImmersion`; `U.ι` is the existing open-subscheme
  inclusion, so no extra open-immersion hypothesis is required.
- `lem-weil-pbc-reduced-induced-closed-subscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`, in
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`. Its full signature
  supplies the canonical vanishing ideal's reduced closed immersion, image, affine
  description, and uniqueness. The canonical data definitions are Mathlib's
  `Scheme.IdealSheafData.vanishingIdeal`, `.subscheme`, and `.subschemeι` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` and `.Subscheme`, exposed through the
  imported modules. No arbitrary closed immersion or existentially chosen scheme is used.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, and
  `AlgebraicGeometry.IsImmersion`, in `.Immersion`. The latter module's
  `IsImmersion.isImmersion_iff_exists` is precisely the closed-then-open factorization
  in the dependency's definition of immersion.

All statement dependency modules are present directly or through public imports.
The recorded proof dependencies have Mathlib matches or the already public reduced
induced module: the private imports add Noetherian schemes/rings, affine schemes,
integral morphisms, finite presentation and quasi-separated morphisms. Composition,
finite morphisms and separatedness are already supplied by the public imports.
The theorem's docstring carries the node's five-step natural-language proof and IDs.

Sources read: `literature/stacks-project/schemes.tex`, labels
`lemma-reduced-closed-subscheme`, `definition-reduced-induced-scheme`, and
`lemma-separated-permanence`; `morphisms.tex`, labels `lemma-composition-finite-type`,
`lemma-immersion-locally-finite-type`, and `lemma-finite-type-noetherian`;
`properties.tex`, label `lemma-immersion-into-noetherian`. These give the construction,
separated composition, finite-type composition, and the essential quasi-compactness
of the arbitrary open. I also read the current blueprint's
`sec-deligne-laumon-a1/sk-p-dl-a1-exact/p-dl-a1-exact.proof.md`.

Edge cases checked mathematically before drafting:

- `S = ∅`, including `U = ∅` and an empty ambient scheme: the image is empty, and
  the subscheme has empty underlying space, hence is isomorphic to `Scheme.empty`.
  No nonemptiness instance is required anywhere.
- `S = Set.univ`, `U = ⊤`: the construction is the ambient reduction, not the
  ambient scheme itself when it has nilpotents.
- An arbitrary nonreduced T is allowed; reducedness belongs to the constructed
  stratum and is not imposed on T.
- U is arbitrary, with no additional compactness hypothesis. Finite type over a
  field makes T Noetherian, and the existing open-immersion quasi-compactness
  instance supplies the property needed in the eventual proof.
- A general field in any characteristic is allowed. There is no algebraic-closure,
  perfection, connectedness, affine, or dimension hypothesis.

Searches performed through `batch2/msearch.py` (2026-10-24):

- LeanFinder, query: "A reduced locally closed subscheme of a separated finite type
  scheme over a field is separated of finite type with the specified image and empty
  when the subset is empty". Eight hits: generic separated/reduced schemes,
  quasi-affine separatedness, reduction of opens, and a finite-type criterion over
  a Jacobson target. No exact theorem with all of this node's clauses.
- Loogle, query: `AlgebraicGeometry.IsImmersion, AlgebraicGeometry.IsSeparated`.
  Zero hits.
- Grep, query: `vanishingIdeal|reduced.*[Ii]nduced|stratum`, subdirectory
  `AlgebraicGeometry`. Twenty-five displayed hits, including
  `Scheme.IdealSheafData.vanishingIdeal`, ideal-sheaf functoriality and affine
  transition limits. Reused the existing vanishing-ideal construction.
- LeanSearch, query: "A locally closed subscheme of a separated finite type scheme
  over a field is separated and finite type". Eight hits: properness equivalences,
  scheme separatedness, restriction of separated maps, and local finite type of
  closed immersions. No exact all-clause theorem.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `locally.closed.*finite.type|stratum.*[Ff]inite|vanishingIdeal.*subschemeι`, followed
  by the narrower `locally.closed.*finite.type|stratum.*separated|stratum.*finite.type`:
  found uses of the canonical subscheme and stratification results, but no statement
  matching this item. The source's `NoetherianApproximation` finite-type result
  concerns constructible subsets of affine spectra, a different statement.
- The prescribed item-ID search in `lean/WeilConjectures` returned no hits.
  Exact proposed-name searches in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` returned no hits.

No disputed statement, new node, dependency repair, or statement correction.

Validation: `scompile.py Q96 lem-dl-a1-locally-closed-stratum-separated-finite-type`
compiled the file in sandbox and library module modes on the server, with no
errors or warnings (1.5 s and 2.4 s respectively). Every universe and parameter
is explicitly bound; autoImplicit and relaxedAutoImplicit are disabled. The
maximum source line width is 93 characters.

## Second reading by Q96

Author's second reading, with the original node and final Lean file open; the
maintainer supplies the independent review for this dispatcher assignment.
I matched every assumption and conclusion in the table above. In particular,
finite type has BOTH components, the map in all three geometric-property
conclusions is the specified composite, and the image equality is in T rather
than in U. The closed subset used in the construction is the inverse image of S
in U, not S treated as a closed subset of T. The subset-containment hypothesis
therefore recovers the whole S in the image equality. The empty clause asserts an
isomorphism of schemes, not an equality of implementation-specific objects.
The canonical construction is exactly the dependency's reduced induced closed
subscheme, so no reducedness hypothesis or weaker surrogate object was added.
No mathematical mismatch was found. Before final validation I moved the
`open Scheme.IdealSheafData` command inside `namespace AlgebraicGeometry` to
resolve that namespace correctly; the final module compiled cleanly.
