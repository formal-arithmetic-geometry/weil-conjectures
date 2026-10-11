## Worker report

The module `Sheaf.RingTheory.RegularLocalFiniteGlobalDimension` states
`IsRegularLocalRing.hasGlobalDimensionLE_of_ringKrullDim_eq`, with a `sorry` proof.
No definitions or additional nodes are needed, and no node correction is made.

Hypothesis and clause correspondence:
- The commutative ring R is `(R : Type u) [CommRing R]`.
- “Regular local ring (R,m)” is `[IsRegularLocalRing R]`, the recorded ring clause
  of `def-weil-regular-scheme`. This class includes locality and Noetherianity;
  its maximal ideal is Mathlib's `IsLocalRing.maximalIdeal R`. No separate chosen
  maximal ideal or Noetherian hypothesis is needed.
- “Of Krull dimension d” is `(d : ℕ)` and
  `(hd : ringKrullDim R = (d : WithBot ℕ∞))`. The cast uses exactly the extended
  dimension codomain; it does not replace dimension by a truncation.
- “Global dimension at most d: every R-module has a projective resolution of
  length ≤ d” is `Ring.HasGlobalDimensionLE.{u, max u v} R d`. Its definition
  quantifies over every `M : ModuleCat.{max u v} R`, with no finite-generation
  condition, and asserts `ModuleCat.HasProjectiveResolutionLE M d`. That is an
  exact augmented projective resolution whose terms above d are zero.
- “Finite global dimension” is included in the bound with the natural witness d:
  `Ring.HasFiniteGlobalDimension` is `∃ n, Ring.HasGlobalDimensionLE R n`.
  This redundant consequence is not separately conjoined to the conclusion.

Dependency declarations read and used:
- `Mathlib.RingTheory.RegularLocalRing.Defs`, `IsRegularLocalRing`, with its
  docstring and full class signature; the dependency's `lean.declarations` and
  `mathlib_match` explicitly record this ring notion. The main `IsRegularRing`
  declaration is for a different clause and is not used here.
- `Sheaf.RingTheory.GlobalDimension`, `Ring.HasGlobalDimensionLE`, reading its
  complete definition and docstring, and its underlying
  `ModuleCat.HasProjectiveResolutionLE`. Also read `Ring.HasFiniteGlobalDimension`
  to check the finite-global-dimension clause.

Source checked: the local `literature/stacks-project/algebra.tex` is absent on
this machine, so opened https://stacks.math.columbia.edu/tag/00O7. Proposition
00O7 explicitly states the dimension bound for regular local rings. Its proof
uses 00NT and 00NG for finite modules and then 065T for all modules. The declaration
has all five steps of the node's proof in its docstring, including the zero
module and padding argument.

Edge cases checked before writing:
- d = 0: the claim is a resolution concentrated in degree zero, meaning every
  module over a dimension-zero regular local ring (a field) is projective.
- M = 0: the zero resolution meets the bound, including d = 0.
- Arbitrary, possibly infinitely generated modules are included; no finiteness
  hypothesis was added. The universe `max u v` includes the ring's universe and
  can grow arbitrarily, avoiding vacuous small-module testing.
- The zero ring is excluded by the regular-local hypothesis itself, as in the
  source's local-ring convention; no extra exclusion was added. All
  characteristics and all finite natural dimensions are included.

Searches for an existing statement (2026-10-11):
- `msearch.py ... leanfinder "regular local ring of Krull dimension d every module
  has a projective resolution of length at most d"`: 8 hits, the general
  CategoryTheory projective-dimension API only; no regular-local dimension bound.
- `msearch.py ... loogle "IsRegularLocalRing,
  CategoryTheory.HasProjectiveDimensionLE"`: OK, zero hits.
- `msearch.py ... grep "IsRegularLocalRing|globalDimension|GlobalDimension"
  RingTheory/Regular`: OK, zero hits.
- `rg` in the source `WeilConjectures` for `IsRegularLocalRing`,
  `FiniteGlobalDimension`, and projective-dimension declarations: found
  `IsRegularLocalRing.exists_hasProjectiveDimensionLE` in
  `WeilConjectures/Mathlib/RingTheory/Regular/ProjectiveDimension.lean`.
  Read its complete signature and docstring: it requires `Module.Finite R M`
  and concludes existence of an unspecified bound, using Ext-defined projective
  dimension. It is not this node's uniform bound for all modules.
- `grep -rn "lem-weil-pbc-regular-local-finite-gl-dim"` in the source
  `WeilConjectures`: zero hits.
- `rg` in `lean/Sheaf` for the same ring/global-dimension notions found the shared
  definition, the converse RegularLocalOfFiniteGlobalDimension theorem, and the
  Ext-vanishing sibling; none state this theorem.
- `rg` for the proposed full theorem basename in Mathlib, the source project,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: zero hits.

No STATEMENT-DISPUTED issue or dependency fault found. The module introduces
only the named theorem, leaving its proof to stage 3.

## Second reading by G1

Read the sandbox node and module independently, both statement dependency nodes,
their recorded declarations and docstrings, and the underlying Mathlib
`ProjectiveResolution` and ModuleCat projectivity equivalence. No new definition
nodes, dependency modules, or statement correction are present or needed.

Source: fetched Stacks `algebra.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex into
the sandbox as `algebra-source.tex`, and read lines 26913–26938 (the section
introduction and `proposition-regular-finite-gl-dim`). Also read definitions
`definition-finite-proj-dim` (26569) and `definition-finite-gl-dim` (26785).
The section imposes no further standing hypotheses. Checked the tagged pages
https://stacks.math.columbia.edu/tag/00O7 and
https://stacks.math.columbia.edu/tag/00KU against these notions.

Object, hypothesis, and conclusion list, with the Lean rendering and verdict:

1. Object: the commutative ring `R`. Rendering: `(R : Type u) [CommRing R]`.
   Exact: no field, algebra structure, or characteristic assumption is added.
2. Object: its maximal ideal `m`, with `R` local. Rendering:
   `[IsRegularLocalRing R]` extends `IsLocalRing R`, whose maximal ideal is
   `IsLocalRing.maximalIdeal R`. Exact: the node names the unique maximal ideal,
   without choosing additional data or quantifying over arbitrary ideals.
3. Hypothesis: `R` is regular local, including Noetherianity and generation of
   its maximal ideal by dimension-many elements. Rendering:
   `[IsRegularLocalRing R]`, from the recorded `def-weil-regular-scheme` ring
   clause in `Mathlib.RingTheory.RegularLocalRing.Defs`. Its class extends
   `IsLocalRing R` and `IsNoetherianRing R`, with
   `(maximalIdeal R).spanFinrank = ringKrullDim R`. Exact: the equality describes
   the minimal number of generators; the dependency's documented Krull-height
   inequality equates this with generation by dimension-many elements. The
   recorded `IsRegularRing` main declaration is not substituted for this clause.
4. Object and hypothesis: finite Krull dimension `d`. Rendering: `(d : ℕ)` and
   `(hd : ringKrullDim R = (d : WithBot ℕ∞))`. Exact: an equality in Mathlib's
   actual dimension codomain, without truncation or extra positivity assumption.
5. Conclusion: every `R`-module has a projective resolution of length at most
   `d`. Rendering: `Ring.HasGlobalDimensionLE.{u, max u v} R d`. Exact: the
   recorded definition in `Sheaf.RingTheory.GlobalDimension` expands to
   `∀ M : ModuleCat.{max u v} R, ModuleCat.HasProjectiveResolutionLE M d`;
   no `Module.Finite` restriction occurs. The latter definition existentially
   quantifies a `ProjectiveResolution M` and requires `IsZero` in degrees above
   `d`. Mathlib's structure has projective terms and a quasi-isomorphism to
   `single₀ M`, giving the exact augmented sequence. The imported ModuleCat
   projectivity equivalence identifies categorical projectivity with
   `Module.Projective R M`. Thus neither exactness nor the terminal injection
   at degree `d` is omitted.
6. Conclusion: finite global dimension, at most `d`. Rendering: the same bound,
   with natural witness `d` for the existing
   `Ring.HasFiniteGlobalDimension := ∃ n, Ring.HasGlobalDimensionLE R n`.
   Exact: the finite clause follows definitionally from the bound; a separate
   conjunction would repeat the same content. Quantifier order is ring and its
   regular-local structure, dimension and its equality, then every module and
   existence of its resolution; the resolution may depend on the module.

Edge cases: `d = 0` is included and means all modules are projective, as over a
dimension-zero regular local ring. The zero module is included, with the zero
resolution, and no nonzero-module hypothesis leaks from the natural-language
proof into the statement. The zero ring is excluded by Mathlib's `IsLocalRing`
extending `Nontrivial`, matching the source's local-ring convention. All
characteristics are covered. `u` and `v` are explicitly bound; `max u v` includes
the ring universe and arbitrarily large module universes, and modules in smaller
universes can be lifted. There is no index-set or scheme object here, so empty
index sets and empty schemes impose no additional case.

Independent searches, using different wording from the first reader:

- `msearch.py ... leansearch "Noetherian local ring whose maximal ideal has
  dimension many generators has projective resolutions uniformly bounded by
  Krull dimension"`: service unavailable (Internal Server Error); recorded as
  unavailable, with no negative verdict inferred.
- `msearch.py ... leanfinder "Auslander Buchsbaum Serre regular local rings global
  homological dimension equals Krull dimension"`: eight Krull/support-dimension
  and regular-sequence hits; none states the uniform projective-resolution bound.
- `msearch.py ... grep "regular.*(dimension|resolution)|global.*dimension|
  homological.*dimension" RingTheory/Regular`: zero hits.
- Direct `rg` over source `WeilConjectures`, project `lean/Sheaf/RingTheory`, and
  `dag/lean_names_upstream.json` for `hasGlobalDimensionLE`, `HasGlobalDimensionLE`,
  `exists_hasProjectiveDimensionLE`, `regular.*resolution`, and
  `global.*dimension`: only shared definitions, testing/localization/converse
  siblings, and the upstream finite-module theorem. Opened the upstream
  `IsRegularLocalRing.exists_hasProjectiveDimensionLE` (lines 198–202 of
  `WeilConjectures/Mathlib/RingTheory/Regular/ProjectiveDimension.lean`): it assumes
  `[Module.Finite R M]` and supplies an unspecified `∃ n`, using Ext projective
  dimension. It is not this uniform bound for every module. No duplicate found.

No mismatch was found and no Lean or node field was changed. The module has one
theorem, with only `sorry` as proof and no hollow definitions. Both imports are
used. Header, namespace, explicit universes, line lengths and source/blueprint
docstrings conform. The theorem docstring carries each of the node's five proof
steps, including the depth argument, terminal MCM module, its freeness, zero
module and padding, and passage from finite to all modules via 065T. The node's
`lean.statement` agrees verbatim with the file signature.

Validation: `scompile.py G1 lem-weil-pbc-regular-local-finite-gl-dim` on the
delivered module compiled on the server in 1.6 seconds, exit 0, with no warnings.
