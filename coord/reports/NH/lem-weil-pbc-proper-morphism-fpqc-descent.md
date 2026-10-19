## Worker report

The module `Sheaf.AlgebraicGeometry.ProperMorphismFpqcDescent` states
`AlgebraicGeometry.isProper_of_fpqc_cover`, with `sorry` as its entire proof. No
new notions, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`, using `def-pc-scheme`.
- The arbitrary morphism f: `(f : X ⟶ S)`.
- The index set I and the schemes S_i: `{I : Type v}` and `(S' : I → Scheme.{u})`.
  The index universe is independent of the scheme universe; no size or finiteness
  restriction on the family is imposed.
- The arrows g_i: `(g : ∀ i, S' i ⟶ S)`.
- The fpqc covering hypothesis:
  `(hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)`.
  This is precisely the covering predicate recorded by `def-weil-pbc-fpqc-covering`:
  flat, jointly surjective and quasi-compact as a family. It does not require the
  individual covering morphisms to be quasi-compact.
- The definition of f_i as the second projection from X ×_S S_i is rendered directly
  by `pullback.snd f (g i)`, rather than introducing additional quantified data.
- Every f_i proper: `(h : ∀ i, IsProper (pullback.snd f (g i)))`.
- The sole conclusion, f proper: `IsProper f`.

The source `literature/stacks-project/descent.tex`, label
`lemma-descending-property-proper` (Tag 02L1), says properness is fpqc local on the
base; its descent direction is exactly this node. Its proof combines universal
closedness, separatedness and finite type. The module docstring gives the node's
six-step proof, including the identification of the diagonal base changes over
the base-changed diagonal target.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (schemes and arrows).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `AlgebraicGeometry.Scheme.fpqcPrecoverage` (the covering hypothesis).
  Its quasi-compact-cover condition agrees with the affine-open formulation:
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact` refines compact opens by
  finitely many affine opens, including the empty finite family.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `CategoryTheory.Limits.pullback.snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
  Mathlib uses separatedness, universal closedness and local finite type; its
  instance `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed` supplies
  quasi-compactness, so this agrees with the node's finite-type formulation.

The following proof-dependency modules are imported without `public`:
`Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover`
(`AlgebraicGeometry.universallyClosed_of_fpqc_cover`),
`Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`
(`AlgebraicGeometry.locallyOfFiniteType_of_fpqcCover`),
`Sheaf.AlgebraicGeometry.OverPullbackDiagonalClosedImmersion`
(`AlgebraicGeometry.isClosedImmersion_overPullback_diagonal_iff`), and
`Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent`
(`AlgebraicGeometry.isClosedImmersion_of_fpqc_cover`). Their signatures and
source docstrings were read. The Mathlib proof dependencies are imported via
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`, and
`Mathlib.CategoryTheory.Sites.Precoverage` (in particular
`CategoryTheory.Precoverage.mem_coverings_of_isPullback`).

Edge cases checked: an empty index type is allowed; the fpqc hypothesis then
forces the base to be empty, and a scheme mapping to an empty base is empty, so
the properness conclusion is valid. Empty source schemes and empty components
are allowed. A singleton cover gives the usual fpqc descent assertion. No
Noetherian, separated-base, affine-base, finite-family, or individual
quasi-compactness assumption was added. All universes and variables are bound.
No mathematical fault or disputed statement was found.

Searches (via `msearch.py`, plus direct source inspection):

- LeanFinder: `Proper morphisms descend along fpqc covering families` returned
  generic descent criteria, quasi-compact-cover lemmas, flat-descent results,
  and Zariski locality of properness; no exact proper covering-family theorem.
- Loogle: `AlgebraicGeometry.IsProper` returned the definition, its projections,
  base-change stability, composition and locality results; no exact match.
- LeanSearch: `Proper morphisms descend along fpqc covering families` was
  unavailable (`Internal Server Error`); the other searches were used.
- Mathlib grep: `IsProper.*descend|descend.*IsProper`, under AlgebraicGeometry,
  returned no hits. A broader direct search for proper/descendsAlong found
  general descent tools, not this statement.
- Direct `rg` over `WeilConjectures` and `lean/Sheaf` for
  `proper.*fpqc|[Ii]sProper.*[Cc]over|[Ii]sProper.*descend|descend.*[Ii]sProper`
  and the item id found generic fpqc descent machinery and a citation of this
  node, but no existing declaration of its statement. The upstream module
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` was read: its generic
  lemmas take a morphism property with descent/locality assumptions and are not
  this properness statement.
- The proposed name `isProper_of_fpqc_cover` was checked in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Validation: compilation uses only the prescribed server `scompile.py`; the
required delivery dry run is run with `--no-push`. The independent second reading
is reserved for the next worker.

## Second reading by NH

I independently read the item node, its four statement-dependency nodes and their
recorded declarations, the four imported project proof-dependency modules, and
Stacks `descent.tex`, `lemma-descending-property-proper` (02L1). The source's
`definition-property-morphisms-local` quantifies over arbitrary covering families
and arbitrary morphisms over a base; it imposes no Noetherian or compactness
assumption. Properness is an absolute morphism property, so the ambient base
introduces no additional hypothesis here. I also read `topologies.tex`,
`definition-fpqc-covering` (022B), including its allowance of n = 0.

Object, hypothesis and conclusion checklist, in the node's order:

- X and S are arbitrary schemes: `{X S : Scheme.{u}}`. PASS. The recorded
  `AlgebraicGeometry.Scheme` is a locally ringed space locally isomorphic to an
  affine spectrum; its `Scheme.Hom` supplies exactly the scheme morphisms.
- The morphism f from X to S: `(f : X ⟶ S)`. PASS; there are no property instances
  on f or on either scheme in the signature.
- The set I and schemes S_i: `{I : Type v}` and `(S' : I → Scheme.{u})`. PASS.
  The independently quantified index universe permits arbitrary covering families;
  there is no nonemptiness, smallness relative to u, or finite-family restriction.
  A common arbitrary scheme universe u allows all the schemes in any given
  set-indexed family to be placed in a sufficiently large universe.
- The covering arrows: `(g : ∀ i, S' i ⟶ S)`. PASS, with exactly the common target S.
- The fpqc covering condition: `hg : Presieve.ofArrows S' g ∈
  Scheme.fpqcPrecoverage S`. PASS. I opened `fpqcPrecoverage`,
  `propQCPrecoverage`, and `QuasiCompactCover`, as well as
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact`. These give flat arrows
  and finite affine-open image coverings of each affine open of S, exactly as the
  node requires. The predicate does not demand that each g_i be quasi-compact.
  Passing through the presieve loses only repeated identical arrows, which
  affects neither flatness nor the finite-image-cover condition.
- f_i is the second projection X ×_S S_i → S_i:
  `pullback.snd f (g i)`. PASS. I opened `pullback` and `pullback.snd`; the latter
  targets the second source of the cospan, namely S' i. Scheme pullbacks exist
  without any further hypothesis; no independent replacement for f_i is chosen.
- Every f_i is proper: `h : ∀ i, IsProper (pullback.snd f (g i))`. PASS. I read
  Mathlib's `IsProper`, `IsSeparated`, and `UniversallyClosed` declarations and
  the instance `UniversallyClosed → QuasiCompact`. Thus Mathlib's local finite
  type clause plus universal closedness gives exactly the node's finite type
  clause, including quasi-compactness. No additional hypothesis is hidden here.
- Conclusion f is proper: `IsProper f`. PASS, using the same definition as in h;
  no extra conjunct or conclusion, and the quantifier order is unchanged.

The imported universal-closedness and locally-finite-type descent declarations
have the same arbitrary-family covering predicate and second projections. The
closed-immersion descent theorem has that same family form too. The diagonal
lemma takes arbitrary `X Y : Over S` and identifies the closed-immersion property
of the pulled-back diagonal with separatedness of the pulled-back morphism;
its target uses the second projection's structure map, as its node specifies.
These are usable dependencies, with no finiteness assumptions. The remaining
proof leaves are Mathlib's universal-closedness/quasi-compactness instance and
precoverage base-change stability. No new definition nodes or dependency modules
are present or needed, and there is no statement correction to audit.

Edge cases: I may be empty; then the fpqc hypothesis forces S empty, and a scheme
mapping to it is empty, so the conclusion holds. Empty X, empty components,
repeated components, and singleton covers are all permitted. In particular n = 0
in the affine-cover condition is preserved. There are no integer degrees, field
characteristics, or nonzero-ring restrictions. Universes u and v and every
variable in the signature are explicitly bound. The independent v is appropriate
for a covering family, rather than an indexing category for a limit.

Independent searches used different wording from the first reader:

- LeanFinder via `msearch.py`: `Faithfully flat descent of properness for families
  of scheme morphisms` returned eight generic or other-property descent results,
  including universal closedness, but no properness covering-family theorem.
- Loogle via `msearch.py`: `AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat`
  returned zero hits.
- LeanSearch via `msearch.py`: `Descent of proper scheme morphisms along
  faithfully flat covering families` was unavailable (Internal Server Error).
- Direct `rg` in Mathlib algebraic geometry, upstream `WeilConjectures`, and
  project `lean/Sheaf` searched proper/fpqc and proper/descent combinations,
  `isProper_of_fpqc_cover`, and the proposed declaration name in the upstream
  name index. No duplicate declaration was found. I opened upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`: its general descent
  declarations require an independently supplied `P.DescendsAlong` instance;
  they do not state this properness result. The project's field-extension
  properness descent and closed-proper-support locality are special cases or
  applications, not exact matches.

No mismatch was found. I left the Lean and node unchanged and added this review.
The module has one theorem with entire proof `sorry`, no definitions or private
notation, both required source/blueprint docstrings, and all six node proof steps
in its theorem docstring. The node's `lean.statement` is verbatim the theorem
signature. Server `scompile.py` compiled the delivered module cleanly in 1.2 s,
with nice 19, two threads and the prescribed 60-second per-file limit.
