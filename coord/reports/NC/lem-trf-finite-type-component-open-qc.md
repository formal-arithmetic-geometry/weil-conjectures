## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeConnectedComponent` states
`AlgebraicGeometry.finiteType_connectedComponent_open_quasiCompact` with its proof
postponed by `sorry`. There are no new notions, dependency repairs, or statement
corrections. The item JSON changes only in `lean`.

Clause-by-clause reading against the item:

- “k a field” is `{k : Type u} [Field k]`, and “C a scheme” is
  `(C : Scheme.{u})`.
- “C of finite type over k” is `[C.Over (Spec (.of k))]` together with
  `[LocallyOfFiniteType (C ↘ Spec (.of k))]` and
  `[QuasiCompact (C ↘ Spec (.of k))]`. This is exactly the conjunction
  recorded by `def-weil-finite-type-morphism`, with the project's convention
  for schemes over a field. There is no smoothness, separatedness, reduction,
  algebraic closure, or characteristic hypothesis.
- “c in C” is `(c : C)`. Mathlib's `connectedComponent c` is the maximal
  connected subset containing c, as specified by the node. It is not a
  geometric connected component or an irreducible component.
- “T is open” is `∃ U : C.Opens, (U : Set C) = connectedComponent c`.
  A bundled open subset contains precisely a set and its openness proof;
  the equality fixes its set to this particular component. The existential
  does not replace T by an arbitrary neighbourhood.
- “T is quasi-compact (every open cover has a finite subcover)” is
  `IsCompact (U : Set C)`. Mathlib's compactness definition has no Hausdorff
  requirement, so it is exactly algebraic-geometric quasi-compactness.
  Compactness in C is equivalent to compactness of the subspace U.
- “with the open subscheme structure” is the existing `U.toScheme`,
  whose structure sheaf is the restriction of that of C, with canonical
  inclusion `U.ι`. No new scheme or choice of structure sheaf is introduced.
- “nonempty connected scheme” is `ConnectedSpace U.toScheme`. The recorded
  dependency `ConnectedSpace` extends `PreconnectedSpace` with a `Nonempty`
  field; therefore this single clause includes both assertions and excludes
  the empty component, exactly as the node says.
- “of finite type over k” is the conjunction
  `LocallyOfFiniteType (U.ι ≫ (C ↘ Spec (.of k)))` and
  `QuasiCompact (U.ι ≫ (C ↘ Spec (.of k)))`.
  This is the restricted structure map, not an independently chosen morphism.

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`. Read the full class signatures and
  finite-type module docstring: finite type is their conjunction.
- `def-weil-connected-scheme`: its Mathlib match `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`, whose full signature and nonemptiness
  field were read. Also read `connectedComponent` and
  `mem_connectedComponent` in that module.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. Read its locally-ringed-space
  definition, and `Scheme.Opens.toScheme`, `Scheme.Opens.ι`, and the
  `IsOpenImmersion U.ι` instance in `Mathlib.AlgebraicGeometry.Restrict`.
  These are the canonical open-subscheme construction supplied by Mathlib.
- `Mathlib.AlgebraicGeometry.Over`, `Scheme.Over`, provides the existing
  structure-map convention. It adds data, not an extra mathematical condition.

Proof dependency imports are private. `Mathlib.AlgebraicGeometry.Noetherian`
contains the recorded finite-type/Noetherian and Noetherian-topology tools;
`Mathlib.Topology.NoetherianSpace` contains the compactness-of-subsets leaf;
`WeilConjectures.Mathlib.Topology.NoetherianSpace` contains the recorded
`TopologicalSpace.NoetherianSpace.isOpen_connectedComponent` and
`finite_connectedComponents` (their complete declarations and docstrings were
read). The remaining proof dependencies are the already imported Mathlib
scheme/finite-type/quasi-compactness modules. The declaration docstring carries
all five original proof steps, including quasi-compactness of the inclusion
checked on affine preimages, before composing finite-type morphisms.

Sources read: Stacks `more-morphisms.tex`, Tag 057K,
`lemma-local-local-structure-finite-type`, statement and proof paragraph
beginning “Let T be the connected component of Y_s containing y”. Its
Noetherian/open-component inference does not require smoothness. The current
blueprint ancestor `lem-trf-local-term-locality` and the recorded unit were
located under `literature/blueprint/latest/`; this auxiliary item is not the
unit's own statement. No blueprint route was changed.

Edge cases checked before drafting:

- C empty: there is no c, so the universally quantified statement is vacuous;
  no global nonemptiness hypothesis excludes empty schemes.
- C = Spec k: the component is the whole one-point scheme.
- A nonreduced finite-type scheme such as Spec(k[ε]/ε²): its component is
  still nonempty and the construction retains the nilpotents.
- A disjoint union of two affine lines: the selected component is one open
  affine line; the equality to `connectedComponent c` fixes the intended one.
- A line with doubled origin: separatedness is unnecessary and is not assumed.
- An arbitrary field, including positive characteristic and a field which is
  not algebraically closed, is allowed. Connectedness is ordinary connectedness.
- `u` is explicit and unrestricted; the field and scheme are in the same
  ambient scheme universe as the source category requires. There is no test
  scheme quantification or independent smaller universe.

Searches actually run (2026-10-24), using msearch.py:

- LeanFinder: “A connected component of a scheme of finite type over a field
  is open quasi compact and its open subscheme is connected nonempty and of
  finite type”. Eight hits, including `IsIntegral`, `IsArtinianScheme`, and
  `finite_irreducibleComponents_of_isNoetherian`; none gives the full result.
- Loogle: `connectedComponent, IsOpen, IsCompact`. Zero hits.
- Mathlib grep: `connectedComponent|[Cc]onnected.*[Cc]omponent`, subdirectory
  `AlgebraicGeometry`. Nine hits, in Geometrically/Connected and
  Sites/ConstantSheaf; none states this result.
- LeanSearch: “A connected component of a finite type scheme over a field is
  an open quasi compact connected finite type subscheme”. Eight hits,
  including `isOpen_connectedComponent`, `connectedComponent`, compact-open
  characterizations and `finite_irreducibleComponents_of_isNoetherian`;
  these supply separate ingredients, not this combined result.
- Direct rg over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for component/finite-type phrases,
  `connectedComponent`, and `isOpen_connectedComponent`. Read the candidate
  `WeilConjectures.AlgebraicGeometry.SmoothCurveConnectedCoproduct`: it assumes
  a separated smooth curve, so is not this general statement. Read
  `WeilConjectures.AlgebraicGeometry.NoetherianComponents`: its component
  decomposition assumes normality, also not this statement. The group-scheme
  identity-component results assume a group structure. No exact duplicate.
- Direct grep for the item id in `lean/WeilConjectures`: no matches.
- Direct rg for `finiteType_connectedComponent_open_quasiCompact` in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing declaration with that name.

Validation uses scompile.py exclusively. The initial module-mode compile found
that `QuasiCompact` was exposed only by a private transitive import; adding its
own `public import` repairs the declaration's public interface.

No statement dispute or node fault was found.

The corrected module passed scompile.py in both sandbox mode (3.5 seconds)
and library-module mode (1.5 seconds), with no errors or warnings.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
