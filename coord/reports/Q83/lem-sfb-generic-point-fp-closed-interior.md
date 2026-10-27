## Worker report

The module `Sheaf.AlgebraicGeometry.GenericPointFpClosedInterior` states
`AlgebraicGeometry.IsClosedImmersion.exists_open_subset_range_of_isGenericPoint`.
Its only proof is `sorry`, as required for stage 2. It introduces no definitions.
The node is unchanged except for its `lean` record.

The source was read locally: `literature/stacks-project/properties.tex`, the full
lemma and proof labelled `lemma-generic-point-in-constructible` (Tag 0AAW), and
`literature/stacks-project/more-groupoids.tex`, the lemma and proof labelled
`lemma-finite-flat-over-almost-dense-subscheme-addendum` (Tag 0ABB). The latter
uses locally constructible images of finitely presented closed strata and 0AAW
to obtain neighborhoods contained in those strata as underlying sets.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| A scheme X, a closed subscheme Z and its inclusion i | `{X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)` |
| i is a closed immersion | `[AlgebraicGeometry.IsClosedImmersion i]` |
| i has finite presentation in the conventions of Stacks 01TP | `[AlgebraicGeometry.LocallyOfFinitePresentation i] [AlgebraicGeometry.QuasiCompact i] [AlgebraicGeometry.QuasiSeparated i]` |
| An irreducible component of X | `{C : Set X} (hC : C ∈ irreducibleComponents X)` |
| ξ is its generic point | `{ξ : X} (hξ : IsGenericPoint ξ C)` |
| ξ belongs to the underlying image of i | `(hξi : ξ ∈ Set.range i)` |
| There exists an open subscheme N of X | `∃ N : X.Opens` |
| ξ belongs to N | `ξ ∈ N` |
| The underlying set of N is contained in the image | `(N : Set X) ⊆ Set.range i` |

`X.Opens` is Mathlib's `TopologicalSpace.Opens X`; each such open has its
canonical open subscheme `N.toScheme` and open immersion `N.ι`, defined in
Mathlib's `AlgebraicGeometry/Restrict.lean`. Thus the existential is precisely an
open subscheme, with no extra scheme map to choose. The range uses the existing
coercion of `Scheme.Hom` to its underlying function. No factorization through Z
occurs in the conclusion. There is no reducedness, Noetherian, compactness or
quasi-separatedness assumption on X. The two latter morphism instances on i
spell out the finite-presentation convention; they do not assert anything of
this kind about X.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`, and `Scheme.Opens`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-scheme-conventions` is explicitly a convention record, with no
  declaration of its own. Its finite-presentation clause is rendered by
  `AlgebraicGeometry.LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, and `QuasiSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (the latter two are public
  dependencies of the finite-presentation module). Their source signatures and
  docstrings were read.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, whose body
  is `closure ({ξ} : Set X) = C`.
- `def-weil-irreducible-components`: the mathlib_match is
  `Mathlib.Topology.Irreducible`, `irreducibleComponents`, defined as the maximal
  irreducible subsets. This is a Mathlib leaf and needs no new lean record.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the canonical restriction of an open is
  the standard open subscheme represented by `X.Opens`.

The public imports are the statement dependencies. Plain proof imports retain
`Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.Properties`, `Mathlib.Topology.Constructible`,
`Mathlib.Topology.Spectral.Basic`, and
`WeilConjectures.Topology.ProconstructibleClosureSpecialization`. The last
provides the recorded `Topology.exists_mem_iInter_closure_singleton`. The
finite-presentation public import also provides the affine-opens finite
presentation lemma and `Scheme.Hom.isConstructible_image` (Chevalley); the
other imports provide the recorded affine qcqs, spectral-space and
constructible-subset interfaces. No dependency repair is needed.

The theorem docstring follows every step of the node's proof: affine reduction
and verification of Chevalley's hypotheses, constructibility and complementation,
uniqueness of a generalization of a component generic point using maximality
and sobriety, the singleton-family application of Tag 0903(1), and the open
complement of the closure. It names each DAG input.

Edge cases checked before writing:

- Empty X: there is no ξ or irreducible component, so the hypotheses are
  uninhabited. Empty Z: membership in `Set.range i` is impossible.
- Identity immersion: N may be the whole X.
- Nilpotent thickening, for example the reduced point in Spec of the dual
  numbers: the image is the whole space, so N can be the whole scheme as an
  open, even though its inclusion into X need not factor through Z.
- Reducible X: the two axes give a neighborhood of a chosen component generic
  point inside that component (a principal open avoiding their intersection).
  The statement does not assume X irreducible.
- Non-Noetherian X with infinitely many components: no finite enumeration of
  components is asserted or used. The source argument is affine-local and
  uses finite presentation of i instead.
- The universe u is explicit, as are all variables. No independent universe
  restricts test objects, and no implicit parameter is auto-bound.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: "A generic point of an irreducible component of
  a scheme in the image of a finitely presented closed immersion has an open
  neighborhood contained in that image" returned eight hits. They concern
  generic points of components, generic-point images under open immersions,
  generalizing maps and stalk morphisms; none states the desired neighborhood
  theorem for a finitely presented closed immersion.
- `msearch.py ... loogle`: `IsGenericPoint, irreducibleComponents` returned
  `genericPoints.isGenericPoint` and `genericPoints.isGenericPoint_ofComponent`.
  Both describe generic points; neither gives the neighborhood conclusion.
- `msearch.py ... leansearch`: "A generic point in the image of a closed
  immersion of finite presentation has an open neighborhood contained in the
  image" returned eight hits about closed-immersion images, open immersions
  and local finite type. None states this result.
- `msearch.py ... grep`:
  `generic.*(constructible|interior)|[Ii]nterior.*generic|generic.*[Ff]inite[Pp]resentation`
  returned zero Mathlib hits.
- `rg -n` with the same patterns and the node id in `lean/WeilConjectures` and
  `lean/Sheaf` returned neighboring generic-fibre, constructible-sheaf and
  fibre-interior results; none states the item. In particular
  `FiniteGenericFiberStratumInteriors.lean` assumes a finite map to a Noetherian
  integral affine base and a stratification and has a different conclusion.
  `ClosedFibreInteriorComponent.lean` concerns fibre dimension. The generic
  lissity result in `WeilSheaf/LisseLocus.lean` concerns sheaves on a Noetherian
  scheme, not arbitrary finitely presented closed subschemes.
- `rg` for the proposed declaration name and module name in the project,
  Mathlib and `dag/lean_names_upstream.json` found no existing declaration.

No statement correction, new node, dependency module, or unresolved statement
fault was needed.

## Second reading by Q83

A separate second pass by the same worker reopened the node and module and
checked the displayed table against the actual signature. The dispatcher
prohibits starting other agents; the maintainer performs the independent review.
The pass checked that `C ∈ irreducibleComponents X` imposes maximal irreducibility,
not merely irreducibility; `IsGenericPoint ξ C` refers to that same C; the image
in both hypothesis and conclusion is the same `Set.range i`; and the two
conclusion clauses concern the same existential `N : X.Opens`. Finite presentation
uses all three properties in the convention node, with quasi-separatedness on i
rather than X. The signature requires neither reducedness nor Noetherianity.
There is no scheme-theoretic factorization clause. No mismatch or statement
change was found.

Validation: `scompile.py Q83 lem-sfb-generic-point-fp-closed-interior` on the
module succeeded in both sandbox and library module modes (5.8 s and 6.5 s),
with no compiler errors or unexpected warnings. A direct JSON comparison
confirmed that only `lean` changed. Every Lean source line is at most 100
characters.
