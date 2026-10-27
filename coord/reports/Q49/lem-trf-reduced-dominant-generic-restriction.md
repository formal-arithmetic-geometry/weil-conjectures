## Worker report

The new module `Sheaf.AlgebraicGeometry.ReducedDominantGenericRestriction` states
`AlgebraicGeometry.Scheme.Hom.injective_genericFiber_restriction_of_isReduced`.
Its only proof is `sorry`, as required in stage 2. No definitions, helper nodes,
dependency repairs, or statement corrections are needed. The original node is
preserved except for its `lean` record.

Clause-by-clause correspondence:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Integral base: `[IsIntegral S]`, Mathlib's recorded notion, which includes
  nonemptiness, reducedness, and irreducibility.
- The specified generic point of the base: `(ξ : S)` and
  `(hξ : IsGenericPoint ξ Set.univ)`. This uses any generic point supplied by
  the statement, rather than introducing a second choice of generic point.
- Reduced source: `[IsReduced X]`, with no irreducibility or nonemptiness
  hypothesis on `X`.
- Every generic point of every component maps to ξ: `hcomponents` quantifies
  over every `C : Set X`, assumes `C ∈ irreducibleComponents X`, then quantifies
  over every `η : X` with `IsGenericPoint η C`, and asserts `f η = ξ`.
- Arbitrary open subset: `(V : X.Opens)`.
- Quasi-compact underlying space of that open: `[CompactSpace V]`. Mathlib's
  `CompactSpace` requires finite subcovers and imposes no Hausdorff condition.
  The carrier and topology of the open subscheme are the same subtype `V`.
- Open-subscheme structure and its map to S: `V.toScheme`, represented by
  the domain of `V.ι`, and `V.ι ≫ f`.
- The actual scheme-theoretic fibre over ξ is `(V.ι ≫ f).fiber ξ`, the pullback
  along `S.fromSpecResidueField ξ`, with projection `(V.ι ≫ f).fiberι ξ`.
- The source section ring is exactly `Γ(X, V)`. The canonical isomorphism
  `V.topIso : Γ(V.toScheme, ⊤) ≅ Γ(X, V)` provides the inverse
  `V.topIso.inv : Γ(X, V) ⟶ Γ(V.toScheme, ⊤)`.
- Pullback on sections along the actual fibre projection is
  `((V.ι ≫ f).fiberι ξ).appTop`, whose codomain is
  `Γ((V.ι ≫ f).fiber ξ, ⊤)`. The composite with `V.topIso.inv` is therefore
  precisely the canonical homomorphism in the node. `Function.Injective`
  of this composite is the entire conclusion.
- There is no properness, Noetherian, finite-presentation, flatness,
  nonemptiness, or irreducibility hypothesis beyond those explicitly listed
  by the node. All variables and the single ambient scheme universe are
  explicitly bound; `X ⟶ S` is a morphism in `Scheme.{u}`.

Recorded dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`. The module's
  `Scheme.Hom.appTop` is the standard global-section pullback.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral` (nonempty and domain sections on nonempty
  opens).
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`
  (closure of singleton equals the specified set).
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced` (reduced section rings on all opens).
- `def-weil-irreducible-components`: its Mathlib match in
  `Mathlib.Topology.Irreducible`, `irreducibleComponents` (maximal
  irreducible subsets). This mathlib leaf needs no Lean-record repair.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `.fiberι`, and
  `.fiberToSpecResidueField`; the fibre is the actual pullback.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `.Hom.residueFieldMap`.
  The fibre API uses the canonical spectrum of this residue field.
- The additional standard interface `Mathlib.AlgebraicGeometry.Restrict`
  supplies `Scheme.Opens.toScheme`, `.ι`, and `.topIso`; these are the
  existing open-subscheme construction already included in def-pc-scheme.

All statement dependency modules are public imports. The proof-only module
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` is a plain import for
`lem-weil-pbc-qc-scheme-vanishing-section-nilpotent`, specifically
`Scheme.isNilpotent_iff_basicOpen_eq_bot`. The remaining proof dependencies
are in modules already publicly imported: `Scheme.basicOpen`,
`Scheme.mem_basicOpen`, `Scheme.basicOpen_le`,
`Scheme.evaluation_ne_zero_iff_mem_basicOpen`,
`Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero`,
`exists_mem_irreducibleComponents_subset_of_isIrreducible`,
`mem_irreducibleComponent`, `irreducibleComponent_mem_irreducibleComponents`,
and the scheme `QuasiSober` and `T0Space` instances. The theorem docstring
reproduces the node's three-step argument and names its supporting nodes.

Source check: read the local Stacks `more-morphisms.tex`,
`lemma-geometrically-connected-fibres-towards-normal` (Tag 0AY8), including
hypotheses (2), (4), (5), and its proof. Read the surjectivity paragraph of
`lemma-stein-universally-closed` (Tag 03GY), which gives the quasi-compact
nilpotent-section argument. The extracted lemma uses only the hypotheses
needed for its generic-restriction subargument.

Edge cases checked mathematically before writing:

- `V = ∅`: both section rings are the zero ring, so the map is injective;
  no `Nonempty V` instance is requested.
- `X = ∅`: the component condition is vacuous and every open is empty;
  the same conclusion applies. The base stays nonempty because it is integral.
- Reducible `X`: over a field, `Spec k[x,y]/(xy)` satisfies the condition
  and the generic fibre over that base is the whole source. Nothing in the
  signature forces one component or finitely many components.
- Infinitely many components and non-Noetherian rings are allowed. The
  proof chooses a component only after being given a point, then uses
  quasi-compactness of the specified open for nilpotence.
- Reducedness is necessary: over `Spec k[t]`, the nonzero section ε in
  `k[t,ε]/(ε²,tε)` vanishes on the generic fibre, while its sole component
  dominates the base. This example is excluded exactly by `[IsReduced X]`.
- Component dominance is necessary: take the disjoint union of the base
  `Spec k[t]` with a point supported at t=0. Its vertical component gives
  a nonzero idempotent lost on the generic fibre. `hcomponents` excludes it.

Searches for existing declarations (all performed through the prescribed
search wrapper or read-only source search):

- LeanFinder: “Global sections of a reduced scheme inject into its generic
  fibre when all component generic points dominate the integral base”. Eight
  hits, including `germToFunctionField_injective`,
  `germ_injective_of_isIntegral`, and `map_injective_of_isIntegral`; these
  require an integral source and do not state this reducible-source result.
- Loogle: `AlgebraicGeometry.Scheme.Hom.app_injective,
  AlgebraicGeometry.Scheme.Hom.fiberι`. Zero hits.
- Mathlib grep: `generic.*injective|injective.*generic|app_injective|fiberι`
  in `AlgebraicGeometry`. Twenty-two hits, including `Scheme.Hom.app_injective`
  and `fiberι`. Reading `SchemeTheoreticallyDominant.lean` showed that
  `app_injective` assumes schematic dominance and quasi-compactness of the
  morphism; it does not state this component-dominance criterion.
- LeanSearch: “Restriction to the generic fibre is injective on sections of
  a reduced scheme whose irreducible components dominate the base”. Eight
  hits, chiefly restriction/germ injectivity for integral schemes; no exact
  match.
- Read-only `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `generic.*injective|injective.*generic|reduced.*dominant|generic_restriction`.
  Read the nearby upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField` theorem
  `Scheme.injective_Γ_map_pullback_fst_fromSpecFunctionField`: it assumes
  a flat morphism, uses Spec of the function field, and does not match.
  Read the private `generic_injective` in `ConnectedGenericFibreTrait`:
  this also assumes flatness and an affine domain base, so does not match.
- Exact blueprint-id grep in upstream `lean/WeilConjectures`: no hits.
  Exact proposed name and module searches in both libraries and the
  upstream-name index: no hits.

Validation: `scompile.py Q49 lem-trf-reduced-dominant-generic-restriction`
compiled the delivered file both in its sandbox and as its library module,
with no errors or non-sorry warnings (2.4 s and 1.4 s respectively).
No statement dispute or node fault was found.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
