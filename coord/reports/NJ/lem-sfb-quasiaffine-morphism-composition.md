## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiAffineMorphismComposition` states
`AlgebraicGeometry.isQuasiAffineHom_comp` with proof `sorry`. Its statement is
exactly composition of quasi-affine scheme morphisms, as in Stacks Project,
Morphisms, Tag 01SN, `lemma-composition-quasi-affine` (the statement and complete
proof were read at `literature/stacks-project/morphisms.tex:2280–2316`).
No new notion, dependency repair, or statement correction is necessary.

Hypothesis and conclusion correspondence:

- The three arbitrary schemes are `{X Y Z : Scheme.{u}}`, with `universe u`
  explicitly declared. No affine or quasi-affine assumption on these schemes
  is imposed.
- The morphisms are `(f : X ⟶ Y)` and `(g : Y ⟶ Z)`, in the category of schemes.
- Quasi-affineness of f is `[IsQuasiAffineHom f]`.
- Quasi-affineness of g is `[IsQuasiAffineHom g]`.
- The composite g ∘ f is Lean's `f ≫ g`; the full conclusion is
  `IsQuasiAffineHom (f ≫ g)`.
- The explanatory clause about inverse images of every affine open is exactly
  the field `IsQuasiAffineHom.isQuasiAffine_preimage (U : Y.Opens)
  (hU : IsAffineOpen U) : (f ⁻¹ᵁ U).toScheme.IsQuasiAffine`. Mathlib's
  `Scheme.IsQuasiAffine` includes `CompactSpace` and the canonical immersion into
  `Spec Γ`, which is proved to be an open immersion. Conversely a quasi-compact
  open subscheme of an affine scheme is quasi-affine by
  `Scheme.IsQuasiAffine.of_isImmersion`. Thus this uses the same quasi-compact
  meaning of quasi-affine as the node, rather than a weaker open-subscheme notion.
- No finite-type, Noetherian or separatedness assumption is present. Any
  quasi-compactness or relative separatedness needed for the source proof must
  be derived, rather than added to the statement.

The statement dependency interfaces were opened and read, including signatures
and docstrings:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`. These are the
  recorded locally ringed spaces with local affine charts and their morphisms.
- `def-nagata-quasi-affine-morphism`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`, declaration
  `AlgebraicGeometry.IsQuasiAffineHom`, with the affine-open preimage field above.
  This is the exact recorded declaration and is not redefined.

The two statement modules are public imports. Imports for the stated proof
plan are non-public: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.QuasiAffine`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
`Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
`Mathlib.AlgebraicGeometry.OpenImmersion`,
`Sheaf.AlgebraicGeometry.QuasiAffineRelativeSpecEmbedding`
(`AlgebraicGeometry.isQuasiAffineHom_iff_exists_relativeSpec_embedding`),
`WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`),
and `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`
(`AlgebraicGeometry.affine_morphism_relative_spec`). The declaration docstring
carries all five proof steps, including the quasi-coherent algebra pushforward,
its restriction identification, and relative-Spec open embedding.

Edge cases checked before writing:

- Empty source and empty affine test opens are included; no nonemptiness binder
  occurs, and the empty inverse image is quasi-affine.
- Identity morphisms and isomorphisms are covered, with the ordinary composition
  order `f ≫ g`.
- Affine f and g give the familiar affine-composition special case.
- The bases need not be quasi-compact, Noetherian, or separated. The proof is
  local on affine opens of Z; its use of compactness applies to W and E, not
  globally to X, Y, or Z.
- There is no finite-type restriction: even non-finite-type affine maps are
  within the quantifiers. A single arbitrary scheme universe u is the standard
  category-of-schemes convention, with no independent smaller test universe.

Searches for an existing statement:

- `msearch.py ... leanfinder "The composition of two quasi-affine morphisms of
  schemes is quasi-affine"`: eight hits, including affine composition,
  `Scheme.IsQuasiAffine.of_isAffineHom`, and quasi-compact composition; none
  states composition of arbitrary relative quasi-affine morphisms.
- `msearch.py ... leansearch "Quasi-affine morphisms are stable under
  composition"`: eight hits for quasi-separated, quasi-compact, affine, and
  quasi-finite morphisms, plus the abstract composition property; no exact match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.IsQuasiAffine"`: twelve
  absolute quasi-affine scheme declarations. None gives the required relative
  composition statement.
- `msearch.py ... grep "QuasiAffine.*comp|quasi.affine.*compos|IsQuasiAffineHom"
  AlgebraicGeometry`: only two Mathlib hits, for absolute quasi-affineness from
  an immersion or from affine basic opens, not the relative composition theorem.
- Direct `rg` for `IsQuasiAffineHom`, `QuasiAffineMorphism`, and composition
  variants in `lean/WeilConjectures` and `lean/Sheaf`, plus the item id in
  `lean/WeilConjectures` and the proposed declaration name in
  `dag/lean_names_upstream.json`: no existing general composition theorem.
  The upstream QuasiAffine module was read in full: its composition instance
  requires an immersion and quasi-compact composite, so does not state this node.
  The Sheaf hits for ind-quasi-affine composition concern different notions.
- No repair note exists for this item. The prescribed CompactObject example
  is currently a withdrawn module with no declarations; the node still records
  its upstream definition. The delivery follows the active module conventions
  in the nearby QuasiAffineRelativeSpecEmbedding module.

No `STATEMENT-DISPUTED` issue or node fault was found. The node copy changes only
`lean`; its statement, dependencies, and proof are preserved.

## Second reading by NJ

Re-read the node and completed Lean file after drafting. This is a separate
self-review pass by the assigned worker; no independent reader or sub-agent is
claimed. The dispatcher expressly prohibits starting other agents, and the
maintainer supplies the independent review after delivery.

The binders give all three arbitrary schemes and both composable morphisms;
the two class hypotheses are exactly the two quasi-affineness assumptions;
the conclusion applies the same relative predicate to g ∘ f in the correct
Lean order. The compact-open-in-affine interpretation was checked against both
the recorded relative class and Mathlib's absolute class, including the
canonical open-immersion instance. There are no extra typeclass assumptions,
no finite-type restriction, no hidden test object, no universe equality
restriction, and no missing conclusion. Every binder and universe is explicit,
and `set_option autoImplicit false` enforces this. The only postponed proof is
the named theorem corresponding to the delivered DAG node. No mismatch found.
