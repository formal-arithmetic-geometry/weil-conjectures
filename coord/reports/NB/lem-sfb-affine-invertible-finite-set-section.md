# Stage-2 statement: lem-sfb-affine-invertible-finite-set-section

## Worker report

The module `Sheaf.AlgebraicGeometry.AffineInvertibleFiniteSetSection` states
`AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishing_on_finite_set`.
It introduces no definitions, proves nothing, and leaves exactly that theorem as `sorry`.
The node copy changes only `lean`. No statement correction or dependency repair is needed.
The previous worker's stale-assignment message referred to NM's stage-1 split, merged at
01:50 on 2026-10-22; the live node has no stage-2 Lean record, and this delivery does not
resplit it or change its proof.

The source was read at `literature/stacks-project/properties.tex`, lines 5327–5395,
label `lemma-quasi-affine-invertible-nonvanishing-section` (Tag 0F20), including its
induction proof. Its quasi-affine assertion specializes to affine X and W = X;
this node asks only for nonvanishing, so the extra affine section-open conclusion
of the source is deliberately absent, as it is absent from the node.

Clause-by-clause correspondence:

- “Let X be an affine scheme”: `(X : AlgebraicGeometry.Scheme.{u})`
  and `[AlgebraicGeometry.IsAffine X]`. `IsAffine` identifies X with Spec of its
  global sections; it does not add a finite-type or Noetherian condition.
- “L an invertible O_X-module”: `(L : X.Modules) [L.IsInvertible]`, using the exact
  recorded invertibility class. It means Zariski-locally free of rank one;
  quasi-coherence follows from this and is not an additional hypothesis.
- “E a finite set of points, not necessarily closed”: `(E : Set X) (hE : E.Finite)`.
  The points are the underlying points of the scheme, with no closed-point predicate.
- “There exists s in Gamma(X,L)”: `∃ s : Γ(L, ⊤)`.
- “For every x in E”: `∀ (x : X), x ∈ E →`.
- “The image of its germ in L_x / m_x L_x is nonzero”:
  `L.presheaf.germ ⊤ x trivial s ∉
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x))`.
  The stalk is `L.presheaf.stalk x`; the displayed ideal multiple of its top
  submodule is literally m_x L_x. A quotient class is zero exactly when its
  representative belongs to this submodule, so nonmembership expresses precisely
  the requested nonzero residue class, without a choice of trivialization.
- The explanatory local ring is `X.presheaf.stalk x` and its maximal ideal is
  `IsLocalRing.maximalIdeal (X.presheaf.stalk x)`. The imported recorded residue-field
  definition is `X.residueField x = IsLocalRing.ResidueField (X.presheaf.stalk x)`.
  No separately chosen residue field or extension data enters the statement.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` in
  `Mathlib.AlgebraicGeometry.Scheme`; affine structure uses
  `AlgebraicGeometry.IsAffine` and `Scheme.isoSpec` in
  `Mathlib.AlgebraicGeometry.AffineScheme` (lines 59–69).
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, lines 57–60.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` in `Mathlib.AlgebraicGeometry.ResidueField`,
  lines 45–46 and 128–131; the full signatures and docstrings were read.
- The existing stalk module instance in
  `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`, lines 166–169,
  supplies the canonical O_X,x-module structure on `L.presheaf.stalk x`. This is a
  public import because that instance is used in the statement; no extra instance
  or hypothesis is supplied by this delivery.

All proof dependency nodes were also read. The already recorded proof interfaces
are imported without `public`: `nonempty_affine_algebraModule_generatingSections`
from `WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleGenerators`,
`globalGeneration_nonvanishing_cover` from
`WeilConjectures.AlgebraicGeometry.GlobalGenerationNonvanishingCover`, and
`nonvanishing_section_trivializes` from
`WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`.
Their signatures and proof docstrings were read. The Mathlib-leaf proof interfaces
for `def-weil-affine-spectrum` and `lem-weil-pbc-affine-open-stalk-localization`
come from the imported `Mathlib.AlgebraicGeometry.AffineScheme` and its imports.
The theorem's docstring carries all six proof steps, including clearing denominators,
global generation, the comparable-point reduction, the induction section, the
separating scalar product, and the final sum.

Edge cases checked before writing:

- E empty: zero is a global section and the point condition is vacuous. No nonempty
  binder on X or E appears.
- X empty (including Spec of the zero ring): E is empty and the same conclusion holds.
- E a singleton: global generation gives a nonvanishing section at its point.
- Comparable points: openness propagates nonvanishing from a specialization to its
  generalizations, as in the source's induction; distinctness or incomparability
  is not a statement hypothesis.
- Generic and other nonclosed points: allowed by `x : X`; there is no maximal-prime
  or closed-point restriction.
- No restriction on characteristic, residue-field size, dimension, reduction, or
  Noetherianness is imposed. A line bundle on an affine scheme need not be trivial;
  the conclusion asks only for one section on the prescribed finite set.
- `u` is explicit and unrestricted; `autoImplicit` is disabled. The module and stalk
  universes follow the project's existing `X.Modules` convention.

Searches actually run with `msearch.py NB lem-sfb-affine-invertible-finite-set-section`:

- LeanFinder: “An invertible sheaf on an affine scheme has a global section nonvanishing
  at every point of a prescribed finite set”. Eight hits: structure-sheaf fraction
  normalization, clearing denominators on affine opens, scalar evaluation/basic-open
  lemmas, `Scheme.affineBasicOpen`, and `IsAffineOpen.basicOpen`. None chooses one
  section of an arbitrary invertible module nonzero on a finite set.
- Loogle: `AlgebraicGeometry.Scheme.Modules.IsInvertible, "section"`.
  Zero hits; the service reports the project-specific identifier as unknown.
- Mathlib grep: `nonvanish.*[Ff]inite|[Ff]inite.*nonvanish|affine.*[Ss]ection`,
  subdirectory `AlgebraicGeometry`. Seventeen hits about Noetherian affine covers,
  ideal sheaves, scalar sections/basic opens, finite morphisms and affine limits;
  none states the required invertible-module section-existence theorem.
- LeanSearch: “A line bundle on an affine scheme admits a section nonzero in the
  residue fibres at finitely many prescribed points”. Eight hits: scalar evaluation,
  `evaluation_ne_zero_iff_mem_basicOpen`, clearing denominators, scalar zero-cover,
  and component nontriviality. The evaluation signature applies to `Γ(X,U)`,
  sections of the structure sheaf, and not to an arbitrary invertible module.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `finite.*nonvanish|nonvanish.*finite|affine.*[Ff]inite.*[Ss]ection|[Ss]ection.*[Ff]inite.*affine`:
  results concern other finite-section constructions, finite nonvanishing covers,
  ample tensor powers, or the consumer `FiniteTrivializeInvertibleUpstairs`.
  They do not supply this lemma.
- `rg` for the item id in both project source roots found only the consumer's proof
  docstring. A further name/module collision search for
  `exists_section_nonvanishing_on_finite_set|AffineInvertibleFiniteSetSection`
  in Mathlib, both project roots, and `dag/lean_names_upstream.json` found no hit.

No STATEMENT-DISPUTED flag and no node fault was found. The only initial elaboration
issue was import visibility for the existing stalk module instance; adding the
owning module as a public import preserves exactly the same mathematical statement.

Validation: `scompile.py` successfully compiled both the sandbox check and the actual
module (2.2 s and 2.3 s), with no errors or unexpected warnings. The prescribed
`deliver2.py --no-push` passed the server preflight and per-file compile. A local
read-only packet check confirmed that only `lean` changed in the node, the recorded
signature is verbatim, all Lean lines are at most 100 characters, and the module
contains exactly one theorem and one `sorry`.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
