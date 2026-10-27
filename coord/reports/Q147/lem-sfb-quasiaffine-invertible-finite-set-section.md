## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiAffineInvertibleFiniteSetSection` states
`AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishing_on_finite_set_of_quasiAffine`.
Its sole theorem has proof `sorry`. No definitions, new nodes, dependency repairs or
statement corrections are needed. The node copy changes only `lean`.

Source read: `literature/stacks-project/properties.tex`,
`lemma-quasi-affine-invertible-nonvanishing-section` (Tag 0F20), lines 5326–5394,
and `definition-quasi-affine` (Tag 01P6), lines 2406–2410. The node deliberately
retains just the nonvanishing conclusion with W = X; it does not assert an affine
nonvanishing locus or introduce an arbitrary W.

Hypothesis and clause correspondence:

- A scheme X is `(X : Scheme.{u})`; `u` is explicitly declared and `autoImplicit` is false.
- Quasi-compactness is `[CompactSpace X]`, i.e. compactness without a Hausdorff requirement.
  This is the every-open-cover-has-a-finite-subcover condition in the node.
- Admitting an open immersion into an affine scheme is exactly
  `(hX : ∃ (Y : Scheme.{u}) (j : X ⟶ Y), IsAffine Y ∧ IsOpenImmersion j)`.
  The ambient scheme and immersion are existential, not extra chosen structure in the result.
  `IsAffine` is Mathlib's canonical affinization-isomorphism condition, equivalent to being
  isomorphic to Spec of a commutative ring. Any required ambient scheme can be taken to be
  Spec Γ(X,O_X), so using the same universe does not restrict quasi-affine schemes.
- An invertible O_X-module is `(L : X.Modules) [L.IsInvertible]`, using the dependency's exact
  locally rank-one predicate. No quasi-coherence or finite-type binder is added: these are
  consequences of invertibility used only in the natural-language proof.
- A finite set of arbitrary points is `(E : Set X) (hE : E.Finite)`. There is no closed-point
  predicate or specialization restriction.
- Existence of a global section is `∃ s : Γ(L, ⊤)`.
- For each point of E is `∀ (x : X), x ∈ E →`.
- The germ is `L.presheaf.germ ⊤ x trivial s`.
- The maximal-ideal multiple of its stalk is
  `(IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
    (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x))`.
  Nonmembership in that submodule is equivalent to nonzero image under the canonical
  quotient map to L_x / m_x L_x. Thus the conclusion is exactly the node's residue-fibre
  condition; it does not demand a nonzero germ alone, which would be weaker.
- No Noetherianity, reducedness, irreducibility, separatedness, nonempty-X or nonempty-E
  hypothesis occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` (lines 42, 74).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion` (line 38),
  the dependency's open immersion of locally ringed spaces.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (line 57); the full `exists_isoUnit` field
  specifies a rank-one trivialization on a neighborhood of every point.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`,
  `Scheme.residue`, and `Scheme.Hom.residueFieldMap`; residueField is literally the quotient
  of the local ring by its maximal ideal. The conclusion uses this maximal ideal directly.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine` (line 59).
- `Mathlib.Algebra.Category.ModuleCat.Stalk` and
  `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` provide the existing stalk
  module structure over the commutative structure-sheaf stalk. The latter's instance
  (lines 167–169) exposes it for `L.presheaf.stalk x`; no duplicate structure is introduced.

All recorded proof-dependency modules with Lean records are plain imports, including
QuasiAffineOpenPrincipalComparisonCover, Ample, CoherentFiniteType,
AmpleTwistGlobalGeneration, CochainTensorUniverses, GlobalGenerationNonvanishingCover,
NonvanishingSectionTrivializes, and AffineFinitePointScalarSeparation. The mathematical
proof in the docstring follows all seven steps of the node: ampleness of O_X, global
generation of L, pointwise nonvanishing, empty case, removing comparable points, an ambient
affine scalar separator, and addition s + f*t. Only the statement dependencies and APIs
needed to type the signature are public imports.

Edge cases checked mathematically:

- E empty: zero is a global section and the condition is vacuous.
- X empty: its only subset E is empty; invertibility is locally vacuous and zero works.
  CompactSpace permits the empty space and the empty scheme embeds openly in an affine scheme.
- Singleton E: global generation gives the required section.
- Nonclosed and specialization-related points: no exclusion in the signature; openness of
  nonvanishing handles comparable points in the proof.
- Finite residue fields, nilpotents, reducible and disconnected schemes: no field-size,
  reducedness or irreducibility assumption is introduced. Scalar separation and induction
  avoid a generic-linear-combination argument requiring infinite residue fields.
- Positive arbitrary scheme universe: `universe u` and `Scheme.{u}` are unrestricted.

Searches performed before writing:

- `msearch.py ... leansearch "An invertible sheaf on a quasi-affine scheme admits a section
  nonzero on a finite set of points"`: eight hits, including the quasi-affine basic-open
  criterion and canonical open immersion, but no finite-point line-bundle section result.
- `msearch.py ... leanfinder "On a quasi-affine scheme an invertible module has a global
  section nonvanishing at every point of a finite subset"`: eight hits about structure-sheaf
  localization, residue evaluation and fraction representation; no exact result.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Modules.IsInvertible,
  SheafOfModules.germ, Submodule.Quotient.mk"`: zero hits, unknown identifier
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` in the Mathlib-only search service.
- `msearch.py ... grep "nonvanishing|nonvanish|IsInvertible" AlgebraicGeometry`: zero hits.
- Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and the Mathlib AlgebraicGeometry tree
  for nonvanishing, finite-set sections, quasi-affine names, the item id, and the proposed
  declaration name: no exact result. `Sheaf.AlgebraicGeometry.AffineInvertibleFiniteSetSection`
  has `exists_section_nonvanishing_on_finite_set`, but requires `IsAffine X`, a strict
  special case; its full signature and docstring were read. The existing `nonvanishingLocus`
  in upstream `Ample.lean` uses the same germ-not-in-maximal-ideal-times-stalk predicate;
  the delivered statement spells it out, with no second definition.
- `rg` of `dag/lean_names_upstream.json` found quasi-affine framework and nonvanishing
  definitions but no declaration of this finite-set quasi-affine result.

Validation: the prescribed `scompile.py` was used. The first compile diagnosed a missing
visible instance for the commutative-ring action on `L.presheaf.stalk x`; importing the
existing FlatPullbackStalk API repairs this without altering the statement.

No STATEMENT-DISPUTED flag or mathematical node fault was found.

## Second reading by Q147

This is a separate self-check of the node and completed file, not a claim of an independent
second worker; the dispatcher explicitly forbids starting other agents and the maintainer
performs the independent review. I reopened the node's statement and compared all binders
and its conclusion against the signature. CompactSpace is precisely quasi-compactness;
hX has both affinity and the open-immersion clause and is only existential. L uses the
recorded invertibility class. E is a finite Set of all points. The conclusion has one
section simultaneously for every point of E, and nonmembership in m_x L_x, rather than
mere nonzero germ. Empty X and E remain allowed; no extra geometric hypothesis is present.
All universes and variables are bound. The source's additional affine-locus conclusion is
intentionally absent from this node and the Lean statement. No statement mismatch was found;
only the missing public stalk-instance import was repaired after the first compile.
