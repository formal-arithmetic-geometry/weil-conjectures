## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricTangentUnramified` states
`AlgebraicGeometry.unramified_iff_geometricFiber_tangentSpace_zero`, with proof `sorry`.
It gives two equivalent tests for unramifiedness as the two conjuncts of one theorem:
vanishing of geometric-fibre tangent spaces and uniqueness of relative dual-number lifts.
No definitions or helper nodes are introduced. The current, NZ stage-1-reviewed node is
used without changing its statement or any dependency fields. The previous blocked attempt
had delivered no Lean record; this delivery supplies a genuine new statement and node delta.

Hypothesis and clause correspondence:

- Schemes X and S and their morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally of finite type: `[LocallyOfFiniteType f]`. There is no finite-presentation,
  flatness, separatedness, quasi-compactness, or Noetherian binder.
- Unramifiedness: `IsUnramified f`, the dependency's actual definition combining
  `LocallyOfFiniteType f` with `IsOpenImmersion (pullback.diagonal f)`.
- Every algebraically closed field and every geometric point of S:
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)`.
  The field and schemes share the explicit universe u; this includes an algebraic
  closure of every source residue field and does not impose an independent smaller
  universe on test fields. No algebraicity over the residue field of a base point
  is required: arbitrary geometric point maps s are tested.
- The geometric fibre scheme is `pullback f s`, with structure map `pullback.snd f s`.
  This uses the recorded fibre product, rather than a set of geometric lifts.
- Every Omega-point of that fibre is `x : Spec (.of Ω) ⟶ pullback f s` with
  `x ≫ pullback.snd f s = 𝟙 (Spec (.of Ω))`. This equation says precisely that x
  is a morphism over Omega, not an arbitrary scheme map from Spec Omega.
- Its underlying point is `x (IsLocalRing.closedPoint Ω)`. The tangent space is the
  dependency's `schemeTangentSpace Ω (pullback f s) (pullback.snd f s)` at this point.
  No residue-field identification is assumed as an additional hypothesis: at an
  Omega-point over Omega, its residue field is canonically Omega.
- Zero tangent space: `Subsingleton (schemeTangentSpace ... )`. The recorded tangent
  space carries an additive group, hence contains zero. Thus Subsingleton means exactly
  that it is the zero vector space, with no choice of a separate vector-space model.
- The first equivalence is the first conjunct `IsUnramified f ↔ ∀ ... Subsingleton ...`.
- The equivalent infinitesimal test is the second conjunct `IsUnramified f ↔ ∀ ...`.
  Here `θ : Spec (.of (DualNumber Ω)) ⟶ pullback f s` is the proposed lift;
  `θ ≫ pullback.snd f s = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω))`
  states it is a map of Omega-schemes. Reduction is
  `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ θ = x`.
  The conclusion identifies θ with the specified constant map
  `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω)) ≫ x`.
  The inclusion is Omega to dual numbers, hence Spec reverses it to the structure map;
  the first projection sends epsilon to zero, hence Spec gives the closed point inclusion.
- Empty fibres: the universal quantifier over Omega-points has no instances. Nothing
  demands a point in every fibre or nonemptiness of the source or base.

Statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (source lines 36–46 and 74–78): schemes and their morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (lines 39–46).
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`:
  `AlgebraicGeometry.IsUnramified`, read with its docstring and exact conjunction.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (lines 58–63), together
  with inline field/map binders, as `def-weil-geometric-point` prescribes.
  Also read `Scheme.SpecToEquivOfField` and its docstring in
  `Mathlib.AlgebraicGeometry.ResidueField` (lines 343–359); no bundled point replacement.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and their universal property (lines 92–139),
  with scheme pullbacks from `Mathlib.AlgebraicGeometry.Pullbacks`.
  Both `def-weil-geometric-fibre` and `def-pc-fibre-product` record this construction.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`:
  `AlgebraicGeometry.schemeTangentSpace`, with its additive-group/module instances;
  read the full module and docstrings. This is the upstream module named by the node,
  not its retired Sheaf twin. Its residue-field-based tangent space agrees with the
  Omega-based formulation because x is a rational point over Omega.
- `Mathlib.Algebra.DualNumber`: `DualNumber`, `DualNumber.eps` (lines 43–51),
  with the actual `TrivSqZeroExt.inlHom` and `TrivSqZeroExt.fstHom` maps already used
  in the recorded tangent definition.

The statement imports are public. The already-stated proof dependencies have plain imports:
`Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality`
(`rational_tangent_cotangent_duality`),
`Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion`
(`rational_unramified_iff_cotangent_surjective`),
`Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange` (`unramifiedLocus_baseChange`),
`Mathlib.LinearAlgebra.Dual.Lemmas` (`LinearMap.dualMap_injective_iff`), and
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` (`AlgebraicClosure`).
The locally-finite-type base-change instances are already public through the statement
imports. The theorem docstring records all six proof steps of the node, including the
closed rational-point checks, passage through a closure of the source residue field,
base-change reflection of locus membership, and the equivalence of the two tests.

Source checks: read varieties.tex, definition-tangent-space (0B2C) and
lemma-injective-tangent-spaces-unramified (0B2G), including its proof, and
morphisms.tex, lemma-set-points-where-fibres-unramified (0475), including its proof.
These supply the relative tangent notion, the local rational-point criterion, and the
arbitrary-base-change test. The accepted node's wording already says maps of Omega-schemes;
there is no statement correction, dependency repair, or disputed statement in this packet.

Edge cases checked mathematically before writing:

- Empty source and empty fibres give vacuous point conditions, and the empty morphism
  is unramified. The empty base forces an empty source and is included.
- For the identity of a field spectrum, the tangent space relative to that field is
  zero. The relative-base equation forces every dual-number lift to be constant.
  This equation is essential: for an algebraic closure of Q(t), a nonzero derivation
  gives a nonconstant non-relative dual-number map. Such a map is correctly excluded.
- Affine one-space over an algebraically closed field fails both criteria: at the
  origin the map sending the coordinate to epsilon is a nonconstant relative lift,
  and its tangent space is one-dimensional. The lft hypothesis therefore does not
  make either conclusion hollow.
- Nonreduced geometric fibres, including those obtained from inseparable finite field
  extensions, can have nonzero tangent spaces and are not incorrectly omitted.
- Every characteristic is allowed; no characteristic-zero or perfectness binder occurs.
  Nonclosed points on X are tested by taking a closure of their own residue fields,
  not by assuming all points of a single geometric fibre are rational.
- The only extra equations in the dual-number test express being over Omega and
  reducing to x; they are the source's defining conditions, not extra restrictions.

Searches actually run using `batch2/msearch.py` with group NW and this item:

- LeanFinder, query `A locally finite type morphism of schemes is unramified iff all
  geometric fibre tangent spaces vanish`: 8 hits, chiefly `FormallyUnramified`, its
  affine criterion and open-diagonal instance, and `Algebra.unramifiedLocus_eq_univ_iff`.
  None gives the geometric tangent-space criterion.
- Loogle, query `"AlgebraicGeometry", "tangent"`: 0 hits.
- Mathlib grep in `AlgebraicGeometry`, query
  `tangent.*unramified|unramified.*tangent`: 0 hits.
- LeanSearch, query `Unramified scheme morphisms characterized by vanishing tangent
  spaces at geometric fibre points`: 8 hits, giving formal unramifiedness and
  vanishing Kahler differentials, not this geometric-fibre tangent criterion.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `geometric.*[Tt]angent|[Tt]angent.*unramified|unramified.*[Tt]angent`:
  found the rational cotangent criterion and the finite locally free tangent criterion.
  They have different hypotheses/conclusions and are not an exact existing match.
- `rg -n lem-sfb-geometric-tangent-unramified lean/WeilConjectures`: no match.
- `rg` of Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json` for
  `geometricTangent|unramified_iff_geometric|GeometricTangentUnramified`: no match.

Validation: `scompile.py NW lem-sfb-geometric-tangent-unramified` compiled the delivered
file in both sandbox and library module modes cleanly (1.9 s and 2.3 s), with no errors
or warnings. The module starts with `module`, explicitly binds universe u, and disables
autoImplicit. Its sole theorem has proof `sorry`; it contains no other declaration.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
