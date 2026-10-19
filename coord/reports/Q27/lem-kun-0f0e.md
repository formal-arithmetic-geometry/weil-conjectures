## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow` states
`AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_boundedBelow`, with one
`sorry` and no additional declarations. The node's statement is unchanged.

Hypothesis and conclusion correspondence:

- A scheme X: `(X : Scheme.{u})`, for an arbitrary universe u.
- X quasi-compact: `[CompactSpace X]`.
- X quasi-separated: `[QuasiSeparatedSpace X]`. These are the standard scheme-space
  encodings of the scheme conventions, not separatedness or a finiteness assumption.
- E in D+(X_et): `E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))`.
- K in D+(Z): `K : DerivedCategory.Plus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))`.
  Mathlib's Plus is the full subcategory of objects cohomologically bounded below,
  not merely a category of strictly bounded chosen representatives.
- The canonical arrow is exactly `constantDerivedProjectionMap
  (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) X (DerivedCategory.Plus.ι.obj E)
  (DerivedCategory.Plus.ι.obj K)`. Its source is RΓ(E) tensor K; its target is
  RΓ(E tensor the derived constant complex K). The constant functor is exact, so its
  left derived functor used in this map is canonically the termwise constant functor.
- The sole assertion about this arrow is `IsIso`, precisely the node's conclusion.

The integer-module encoding follows the existing `def-kun-derived-tensor` record:
modules over `ULift.{u + 1} ℤ` are ordinary abelian groups of universe u+1, by
restriction along `ULift.ringEquiv.symm` and the integer-module equivalence with
AddCommGrpCat. An integer action is unique, so this adds no coefficient structure
or hypothesis. The ring lift accommodates the published small-etale coefficient
universe. There is no torsion, finite dimension, properness, or bounded-above restriction.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention record without a
  declaration or module. Its quasi-compact/quasi-separated scheme notions are the
  Mathlib space classes above; their equivalence with morphism formulations is in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` (the total right derived
  functor of `Sheaf.Γ`) and `AlgebraicGeometry.Etale.cohomology` (its composition
  with `DerivedCategory.homologyFunctor`). The map uses the former construction.
- `def-weil-pbc-bounded-derived-subcategories`: the Mathlib match
  `DerivedCategory.Plus`, `Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
  together with its full inclusion `DerivedCategory.Plus.ι`.
- `def-weil-abstract-derived-category`: `DerivedCategory` and `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. Published Grothendieck instances
  provide the derived categories here; no new localization choice is introduced.
- `def-kun-derived-tensor`: `AlgebraicGeometry.Etale.derivedTensor`,
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`. This is `curriedTensor` on
  the K-flat-derived monoidal structure, also used by the canonical map.
- `def-kun-constant-sheaf`: `CategoryTheory.Functor.mapHomologicalComplex`,
  `Mathlib.Algebra.Homology.Additive`, applied to `CategoryTheory.constantSheaf`,
  the sheafification of constant presheaves. The exactness instances in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver` identify its
  termwise derived interpretation with the left derived constant functor.
- `def-kun-constant-projection-morphism`:
  `AlgebraicGeometry.Etale.constantDerivedProjectionMap`,
  `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`. Read the entire module:
  its normalized constant-presheaf monoidal structure and flat-preservation theorem
  are global instances for ModuleCat. Its derived adjunction and tensor comparison
  specify the actual counit mate; no arbitrary map or comparison is substituted.

The module imports all recorded modules of the stated proof dependencies, as
non-public imports when used only by the proof plan. `lem-kun-lazard-flat-module`
and `lem-kun-torsionfree-complex-model` have neither Lean records nor Mathlib
matches in the read-only DAG and are referenced in the proof docstring; they are
not needed to type the statement, and hence do not require dependency modules
in this statement delivery. No missing notion or unusable dependency interface
was encountered.

The docstring carries all seven proof steps from the node: triangle compatibility
and the unit; lower-bound preservation; K-flatness from bounded flat truncations;
Lazard and qcqs cohomological continuity; truncation in E; finite induction in K;
and the degree-n high-tail cutoff N ≥ max(b, n - a + 1).

Edge cases checked: the empty scheme is allowed by the space hypotheses; zero
E and zero K are allowed; complexes may have any integer lower bounds, including
negative bounds, and may be unbounded above; coefficients may have torsion or
be torsion free; infinite flat integer groups are included; the scheme may be
non-Noetherian and need not be separated. There is no fixed cohomological degree,
no geometric point choice, and no excluded characteristic. The source statement
was checked at https://stacks.math.columbia.edu/tag/0F0E, Lemma 59.92.4. Its proof's
reversed vanishing inequalities are already corrected by the DAG's explicit
lower-bound argument; this does not affect its statement. No statement dispute.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “derived global sections tensor constant bounded
  below integer complex etale quasi compact quasi separated”. Eight hits about
  affine limits, formal unramifiedness, condensed flatness, and
  `DerivedCategory.isGE_Q_obj_iff`; none is this projection isomorphism.
- `msearch.py ... loogle`: `DerivedCategory, IsIso`. Unknown identifier IsIso;
  zero hits, no mathematical verdict from that failed name lookup.
- `msearch.py ... grep`: `constantProjection|pullOutConstant|pull_out_constant`
  in Mathlib/CategoryTheory: zero hits.
- `msearch.py ... leansearch`: “derived global sections tensor constant bounded
  below complex integer modules etale”. Service unavailable, Internal Server Error;
  no mathematical verdict.
- `rg` in upstream WeilConjectures and side lean/Sheaf for derivedTensor,
  rightDerivedGlobalSections, constant projection and pull-out-constant located the
  recorded constructions and `isIso_constantDerivedProjectionMap_of_finite_torsion_cd`.
  The latter is the different theorem lem-kun-0f12, for torsion coefficients and
  finite torsion cohomological dimension, so it does not state this lemma.
- `rg` for `kun-0f0e` in upstream WeilConjectures: no hits.
- `rg` for the new full declaration's short name in Mathlib, upstream
  WeilConjectures, side lean/Sheaf and dag/lean_names_upstream.json: no hits.

Validation: single-file compilation and the prescribed deliver2.py --no-push
are run through the authorized wrappers. The independent second reading is left
to the next worker, as required by the dispatcher brief.

## Second reading by Q27

I read the node record, its source place, and the complete Lean module independently.
The source is Stacks Project Tag 0F0E (Lemma 59.92.4). Its objects and hypotheses
match the module as follows:

- The source's scheme X, assumed quasi-compact and quasi-separated, is rendered by
  `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]`. These are the
  standard scheme-space classes used for the project's convention node; no
  separatedness, Noetherian, finite-type, or properness assumption is added.
- The source's E in D+(X_etale) is rendered by
  `E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))`.
- The source's K in D+(Z) is rendered by
  `K : DerivedCategory.Plus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))`.
  The ULift coefficient is the project's existing integer-module encoding and
  does not add a finiteness or torsion condition.
- The canonical map in the node is rendered exactly by
  `constantDerivedProjectionMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) X
  (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Plus.ι.obj K)`. Its source is
  derived global sections tensored with K, and its target is derived global
  sections of E tensor-derived constant K, through the recorded canonical
  constant-sheaf projection construction.
- The sole conclusion, that this canonical map is an isomorphism, is rendered by
  `IsIso (...)`; there are no extra equalities, bounds, or quantified clauses.

The source proof's bounded-below convention and its reduction through torsion-free
models, bounded flat complexes, and Lazard finite-free colimits are represented only
in the theorem docstring, as required for a stage-2 statement. The source page has
the same conclusion with the equality written in the opposite orientation; this is
the inverse orientation of the node's canonical arrow and does not change the
`IsIso` assertion.

Edge cases checked: X may be empty; E and K may be zero; lower bounds may be
negative; either complex may be unbounded above; integer modules may have torsion or
be infinite; and no characteristic, geometric point, Noetherian, separated, or
properness hypothesis is present. Universe u is shared by the scheme and site, with
coefficient category at u + 1, so no case is excluded by an independent small
universe.

I searched for an existing declaration with the three required search families:
LeanFinder for "bounded below etale cohomology commutes tensor product constant
abelian group complex qcqs" (eight hits about Kaehler differentials, Tor,
representations, and condensed sheaves; no match), Loogle for `"constantSheaf"`
(twelve hits including the ordinary constant functor and its global-sections
adjunction; no derived projection theorem), and `rg` through Mathlib, upstream
`WeilConjectures`, and
the repository's `lean/Sheaf` for `constantDerivedProjectionMap`,
`constantProjection`, and `pullOutConstant`. The searches found only the recorded
generic construction and the distinct finite-torsion theorem
`isIso_constantDerivedProjectionMap_of_finite_torsion_cd`; no declaration states
this bounded-below theorem. LeanSearch was unavailable (internal server error),
both in the worker search and my independent retry; no mathematical verdict is
drawn from that unavailable service. The other searches found no exact match.

No mathematical mismatch was found. The required proof-plan import
`Sheaf.Paper.ProjectionMateExact` fails in the local overlay with incorrect universe
counts for `CochainComplex.IsKFlat` embedded in the compiled `RingedTensorModel`
interface; the missing `MateCanonicalShifts` and `MateCanonicalUnit` fields are
subsequent errors. The recorded source has no explicit universe-count error to
repair. A diagnostic compile without that import passed, establishing that this
item's own signature elaborates, but the required import was restored: it serves
`lem-weil-pbc-ringed-projection-mate-exact` in proof step 1. No statement, object,
hypothesis, conclusion, dependency, or docstring proof step was changed.
The prescribed wrapper then confirmed a clean compile against current server
sources: `EtaleConstantProjectionMap` (3.2 s), `ProjectionMateExact` (14.7 s), and
this module (4.5 s), each with nice 19, two threads, and the 60-second limit.
Thus this was a local overlay artifact problem, with no source repair required.

I also read the Stacks TeX itself at `lemma-pull-out-constant`, including the
preceding and following lemma boundaries: there are no ambient restrictions on X
beyond the stated qcqs hypotheses. The reversed vanishing inequalities in its
proof are already handled by the node's seven-step proof plan; no source-based
statement correction is needed. There are no new definition nodes or dependency
modules in this delivery.

Dependency signatures checked independently: `Etale.derivedTensor A X` is exactly
`curriedTensor` on the unbounded derived sheaf category;
`Etale.rightDerivedGlobalSections A X` is `R(Sheaf.Γ X.smallEtaleTopology A)`;
`DerivedCategory.Plus` is the full subcategory given by an existential lower
cohomological bound, with `Plus.ι` its inclusion. `constantSheaf` is the constant
presheaf followed by sheafification, and `Functor.mapHomologicalComplex` maps its
objects and differentials termwise. I read the complete
`EtaleConstantProjectionMap` module: its derived adjunction and
`rightAdjointProjectionMap` supply the counit mate with the recorded tensor
comparison, not an arbitrary morphism. At the concrete lifted-integer coefficient
category every generic instance is supplied by existing module/sheaf instances,
as verified by compilation. The convention node intentionally has no declaration.
The item introduces only the named theorem, whose sole proof is `sorry`; there is
no new definition, hidden assumption, local notation, or private declaration.
Its module and theorem docstrings give the source and blueprint tag, and the
theorem docstring retains each of the node's seven proof steps. The node's
`lean.statement` was checked character-for-character against the file signature.
