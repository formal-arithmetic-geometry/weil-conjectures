## Worker report

Item: `lem-weil-pbc-gm-pullback-strict-henselization`.
Module: `Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback`.
Declaration: `AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_strictHenselization`.
This states the node's isomorphism claim with one theorem and a `sorry` proof. No definition,
instance, or proof is added. The node copy changes only `lean`.

Hypothesis and clause correspondence:

- Schemes `X`, `S` and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Quasi-compactness and quasi-separatedness of that morphism:
  `[QuasiCompact f] [QuasiSeparated f]`. No qcqs condition on `X` or `S` is added.
- The geometric point of `S`: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `(s : Spec (.of Ω) ⟶ S)`, using the dependency's recorded inline convention.
- The strict henselization: the dependency's actual `strictHenselizationScheme s`,
  defined as `Spec (strictHenselizationRing s)`, with the ring the recorded colimit.
- Its structural map to `S`: `(ρ : strictHenselizationScheme s ⟶ S)` with `hρ`.
  The latter identifies `ρ` with the cone leg through EVERY small representative
  affine pointed neighbourhood followed by that neighbourhood's structural morphism.
  The cone object at `op (op j)` is `Spec Γ(V, top)`, so `Spec.map (ΓSpecIso R).inv`
  identifies it with the actual neighbourhood `V = Spec R`. This is exactly the
  structural map implicit in the notation `X ×_S S_(s)`, not an additional geometric
  restriction on the data. The cone identities imply these composites agree, and
  the category is nonempty by `strictHenselization_properties`; consequently such
  a `ρ` exists and is unique. No arbitrarily chosen morphism to `S` is allowed.
  The universal quantifier over `ρ` with this identification represents the canonical
  map without a new definition or data chosen from an unproved theorem.
- The fibre product and its projection: `pullback f ρ`, `pullback.fst f ρ`.
  The imported Mathlib scheme pullback instance supplies existence.
- The canonical morphism of étale sheaves:
  `upperStarGmSheafToGmSheaf (pullback.fst f ρ)`.
  Its exact source is `(Etale.upperStar AddCommGrpCat.{u+1} p).obj X.gmSheaf`
  and its target is `(pullback f ρ).gmSheaf`, with `p = pullback.fst f ρ`.
  These are the recorded units sheaf and recorded inverse image, not substitutes.
- The adjunction clause: the definition of `upperStarGmSheafToGmSheaf p` is precisely
  `((Etale.upperStarLowerStarAdjunction _ p).homEquiv _ _).symm
  (gmSheafToLowerStarGmSheaf p)`. The latter map sends units to their pullbacks along
  the first projection on each base-changed étale object.
- The conclusion "is an isomorphism": `IsIso` of this precise morphism. It is not
  merely existence of an unspecified isomorphism between the sheaves.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions`: a conventions record, with no standalone
  declaration. Used Mathlib `AlgebraicGeometry.QuasiCompact` and `QuasiSeparated`,
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `QuasiSeparated`.
  Read their class signatures and diagonal/quasi-compactness docstrings.
- `def-weil-geometric-point`: `IsAlgClosed` and the inline geometric-point binders;
  read `AlgebraicGeometry.Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` for its point/residue-field description.
  There is no need to use that equivalence in this statement.
- `def-weil-pbc-strict-henselization-limit`: imported
  `Sheaf.AlgebraicGeometry.StrictHenselization` and read the full module. Used
  `strictHenselizationScheme`, `strictHenselizationNeighbourhoods`,
  `strictHenselizationCone`; its diagram and small-representative equivalence
  determine the structural-map identification. The cone's actual indexing category
  is the DOUBLE opposite of `SmallModel`, hence `op (op j)` is intentional.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  read signatures and universal-property docstrings. Only the first projection is needed.
- `def-sc-gm-torsor`: its recorded additional declaration
  `AlgebraicGeometry.Scheme.gmSheaf` in
  `WeilConjectures.AlgebraicGeometry.Sites.Gm`. Read the units-presheaf/sheaf definitions
  and the map `gmSheafToLowerStarGmSheaf`, with its adjoint
  `upperStarGmSheafToGmSheaf`. Also read the recorded generic `Sheaf.Torsor` signature
  and docstring in `WeilConjectures.CategoryTheory.Sites.Torsor`; torsors themselves
  are not needed here, so that module is not imported.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` and
  `upperStarLowerStarAdjunction` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, imported transitively by
  `Gm`. Read their signatures, coefficient universe assumptions, and docstrings.

The only direct imports are the strict-henselization module, the existing Gm module,
and the quasi-separated morphism module; each supplies notions in the signature.
The declaration docstring carries both proof steps and the precise DAG lemma names,
including the eventually-affine descent needed for the units-colimit argument.

Edge cases checked before writing:

- An empty `S` cannot admit the given geometric point; no artificial nonemptiness
  hypothesis is added. An empty `X` is allowed: its base change is empty and the
  sheaf comparison is invertible on its empty étale site.
- There is no smoothness, reducedness, integrality, Noetherianity, properness,
  separatedness, or characteristic restriction. Nonreduced schemes are included.
- Only `f` is required to be qcqs; `S` need not be qcqs. Over each affine étale
  neighbourhood the base-changed scheme is qcqs, as used in the node's proof.
- The structural map is a strict-henselization limit map, not an arbitrary map:
  the general comparison is false for arbitrary morphisms. The existing upstream
  theorem `isIso_upperStarGmSheafToGmSheaf` requires `[Etale g]`, which is stronger
  than this node and does not apply to the limit projection in general.
- All universes are explicitly bound. The schemes and the geometric point live in
  `u`, the representative neighbourhood index is `SmallModel.{u}`, and the existing
  units sheaf uses `AddCommGrpCat.{u+1}`. No smaller test universe or independent
  index universe makes a condition vacuous. `ULift` and the additive notation in
  the imported units sheaf preserve the actual group of units.

Searches for existing statements (2026-10-11):

- `msearch.py ... leansearch "inverse image of the etale sheaf of units along base
  change to a strict henselization is isomorphic to the sheaf of units"`: service
  unavailable (Internal Server Error); no verdict inferred from this failure.
- `msearch.py ... leanfinder "pullback of etale sheaf of units to a strict henselization
  is the sheaf of units"`: 8 hits, all ring-theoretic étale-locus/standard-étale
  results; no units-sheaf limit comparison.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.gmSheaf,
  AlgebraicGeometry.Etale.upperStar"`: 0 hits; Loogle does not index the upstream
  `Scheme.gmSheaf` identifier.
- `msearch.py ... grep 'gmSheaf|strictHenselization' AlgebraicGeometry`: 0 Mathlib hits.
- `rg` in the upstream `WeilConjectures/` for `gmSheaf`, `upperStarGm`, and the item
  id: found `Sites/Gm.lean` and the generic-point theorem in `Sites/DivisorSequence.lean`,
  but no strict-henselization comparison. The former supplies exactly the canonical
  comparison morphism reused here; its invertibility theorem covers only étale maps.
  The latter covers only the generic point of an integral scheme.
- `rg` in the project's `lean/Sheaf/` for `gmSheaf` and pullback-of-units patterns:
  no same statement; found the shared strict-henselization module, whose construction
  is reused. `rg` in `dag/lean_names_upstream.json`, Mathlib, upstream, and `lean/Sheaf`
  for the chosen full theorem name found no collision.

Source check: the local Stacks tex and blueprint text named in the node are absent
on this machine. Read the primary sources online:
[Stacks Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9) gives the affine pointed
neighbourhood inverse limit and its base change along qcqs `f`;
[Stacks Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ) gives cohomology continuity
for qcqs affine-transition systems. Neither literally states this units comparison;
it is the auxiliary units-continuity assertion spelled out in this node's proof.
The source attribution is therefore understood as its proof route, not a quotation
of a theorem from either tag. No counterexample or statement correction was found.

Validation: `scompile.py P1 lem-weil-pbc-gm-pullback-strict-henselization` compiled
this single module cleanly on the server in 2.0 seconds. No warning was reported.
The first elaboration checks exposed the double-opposite cone index and the need
for the explicit `ΓSpecIso` comparison rather than an unrecognized affine instance;
both are repaired in the final signature.

## Second reading by P1

- Objects and hypotheses: schemes `X S : Scheme.{u}`, qcqs morphism `f`, geometric point `s : Spec (.of Ω) ⟶ S` with `[Field Ω] [IsAlgClosed Ω]`, strict henselization `strictHenselizationScheme s`, and its canonical structural map `strictHenselizationStructuralMap s`; all match the node and source. The base change is `pullback f (strictHenselizationStructuralMap s)` and `p` is `pullback.fst`; the comparison is `upperStarGmSheafToGmSheaf` and the conclusion is `IsIso` of that exact map.
- Edge cases: empty `X` and empty base-change are admitted; the geometric point rules out an empty `S`; no Noetherian, separated, finite-type, characteristic, integrality, or nonzero assumptions are added; universes are shared at `u`.
- Searches: checked Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, `dag/lean_names_upstream.json`, LeanFinder/Loogle/grep; no existing strict-henselization units comparison or canonical structural-map declaration was found.
- Mismatch repaired: the worker theorem introduced extra binders `ρ` and `hρ`, while the node has the canonical structural map. Added dependency node `def-weil-pbc-strict-henselization-structural-map`, with a canonical map definition obtained from its existence theorem, and changed the theorem to use that map directly. Updated the node's `stmt_deps` and copied the exact Lean signature. The theorem and structural-map declaration remain statements/definitions with `sorry` only.

## New nodes

Added `def-weil-pbc-strict-henselization-structural-map` for the canonical map omitted by the dependency declarations; its statement and module docstrings cite the strict-henselization limit and geometric-point conventions.
