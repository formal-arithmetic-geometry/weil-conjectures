## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveStrictLocalIntersectionAcyclic` states
`AlgebraicGeometry.Scheme.isZero_cohomology_projective_strictLocal_intersection`, with `sorry`
as the entire proof. No definition is introduced and no theorem is proved.

Clause-by-clause correspondence:

- Schemes `B,P`: `{B P : Scheme.{u}}`; affine base: `[IsAffine B]`.
- The named morphism `p : P ⟶ B` and `[IsProjective p]` use the blueprint's H-projective
  and quasi-compact convention, without replacing it by properness.
- The two arbitrary geometric points have independently chosen fields `Ωx,Ωu : Type u`,
  each with `Field` and `IsAlgClosed`, and maps `x,y : Spec (.of Ω) ⟶ P`.
  The Lean name `y` denotes the node's point `u` (universe `u` is unrelated).
- `W` is written out as `pullback (strictHenselizationStructuralMap x)
  (strictHenselizationStructuralMap y)`. These canonical maps have sources precisely
  `strictHenselizationScheme x` and `strictHenselizationScheme y`, spectra of the small
  affine pointed-neighbourhood coordinate-ring colimits. There is no arbitrary-map binder.
- `A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}` is an arbitrary abelian sheaf
  on the small etale site. `hA : IsTorsionAbelianSheaf A` is exactly the recorded
  colimit-of-positive-integer-kernels torsion condition, not sectionwise torsion or a
  fixed torsion exponent.
- `i : ℕ`, `hi : 0 < i` cover all the requested positive cohomological degrees.
  `IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} W (i : ℤ)).obj
  ((DerivedCategory.singleFunctor _ 0).obj A))` expresses zero of derived global sections
  cohomology, with the sheaf placed in degree zero. `IsZero` applies to an object of
  `AddCommGrpCat`, not a bare type.
- The signature has no nonemptiness, connectedness, finite-component, Noetherian,
  constructibility, uniform exponent, or invertibility assumption. All universes and
  variables are explicitly bound; the site/coefficient universe convention is unchanged.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, morphisms `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, `IsProjective`;
  the current source was read using `scompile.py --source` because the older checkout
  lacks this extracted module.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points inline as
  prescribed. Also read `Scheme.SpecToEquivOfField` in Mathlib's `ResidueField.lean`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`,
  `strictHenselizationScheme`, `strictHenselization_properties`, read through `--source`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, including its full signature and common-composite
  characterization in `exists_strictHenselizationStructuralMap`, read through `--source`.
  The item gains this already recorded node in `stmt_deps` to name the maps in its fibre product.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`;
  scheme pullbacks from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`: `Scheme.IsTorsionAbelianSheaf`, including
  its full colimit diagram definition.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.cohomology` and
  `Etale.rightDerivedGlobalSections`, with their complete coefficient/category hypotheses
  and defining composition with the homology functor.

The proof docstring carries all three DAG proof steps, including the common affine open,
ind-etale strictly henselian rings, and Artin tensor acyclicity. All available recorded
proof-dependency modules are imported without `public`: `ProjectiveFiniteAffineNeighbourhood`,
`IndEtaleStrictLocalInvariance`, `StrictHenselizationAffineChartIndEtale`,
`StrictHenselizationClosedLift`, and the upstream henselian terminology. The Artin tensor
node has no recorded statement yet, so no module exists to import for that proof dependency.
The initially suspected collision in the proof-only imports does not occur in the published
compile environment: adding all three strict-henselization proof imports compiled cleanly.

Edge cases: `i=0` is intentionally excluded and `i=1` included. `A=0` is allowed. Coincident
geometric points and unrelated algebraically closed point fields are allowed. An empty `W`
(e.g. points on disjoint projective components) is allowed. No component finiteness is used;
no characteristic or torsion-order exclusion occurs. An empty `P` simply has no geometric
point inputs; no inhabitance hypothesis is introduced. The single universe is the recorded
scheme/strict-localization size convention, polymorphic in `u`.

Source verification: opened Hübner–Schmidt's author PDF
<https://www.mathi.uni-heidelberg.de/~schmidt/papers/algebraic_tame_site.pdf>, Definition 7.8,
Proposition 7.9, Theorem 7.10 and Proposition 7.14(i), pp. 14–16. The tensor theorem and the
geometric finite-affine-neighbourhood formulation impose no Noetherian or invertibility
hypothesis. No statement correction or STATEMENT-DISPUTED flag is needed.

Searches (all through the prescribed tools, outputs in the sandbox `searches.jsonl`):

- LeanFinder: "For a projective scheme over an affine base the fibre product of two strict
  localizations has vanishing positive etale cohomology for torsion sheaves". Eight hits on
  affine limit section vanishing, etale morphisms and etale algebras; none states the item.
- Loogle: `"strictLocalization", "cohomology"`: zero hits.
- LeanSearch: "Artin acyclicity of fibre products of strict localizations of a projective
  scheme over an affine base": eight hits on Artinian localizations and affine/Proj pullbacks;
  no matching cohomology statement.
- Mathlib grep: `strict.*local.*acyclic|projective.*strict.*local|Artin.*(tensor|join)`:
  four unrelated hits on Artinian modules/flatness and finite-product monoidal construction.
- `rg` of the same pattern in the upstream `WeilConjectures` and shared `lean/Sheaf` trees
  finds only unrelated Artin–Schreier/Artin–Rees material and a projective-line heading.
  `grep -rn` for the exact blueprint id in upstream yields no hit. The chosen declaration
  name was also searched in upstream, side sources and `dag/lean_names_upstream.json`;
  no existing declaration was found.

Validation: prescribed `scompile.py Q24 lem-trf-projective-strict-local-intersection-acyclic
<file>` compiled both its sandbox and library paths cleanly, then the final file with all available proof imports also compiled cleanly
(3.9 s and 3.1 s), no errors
or non-sorry warnings. No global build or direct git command was run.

## Second reading by Q24

Author's second reading (the dispatcher forbids starting another agent; independent review
belongs to the maintainer): reopened the node and final file and compared each binder and
conclusion as above. The two strict-localization maps have the same ambient target `P`;
the fibre product is over `P`, not over `B` or a residue field. The two point fields are not
identified. Torsion is the canonical sheaf-level condition. Derived cohomology is the recorded
functor on the degree-zero sheaf, and only positive natural degrees are quantified. Checked
the empty product and unrestricted component-count clauses against the absence of additional
binders. No mathematical mismatch was found. The structural-map dependency is added explicitly. The strict-henselization declaration
is the recorded declaration name, supplied here by its canonical upstream owner; its
older Sheaf module is not imported, as the user directs when owners duplicate. No dependency
record is changed.

The first dry run exposed inherited DAG proof-metadata inconsistencies when attempting an
unnecessary lean-record refresh of the strict-henselization dependency. That refresh was
removed: importing the canonical upstream owner already supplies the recorded declaration
names and the full construction. The final packet changes only the item and introduces no
dependency module or definition. This follows the explicit preference for upstream imports
when an older side module duplicates declarations.
