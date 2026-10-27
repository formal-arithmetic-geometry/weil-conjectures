## Worker report

The module `Sheaf.AlgebraicGeometry.GenericFibreAssassinNoncontainmentSpreads` states
`AlgebraicGeometry.Scheme.Modules.genericFibreAssassinNoncontainment_spreads` with
`sorry`. It introduces no definitions. The statement is unchanged from the DAG and
from Stacks Project, More on Morphisms, Tag 05KN, `lemma-bad-case` (local
`literature/stacks-project/more-morphisms.tex`, lines 6907–6923).

Hypothesis and conclusion correspondence:

- Schemes and the given morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Finite type of f: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the two
  conditions in `def-weil-finite-type-morphism` and the Mathlib module docstring.
- An O_X-module: `(F : X.Modules)`.
- Quasi-coherence and finite type of F: `(hF : F.IsQuasiCoherentFiniteType)`.
  This is the existing conjunction of `SheafOfModules.IsQuasicoherent F` and
  `SheafOfModules.IsFiniteType F`; it does not impose coherence or Noetherianity.
- An arbitrary open subscheme U: `(U : X.Opens)`. Its canonical open immersion
  gives the corresponding restricted scheme, so this includes every open subscheme
  up to its canonical isomorphism. There is no compactness condition on U.
- Irreducibility of the underlying space of Y: `[IrreducibleSpace Y]`.
- Its specified generic point: `(η : Y) (hη : IsGenericPoint η Set.univ)`.
  This uses the recorded generic-point notion, rather than restricting to integral
  or reduced schemes or choosing an unrelated point.
- The scheme-theoretic fibre is `f.fiber y`, with canonical projection `f.fiberι y`.
  The fibre module F_y is `((tensorPullback (f.fiberι y)).obj F)`.
- The associated points of F_y use the recorded
  `Scheme.Modules.associatedPoints` from `def-trf-relative-assassin`, which tests
  the maximal stalk ideal against the element-annihilator associated primes.
- The point set of U_y is `(f.fiberι y) ⁻¹' (U : Set X)`, the inverse image in
  `f.fiber y`, not the inverse image of a base open or a subset of X itself.
- Generic failure of containment is the binder `hU`, namely the negation of the
  subset relation between those two sets at η.
- The conclusion's open subscheme is `∃ V : Y.Opens`; its required nonemptiness
  is `(V : Set Y).Nonempty`.
- “For every y in V” is `∀ (y : Y), y ∈ V → ...`.
- The final clause repeats the same negated fibrewise subset relation at y.
  It asks only for a nonempty open, without adding a separate η-membership or
  affine-open clause. Over the irreducible base its nonemptiness already implies
  membership of η. No Noetherian, reducedness, separatedness, or flatness assumption
  has been introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Opens` (obtained transitively through the statement imports).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (transitive).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the canonical
  open-subscheme representation uses Mathlib's `Scheme.Opens`.
- `Mathlib.Topology.Irreducible`: irreducibility, irreducible components, and the
  `IrreducibleSpace` formulation for the entire underlying base space.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: publicly supplies the
  existing `Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. The actual tensor construction
  was read; no arbitrary pullback functor is substituted.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`:
  `Scheme.Modules.associatedPoints` and `Scheme.Modules.relativeAssassin`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and `fiberι` (publicly
  imported by the relative-assassin module).

The already stated proof dependencies are imported privately:
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
(`Scheme.IdealSheafData.reduced_induced_closed_subscheme`),
`WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty`
(`exists_open_closed_subset_fibre_nonempty`), `Mathlib.Topology.Irreducible`
(component coverage), and `Mathlib.AlgebraicGeometry.Properties` (scheme sobriety).
The existing node `lem-sfb-relative-assassin-neighbourhood` has no Lean record or
Mathlib match at the time of writing; it is solely a proof dependency, so its module
is not imported. It is named explicitly in the proof docstring for stage 3. No
statement dependency is missing or unusable, and no new node is required.

The full four-step corrected proof in the node is included in the theorem docstring:
choose the bad fibre-associated point and affine charts; take its reduced closure
outside U and apply the relative-assassin neighbourhood lemma; take a principal
affine P and spread its fibre nonemptiness; choose a fibre-component generic point
and recover a bad associated point on each fibre. Each step names its DAG inputs.

Edge cases checked before writing:

- Empty X or F = 0: the generic associated-point set is empty, so hU is false;
  the implication is correctly vacuous and these objects are not excluded.
- U = X: hU is false. U empty: hU asserts nonemptiness of the generic assassin;
  the conclusion asserts nonemptiness of the fibre assassins on V.
- A one-point field base: V can be the whole base and the conclusion is precisely
  the hypothesis at that point.
- Nonreduced irreducible bases and non-Noetherian bases remain permitted.
- Non-quasi-compact opens U remain permitted.
- Empty Y is excluded by irreducibility and by the specified generic point,
  exactly as in the source; no extra nonemptiness assumption is needed.
- The scheme universe u is explicit and arbitrary; every variable is bound, and
  both `autoImplicit` and `relaxedAutoImplicit` are disabled.

Searches actually run through `msearch.py` (group NM and this item):

1. LeanFinder: “For a finite type scheme morphism over an irreducible base,
   noncontainment of associated points of a finite type quasi coherent module in
   an open on the generic fibre persists on a nonempty base open”. Eight hits:
   scheme sobriety, spreading ring sections, generic points, and related basic
   results; none states this fibre-assassin assertion.
2. Loogle: `AlgebraicGeometry.Scheme.Modules.associatedPoints, IsGenericPoint`.
   Zero hits; it reports the project-specific associatedPoints identifier unknown.
   This is not evidence against the project definition, which was read directly.
3. Mathlib grep: `associatedPoints|relativeAssassin|assassin|noncontainment`
   in `AlgebraicGeometry`. Zero hits.
4. LeanSearch: “Associated points of a generic scheme fibre outside an open
   persist over a nonempty open of an irreducible base”. Eight hits, all generic
   points, sobriety and integral-open facts; no exact statement.
5. Direct rg of `lean/WeilConjectures` and `lean/Sheaf` with the same pattern found
   the existing relative-assassin and tensor-pullback interfaces and the sibling
   `GenericFibreAssassinContainmentSpreads`, which asserts containment rather than
   noncontainment. The base-change sibling asserts an equivalence under field
   extension, not this existence of a base open. No duplicate theorem was found.
6. Direct grep of this exact node ID in `lean/WeilConjectures` found no declaration.
   Direct rg of `genericFibreAssassinNoncontainment_spreads` in Mathlib and both
   project roots found no existing name.

Source issue: the local Stacks proof of 05KN infers that all of the generic support
avoids U from the existence of one bad associated point, which is invalid. For
Spec(k × k) over k with F = O and U one component, generic noncontainment holds
but the support meets U. The already reviewed DAG repairs the proof using 05F1
and 05F5. This delivery reproduces that corrected proof plan and preserves the
true statement. No STATEMENT-DISPUTED flag or statement_change is required.

## Second reading by NM

Final rereading by this worker compared the node, the 05KN source statement,
the recorded dependency definitions, and the delivered signature. The two finite-type
conditions on f, both module properties, arbitrary open U, irreducible base and
specified generic point all appear. The set on each side of the negated subset
relation belongs to the same scheme-theoretic fibre. The conclusion has exactly a
nonempty base open and failure of containment on every point of that open. No
mismatch was found and no source correction or dependency repair was made.
This is a worker self-check; the maintainer supplies the independent review of the
delivery, as specified by this dispatch brief. No other agents were started.
