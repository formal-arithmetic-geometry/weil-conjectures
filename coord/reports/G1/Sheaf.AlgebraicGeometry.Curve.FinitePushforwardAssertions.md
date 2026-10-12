## What changed

Proved AlgebraicGeometry.IsCurve.finite_pushforward_assertions without changing its
signature. Its proof now establishes torsion by the finite stalk product, transfers C1-C5
by additive cohomology equivalences and coefficient-hypothesis descent, pastes actual
pullback squares to transfer C6-C7, transfers C8 along the open pullback, and assembles the
bundle using IsCurve.assertions_iff.

Added three modules: FinitePushforwardCoefficientControl (the one unfinished intermediate
statement), FinitePushforwardCohomologyComparison (proved), and
FinitePushforwardPullbackComparison (proved), under Sheaf.AlgebraicGeometry.Curve.
The two comparison proofs construct the coefficient round-trip isomorphism from the
counit of Ab ≃ Mod(Z). The cohomology equivalence composes with the existing finite edge
map. The pullback comparison uses existing finite exchange and both declarations of
EtaleEdgeMapBaseChange, then proves the elementary equivalences of bijectivity and
surjectivity explicitly. No definition or existing statement changed.

The dry run passed the complete four-file compilation, axiom probes, server checks, and
delivery preflight except for the second reading (which the designated second reader
adds). Nothing was pushed. The final import cleanup is included in the repeated dry run.

## Proved and sorry left

- AlgebraicGeometry.IsCurve.finite_pushforward_assertions: original sorry removed.
- AlgebraicGeometry.IsCurve.finite_pushforward_cohomology_comparison: proved.
- AlgebraicGeometry.IsCurve.finite_pushforward_pullback_comparison: proved.
- The private finite_lowerStar_torsion helper in the item's module: proved from the
  finite stalk formula and Scheme.isTorsionAbelianSheaf_characterizations.
- Sole new sorry: AlgebraicGeometry.IsCurve.finite_pushforward_coefficient_control,
  node g1-finite-pushforward-coefficient-control. It states only descent of primary
  torsion, invertible-order torsion, and constructibility for the converted sheaves;
  it states no cohomology conclusion and no curve assertion implication.

Existing dependency sorries, including the torsion characterization and the abelian
constructibility descent, remain in their existing modules. They are intended upstream
items, not new sorries of this delivery. Thus this is a proved reduction, not a claim of
axiom-free closure of the target.

Edge cases checked mathematically: empty source and empty fibres give the zero product;
no surjectivity of the finite morphism is needed. The geometric fibre over the image of
a specified source point has the specified factor. Primary descent is valid also for
p = 0 and p = 1 because a factor element lifts by zero to the product. In characteristic
zero the invertible-order condition is the torsion condition. Constructibility uses
finite generation plus torsion over Z, not an incorrect claim that arbitrary finitely
generated Z-modules are finite. Pullback comparison works for arbitrary pullback schemes,
so neither field extensions nor opens require an extra curve instance.

## No longer needed

Removed direct imports:

- Sheaf.AlgebraicGeometry.BaseChangeConventions
- Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
- Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent
- Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
- Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange
- WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
- WeilConjectures.SixFunctors.BaseChange.Square
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
- WeilConjectures.SixFunctors.Finite.BaseChange

Constructible descent and torsion characterization remain upstream of coefficient control.
Edge-map compatibility and finite exchange remain upstream of the proved pullback comparison;
cohomology functoriality remains upstream of edge-map compatibility. Thus those nodes and
modules are not claimed globally unnecessary. The three new modules replace their direct
use in the item's body. Public imports are preserved.

The convention declarations in def-pc-base-change / BaseChangeConventions are not used:
Limits.pullback and IsPullback.paste_vert directly implement the chosen field extension.
No separate pasting isomorphism to a preselected source field extension is required:
C6 and C7 already quantify over every cartesian field-extension square. Consequently the
old step involving pullback along that isomorphism and cohomology composition is unnecessary
here. The inverse-image composition module still occurs inside the existing edge-map
compatibility proof and is not globally pruned. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan overstated the glue required for C6-C7:
the definitions allow any cartesian source field-extension square, so vertical pasting
suffices. The abelian constructibility descent statement does not directly accept the
ModuleCat constructibility predicates of this item's target; the unfinished coefficient
control node records this coefficient bridge explicitly rather than silently applying a
mismatched lemma. Finite stalk formula uses algebraically closed points, while the primary
and invertible-order predicates quantify over separably closed points; the remaining proof
must account for purely inseparable enlargement without changing geometric stalks.

The local Stacks TeX source is absent from this clone. Read the online source at
https://stacks.math.columbia.edu/tag/0A5D and https://stacks.math.columbia.edu/tag/03QP.
Searches run: LeanFinder for finite pushforward cohomology and for coefficient descent;
Loogle for bijective composition; msearch grep for stalkIsoPi and the existing descent;
and direct rg on the source and Mathlib. LeanSearch returned Internal Server Error and is
recorded as unavailable, not as evidence that no lemma exists.

## New nodes

g1-finite-pushforward-coefficient-control: primary/invertible-order torsion and
constructibility descend from the converted finite direct image. This is the only new
unfinished item. Its module imports the existing abelian constructibility descent rather
than replacing that planned result.

g1-finite-pushforward-cohomology-comparison: proved additive equivalence in every degree
between the underlying abelian sheaves of the converted source and direct image. Its
proof uses the existing finite edge-map theorem and explicit equivalence counits.

g1-finite-pushforward-pullback-comparison: proved equivalence of bijectivity and
surjectivity for pullback maps in any cartesian square on the finite morphism, including
all coefficient round-trip isomorphisms. Its proof uses the existing finite exchange and
edge-map compatibility nodes. No change records: no old public interface changed.

## Second reading by G1

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof text and imports changed. Verdict: pass.
2. Compiled all four sandbox modules with `lcompile.py --all`; compilation succeeded with no errors. The only remaining `sorry` is the named theorem `finite_pushforward_coefficient_control`, with a matching split node and docstring. No forbidden declarations occur. Verdict: pass.
3. Reviewed the three split-off node statements and their Lean declarations. The cohomology and pullback comparison statements are proved; coefficient control is the sole explicitly open reduction and is weaker than the target. Edge cases and coefficient transport are documented. Verdict: pass.
4. Checked the proof route against the unit and DAG. The target uses the finite stalk torsion argument, coefficient control, cohomology comparison, pullback comparison, and assertions equivalence. Removed imports are listed above; no unit step is bypassed. Verdict: pass.
5. Checked DAG `proof`, `proof_deps`, `proof_origin`, new node metadata, and the realized unit route against the Lean proof. They agree. Verdict: pass.

Changes made in this reading: none to the Lean statements or proofs; added this review record only.
