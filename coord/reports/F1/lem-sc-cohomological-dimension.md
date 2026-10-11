## Worker report

The module lean/Sheaf/AlgebraicGeometry/Curve/EtaleCohomologicalDimension.lean states
AlgebraicGeometry.IsConnectedCurve.subsingleton_etaleCohomology_of_two_lt, with a sorry
proof only. It defines no new notion and makes no node correction.

Every hypothesis and clause of the node is rendered as follows:

- Base field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Curve over that field: `{C : Scheme.{u}} [C.Over (Spec (.of k))]` introduces its structure
  map, and `[IsConnectedCurve (C ↘ Spec (.of k))]` says finite type, separated, connected,
  nonempty, and dimension one. The class extends IsCurve; IsCurve extends IsSeparated,
  LocallyOfFiniteType and QuasiCompact, with dimension at most one. Thus separation is
  already present and no second separation hypothesis is necessary.
- Smooth: `[Smooth (C ↘ Spec (.of k))]`.
- Any abelian etale sheaf: `(F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- Torsion: `(hF : F.IsTorsion)`, meaning every section is locally of finite additive order,
  not that all sections globally have finite order or that one integer kills the sheaf.
- Degree: `(q : ℕ) (hq : 2 < q)` retains exactly the nonnegative cohomology degrees above two.
- Cohomology as in def-weil-pbc-etale-cohomology: the functor
  `Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)` applied to
  `(DerivedCategory.singleFunctor (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F`.
  This is the homology of derived global sections of F in degree zero, precisely the
  dependency's recorded expression. Casting q to integers only adapts the functor's domain.
- Zero cohomology: `Subsingleton` of that additive group's carrier. Because the group
  contains zero, this says the group is trivial.

Dependency declarations and signatures/docstrings read:

- def-sc-curves: WeilConjectures.AlgebraicGeometry.Curve,
  AlgebraicGeometry.IsCurve and IsConnectedCurve. Their full class declarations were read.
  The general field parameter of IsCurve is specialized by the explicit IsAlgClosed binder;
  its documented smoothness predicate is the existing Smooth class. The record is usable.
- def-weil-pbc-etale-sheaves: the mixed record in Sheaf.AlgebraicGeometry.EtaleSheaves
  explicitly records CategoryTheory.Sheaf.IsTorsion and CategoryTheory.Sheaf as existing.
  IsTorsion is imported from its defining module
  WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic; its covering-sieve
  definition and docstring were read. The landed EtaleSheaves file was also read; the new
  set-valued predicates and HasTorsionEtaleCohomology are not used by this statement.
- def-weil-pbc-etale-cohomology: WeilConjectures.SixFunctors.Etale.Derived.LowerShriek,
  AlgebraicGeometry.Etale.rightDerivedGlobalSections and Etale.cohomology. Both full
  definitions and docstrings were read. The record explicitly directs the sheaf case to
  cohomology of singleFunctor 0. The module uses this exact expression without an alias.

Edge cases checked before writing: q = 2 is excluded and must remain excluded (proper
smooth curves can have nonzero degree-two cohomology); q = 3 is included. The zero sheaf
is included. Neither finite generation, constructibility, properness, affineness nor
prime-to-characteristic torsion is imposed. Arbitrarily unbounded local torsion orders
are allowed by IsTorsion. Positive and zero characteristic are both allowed. Empty,
disconnected, and dimension-zero schemes are excluded by the node's connected-curve
notion, not by an added hypothesis. The universe matches the source small-etale-site
encoding, Scheme.{u} and AddCommGrpCat.{u+1}; no extra small index restriction is imposed.

Searches (msearch.py F1 lem-sc-cohomological-dimension):

- leanfinder: "Etale cohomology of a torsion abelian sheaf on a smooth connected curve over
  an algebraically closed field vanishes in degrees greater than two": eight hits on
  cotangent cohomology and singular homology, no match.
- loogle: "AlgebraicGeometry.IsCurve, Subsingleton": zero hits, unknown identifier
  AlgebraicGeometry.IsCurve in Mathlib.
- leansearch: "etale cohomology torsion sheaf curve vanishes above degree two": unavailable,
  Internal Server Error. This is recorded as unavailable, not as a negative search result.
- grep (Mathlib/AlgebraicGeometry): "cohomologicalDimension|subsingleton.*cohomology|
  smallEtaleTopology": twelve site-definition and unrelated EllAdicCohomology hits;
  no curve vanishing statement.
- rg of WeilConjectures and lean/Sheaf for cohomological dimension,
  subsingleton_sheafH_of_three_le and this blueprint id: the existing source theorem
  AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le in
  WeilConjectures/AlgebraicGeometry/Curve/CohomologicalDimension.lean:411 has more general
  curve hypotheses and concludes vanishing of Sheaf.H (Ext-defined cohomology). Its full
  docstring and signature were read. It is not an exact declaration of this node with
  the node's recorded derived-global-sections cohomology. The dependency record explicitly
  leaves the comparison of these cohomology encodings to a stage-3 bridge. No exact existing
  statement was found in the landed Sheaf modules.
- rg for the proposed name in dag/lean_names_upstream.json, lean/Sheaf and WeilConjectures:
  no collision.

The cited blueprint markdown and Stacks source are not materialized in this machine's
literature directory. Read the DAG's source statement and all nine proof steps, and opened
https://stacks.math.columbia.edu/tag/03SC directly. Theorem 59.83.10(1) confirms vanishing
above two even for arbitrary separated finite-type schemes of dimension at most one.
The node asks only its smooth connected case; its statement is correct and is retained.
The declaration docstring records all nine DAG proof steps, including the affine-envelope
route accepted by stage 1. No STATEMENT-DISPUTED flag or dependency fault was found.

## Second reading by F1

I reread the node statement, its three statement dependencies, the Stacks source (Tag 03SC, Theorem 59.83.10(1)), and the Lean declaration line by line. The node introduces a smooth separated connected curve over an algebraically closed field, a torsion abelian étale sheaf, and an integer degree q with q > 2, and concludes vanishing of H^q. Lean renders these items as follows:

- The field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The curve and its structure map are `{C : Scheme.{u}} [C.Over (Spec (.of k))]`; `[IsConnectedCurve (C ↘ Spec (.of k))]` supplies separatedness, finite type, connectedness/nonemptiness, and dimension one through `IsCurve`, while `[Smooth (C ↘ Spec (.of k))]` supplies smoothness.
- The coefficient object is `F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}` and torsion is exactly `hF : F.IsTorsion`, the local sectionwise torsion predicate from `CategoryTheory.Sheaf.IsTorsion`.
- The degree is `(q : ℕ)` with `hq : 2 < q`, equivalent to q > 2 and including every q >= 3 while excluding q = 2.
- The cohomology object is exactly `(Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj ((DerivedCategory.singleFunctor (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)`, the expression specified by `def-weil-pbc-etale-cohomology`; the cast to ℤ only matches the functor's index type.
- `Subsingleton` on that additive group expresses that its cohomology group is zero (the group already has a zero element).

No mismatch was found and no source or Lean statement was changed. In particular, the Lean assumptions add no properness, affineness, constructibility, finite-generation, or prime-to-characteristic condition. `IsConnectedCurve` intentionally excludes empty, disconnected, and dimension-zero schemes, as does the dependency definition of connected curve. The zero sheaf is included, arbitrary local torsion orders are allowed, and both positive and zero characteristic are covered. The q = 2 edge case remains excluded, while q = 3 is included.

I checked the dependency declarations `AlgebraicGeometry.IsCurve`/`IsConnectedCurve`, `CategoryTheory.Sheaf.IsTorsion`, and `AlgebraicGeometry.Etale.cohomology` and their docstrings. Existing `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le` uses the distinct `Sheaf.H` (Ext-style) encoding and therefore does not replace this declaration; no exact existing declaration was found by LeanFinder/Loogle/grep searches. The module compiles cleanly with `scompile.py`; its only proof placeholder is the named theorem's permitted `sorry`.
