## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSupportVanishing` states
`AlgebraicGeometry.affine_support_vanishing`; its only proof is `sorry`.
It is exactly the separably closed field specialization of Stacks Tag 0F0W,
`lemma-interlude-II`, read in `literature/stacks-project/etale-cohomology.tex`
(lines 19915–19943). No statement correction, new node, or dependency module.

Hypotheses and conclusion, clause by clause:

- The separably closed field L is `{L : Type u} [Field L] [IsSepClosed L]`.
- The affine scheme is `(T : Scheme.{u}) [IsAffine T]`.
- Its structure morphism over L is supplied by `[T.Over (Spec (.of L))]`;
  finite type is `[LocallyOfFiniteType (T ↘ Spec (.of L))]` and
  `[QuasiCompact (T ↘ Spec (.of L))]`, exactly the recorded conjunction.
- The abelian etale sheaf is `G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  Its torsion hypothesis is `hG : Scheme.IsTorsionAbelianSheaf G`, the recorded
  canonical-colimit definition, with no fixed exponent assumption.
- The nonnegative integer bound is `c : ℕ` (equivalently an integer with c ≥ 0).
- Every point in its support has residue-field transcendence degree at most c:
  `hsupport : Scheme.etaleSheafSupport G ⊆
  (T ↘ Spec (.of L)).pointsOfTrdegLE c`. The latter definition uses
  `Algebra.trdeg L (T.residueField t)` with the algebra structure induced by
  the actual structure morphism. It is not an independently chosen extension.
- Every integer r > c is `(r : ℤ) (hr : (c : ℤ) < r)`.
- The conclusion is `IsZero` of the abelian-group object obtained by
  `Etale.cohomology AddCommGrpCat.{u + 1} T r` on
  `(DerivedCategory.singleFunctor _ 0).obj G`. This is the recorded ordinary
  derived-global-sections cohomology, not compactly supported cohomology.

Dependency declarations read and used:

- `def-kun-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed`.
- `def-weil-scheme-over-base`: {'declaration': 'AlgebraicGeometry.Scheme.Over', 'file': 'Mathlib/AlgebraicGeometry/Over.lean', 'how': 'exact: an $S$-scheme is `X` with `[X.Over S]` (line 36), its structure morphism is `X ↘ S`; an $S$-morphism is `f : X ⟶ Y` with `[f.IsOver S]` (line 46); $\\operatorname{Hom}_S(X,Y)$ is the hom-set of `CategoryTheory.Over S` (Mathlib/CategoryTheory/Comma/Over/Basic.lean:39) between `X.asOver S` and `Y.asOver S` (line 55); an $R$-scheme is one over `Spec (CommRingCat.of R)`'}
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-torsion-etale-sheaf`: `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`, `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`.
- `def-kun-support`: `Sheaf.AlgebraicGeometry.EtaleSupport`, `AlgebraicGeometry.Scheme.etaleSheafSupport`.
- `def-kun-transcendence-degree`: `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`.
- `def-weil-pbc-etale-cohomology`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.cohomology`.

`Scheme.Hom.pointsOfTrdegLE`, in the recorded support module, is also used.
Its full definition and the support definition were read. Recorded statement
modules are public imports; available recorded proof modules are ordinary imports.
Proof dependencies without a Lean module (`lem-kun-cd-sep-closed-point`,
`def-kun-cd`, `thm-sc-affine-torsion-cd`) remain in the docstring proof plan.
Mathlib proof leaves use the subscheme, sheaf-abelian, finite-type and
quasi-separated modules. Nothing has been proved in the delivered module.

Edge cases: the empty affine scheme is allowed (no Nonempty assumption);
G = 0 makes the support condition empty; c = 0 retains all positive integer
degrees. The statement covers nonreduced schemes and arbitrary characteristic,
including separably closed imperfect fields. Torsion is local and permits
unbounded orders. The universe u is arbitrary and follows the dependency
encodings for schemes, geometric points, and abelian sheaves. There are no
auto-bound variables, local notation, local instances, or added hypotheses.

Searches actually run through msearch.py:

- LeanFinder: “Cohomology of a torsion etale sheaf on an affine scheme over a
  separably closed field vanishes above the transcendence degree of its support”:
  eight hits, all algebraic etaleness/cotangent results, no match.
- Loogle: `"Algebra.trdeg", "Sheaf.H"`: zero hits.
- Mathlib grep: `etale.*support|support.*vanish`: 22 hits, concerning the
  algebraic etale locus, distribution support, valuation support and ideals;
  none states this cohomological vanishing theorem.
- LeanSearch: “Affine torsion etale cohomology vanishes above transcendence
  degree support bound”: unavailable, Internal Server Error; not counted as no match.
- rg over WeilConjectures and lean/Sheaf: `affine.*support|support.*vanish|`
  `lem-kun-affine-support-vanishing`: unrelated supported-object/ideal results,
  no matching theorem. A further search for `affine_support_vanishing` in both
  trees and Mathlib found no collision. Searching the node id in
  dag/lean_names_upstream.json and WeilConjectures found no existing attachment.

Validation: server scompile.py compiled the module cleanly in 2.9 seconds
(initial imports); it also compiled the three side-only dependency overlays,
using nice 19, two threads and 60 seconds per file. The delivery dry run below
rechecks the final module including the remaining Mathlib proof-leaf imports.
No mathematical statement fault or disputed claim was found.

## Second reading by NY

I independently read the node, its five proof steps, the delivered module,
Stacks `etale-cohomology.tex`, lemma-interlude-II (Tag 0F0W), and all eight
statement-dependency records and the declarations used from them. The Stacks
lemma assumes an arbitrary field, an affine finite-type scheme and an abelian
torsion sheaf; its bound is a + cd(K). The node deliberately takes the separably
closed specialization, where cd(L) = 0. No additional standing hypothesis is
needed from the surrounding proof of proposition-cd-affine.

The object/hypothesis/conclusion inventory and comparison is:

- Field L, separably closed: `{L : Type u} [Field L] [IsSepClosed L]`.
  PASS. Mathlib's class requires every separable polynomial to split; it does
  not require perfectness or algebraic closedness.
- Scheme T, affine: `(T : Scheme.{u}) [IsAffine T]`. PASS. I read Mathlib's
  locally affine locally ringed space structure and the affine class asserting
  that the canonical map to Spec of global sections is an isomorphism.
- T over L and finite type: `[T.Over (Spec (.of L))]`,
  `[LocallyOfFiniteType (T ↘ Spec (.of L))]` and
  `[QuasiCompact (T ↘ Spec (.of L))]`. PASS. `Scheme.Over` supplies the
  structure morphism; the latter two classes are exactly the conjunction in
  def-weil-finite-type-morphism, not a finite field-extension assumption.
- Abelian etale sheaf G: `G : Sheaf T.smallEtaleTopology
  AddCommGrpCat.{u + 1}`. PASS, the recorded small-site sheaf encoding.
- Torsion: `hG : Scheme.IsTorsionAbelianSheaf G`. PASS. I read the canonical
  kernel diagram over positive integers ordered by divisibility and its colimit
  map. This allows locally varying and unbounded annihilators.
- Nonnegative integer c: `(c : ℕ)`. PASS, in bijection with the specified
  integers c >= 0; the degree comparison uses its integer coercion.
- Each support point t has trdeg_L kappa(t) <= c:
  `hsupport : Scheme.etaleSheafSupport G ⊆
  (T ↘ Spec (.of L)).pointsOfTrdegLE c`. PASS. I opened both definitions:
  support means some nonzero geometric stalk above t; the stratum uses
  `Algebra.trdeg` with the algebra induced by `p.residueFieldAlgebraMap t`.
  Thus the base extension is the actual structure morphism. The geometric
  points use algebraically closed fields in the scheme's universe, which
  includes algebraic closures of all its residue fields.
- Every integer r > c: `(r : ℤ) (hr : (c : ℤ) < r)`. PASS, with c and the
  support hypothesis fixed before quantifying over r.
- H^r(T_et,G) = 0: `IsZero ((Etale.cohomology
  AddCommGrpCat.{u + 1} T r).obj
  ((DerivedCategory.singleFunctor _ 0).obj G))`. PASS. I read
  LowerShriek.lean's `rightDerivedGlobalSections` and `cohomology`: these are
  R(Gamma) followed by the degree-r homology functor. `singleFunctor _ 0`
  places this same sheaf in degree zero. `IsZero` applies to an abelian-group
  object. No compact-support functor is involved.

Edge cases: empty T and G = 0 are admitted; no nonemptiness or reducedness
instance is present. For c = 0 precisely the positive degrees are asserted to
vanish. Degree zero is correctly excluded when c = 0, and negative degrees
cannot satisfy hr. There is no characteristic or invertibility restriction.
The arbitrary universe u agrees with the recorded scheme, support and
coefficient encodings; there is no independently smaller test-field universe.
There is no index family in this statement, hence no empty-index exception.

Independent duplicate searches (different wording from the worker):

- msearch LeanFinder: "Affine torsion sheaf etale cohomology bounded by
  transcendence degree of nonzero geometric stalks" returned eight algebraic
  etale-locus/support results, no sheaf-cohomology vanishing theorem.
- msearch Loogle: `"IsSepClosed", "IsZero"` returned zero hits.
- msearch Mathlib grep: `etaleSheafSupport|pointsOfTrdegLE|affine_support_vanishing`
  returned zero hits.
- Independent rg in Mathlib algebraic geometry, the upstream WeilConjectures
  tree, project lean/Sheaf and the upstream name map for affine/cohomology,
  support/vanishing and support/trdeg returned unrelated coherent/module
  vanishing and cohomology comparisons. A focused search for the two recorded
  support names, the proposed declaration and this blueprint id found only
  the existing support definition and its other users (closed-immersion
  essential image, constructible support and closed-point approximation),
  no existing copy of this theorem.

No H3/H4 mismatch was found. There are no new nodes, dependency modules or
statement corrections in this delivery. I preserved the correct Lean and
node signature. The one delivered theorem has exactly `sorry` as its proof;
no definition, private notation or local instance is introduced. Both
docstrings name Tag 0F0W and the blueprint id, and the theorem docstring
retains all five node proof steps and their dependency references. All
variables and the single universe are explicitly bound. The node's
`lean.statement` is verbatim the signature before `:= by`.

Second-reader validation: compiled the sole delivered module using server
`scompile.py`, nice 19, two threads, 60 seconds per file; the delivery dry run
also compiles the module and performs the stage-2 preflight.
