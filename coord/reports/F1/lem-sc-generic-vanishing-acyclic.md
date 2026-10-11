## Worker report

Record the existing declaration `AlgebraicGeometry.IsCurve.subsingleton_H_of_genericVanishing`
in `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison`, source lines 146–232.
No Lean module is delivered: the theorem already states precisely this node. Its docstring
and complete proof were read, together with `Scheme.affineOpenUnit` and
`Scheme.genericVanishingSieve` in the same module (lines 94–131). This is statement reuse,
not a claim that its transitive proof dependencies are sorry-free.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: inherited `{k : Type u} [Field k] [IsAlgClosed k]`.
- Curve C over k: inherited `{C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]`.
  The recorded `IsCurve` class extends `IsSeparated f`, `LocallyOfFiniteType f`, and
  `QuasiCompact f`, and has `topologicalKrullDim C ≤ 1`: separated, finite type,
  dimension at most one, exactly as the curve node says.
- Integral C: inherited `[IsIntegral C]`. This includes nonemptiness, reducedness,
  and irreducibility; no smoothness, properness, or exact dimension-one assumption.
- Abelian sheaf G on the small etale site: `(G : Sheaf C.smallEtaleTopology
  AddCommGrpCat.{u + 1})`.
- Every etale C-scheme V and section s: `∀ (V : C.Etale) (s : G.obj.obj (op V))`.
- Existence of an etale covering with the required local property:
  `C.genericVanishingSieve G s ∈ C.smallEtaleTopology V`.
  The arrows of this sieve are exactly morphisms `g : W ⟶ V` for which there is
  `U : C.NonemptyAffineOpens` satisfying
  `(C.affineOpenUnit U G).hom.app (op W) (G.obj.map g.op s) = 0`.
  Thus `G.obj.map g.op s` is the restricted section; the existential U supplies a
  nonempty affine open for each covering arrow separately, not a uniform open.
  A covering sieve contains a jointly surjective family; conversely the family
  in the node generates a covering sieve contained in this sieve. The equivalence
  follows from `Scheme.ofArrows_mem_smallEtaleTopology_iff` and upward closure.
- The unit `G → j_* j^{-1}G`: `affineOpenUnit` is precisely
  `(Etale.upperStarLowerStarAdjunction AddCommGrpCat (C.affineOpensDiagramι.app U)).unit.app G`.
  Here the canonical `Spec Γ(C,U) → C` is the inclusion of U under its canonical
  affine isomorphism; composing with that isomorphism gives `U.1.ι`.
  Vanishing is invariant under this identification, as also used at source lines 225–229.
- All q > 0: `(i : ℕ)` and `Subsingleton (Sheaf.H G (i + 1))`.
  Every positive natural degree is i+1; a subsingleton additive group is zero.
- No torsion assumption: there is no torsion binder or instance on G.

Dependency declarations read and used by the existing statement:

- `def-sc-curves`: `WeilConjectures.AlgebraicGeometry.Curve`, `AlgebraicGeometry.IsCurve`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-pbc-abelian-etale-sheaves`: `Mathlib.CategoryTheory.Sites.Sheaf`,
  `CategoryTheory.Sheaf`, specialized to `AddCommGrpCat`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`; `Scheme.Etale` is in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-pbc-inverse-image` and `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`.
- `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `Etale.cohomology` and
  `Etale.rightDerivedGlobalSections`. Its recorded note explicitly accepts the source's
  `CategoryTheory.Sheaf.H` convention for abelian-sheaf statements, with comparison
  to derived global sections at stage 3. `Sheaf.H` is Mathlib's Ext from the constant
  sheaf ULift ℤ, read in `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.

The source proof follows all four DAG proof steps: the affine-open kernel diagram has
colimit G by monicity and local surjectivity; pulling each kernel back to its affine
open gives zero by the adjunction triangle identity; finite-support acyclicity kills
its positive cohomology; filtered-colimit compatibility then kills the cohomology of G.
The existing kernel-colimit module of this project uses exactly the same covering
hypothesis; it does not duplicate the acyclicity conclusion.

Edge cases checked: the empty curve is correctly excluded by integrality; Spec k
is allowed because the curve dimension is at most one, not exactly one; its only
nonempty open is the whole scheme and the unit condition forces local zero sections.
The zero sheaf satisfies the hypothesis. On an empty etale V the zero section and
empty cover cause no extra condition. Degree one is included (i=0); degree zero is
not asserted to vanish. In particular a nonzero skyscraper sheaf can satisfy generic
vanishing while retaining nonzero global sections. No coefficient characteristic or
torsion restriction is imposed, and u is explicitly declared in the source.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py F1
lem-sc-generic-vanishing-acyclic`:

- LeanSearch: `generically vanishing etale sheaf curve higher cohomology vanishes`:
  unavailable, Internal Server Error (recorded unavailable, no mathematical verdict).
- LeanFinder: `An abelian etale sheaf on an integral curve whose sections vanish
  generically has zero higher cohomology`: eight unrelated cotangent/etale-algebra hits.
- Loogle: `CategoryTheory.Sheaf.H`: twelve hits for the cohomology API, zero-sheaf and
  injective-sheaf vanishing; no generic-vanishing theorem.
- Mathlib grep: `genericVanishing|subsingleton_H_of_generic|generic.*vanish`,
  `AlgebraicGeometry`: no hits.
- `rg -n 'genericVanishing|subsingleton_H_of_generic'` in the source repository:
  exact theorem at GenericComparison.lean:146, sieve definition at :121, applications
  at :261 and :288. In project `lean/Sheaf`: only the kernel-colimit statement/hypothesis.
- `grep -rn 'lem-sc-generic-vanishing-acyclic'` in the source repository: no hits;
  the exact theorem's docstring instead uses the older blueprint id
  `lem-sc-zero-generic-acyclic`. This does not change its mathematical statement.

The blueprint markdown path is not materialized in this read-only checkout. The node's
explicit alternative source place, GenericComparison.lean:140–232, is present and was
read in full. No node correction, missing dependency module, new definition node, or
statement dispute is required. Only the item's lean field is changed.

## Second reading by F1

I opened the node and the existing declaration
`AlgebraicGeometry.IsCurve.subsingleton_H_of_genericVanishing` in
`WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` (lines 140–232).
The introduced objects and their Lean rendering match item by item: the algebraically
closed field is `{k : Type u} [Field k] [IsAlgClosed k]`; the curve over it is
`{C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]`; integrality is
`[IsIntegral C]`; and the coefficient object is
`G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}`.  The hypothesis quantifies
over every `V : C.Etale` and `s : G.obj.obj (op V)` and is exactly
`C.genericVanishingSieve G s ∈ C.smallEtaleTopology V`.  This sieve renders the
node's etale covering, with each arrow carrying a nonempty affine open and vanishing
of the adjunction unit (`C.affineOpenUnit`, the recorded upper/lower-star unit).
The conclusion is exactly `Subsingleton (Sheaf.H G (i + 1))` for `i : ℕ`, hence
all positive degrees; no torsion, smoothness, properness, or extra finiteness
hypothesis occurs.  The inherited `IsCurve` assumptions provide the source's
separated finite-type curve and dimension bound.

Edge cases were checked: integrality excludes the empty scheme; a point curve is
allowed; the zero sheaf satisfies the sieve hypothesis; empty etale test objects
impose no extra condition; `i = 0` gives degree one while degree zero is not claimed;
and no characteristic or universe case is excluded.

I searched Mathlib and the project/source with LeanSearch, LeanFinder, Loogle, and
`rg`/grep (queries and results are recorded above).  No duplicate declaration was
found in Mathlib or `lean/Sheaf`; the exact source declaration is the reusable
existing theorem.  I found no mismatch and made no Lean-module change; the only
delivery change is the item's `lean` record pointing to that existing declaration.
