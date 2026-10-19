## Worker report

The repaired module `Sheaf.AlgebraicGeometry.ZModSheafInvertibleOrders` states
`AlgebraicGeometry.Scheme.zmodSheaf_hasFieldInvertibleOrders`, with proof `sorry`.
Every sheaf of modules over the constant Z/nZ ring sheaf on an arbitrary K-scheme's
small etale site has orders invertible in K, whenever n belongs to I_K.
The node's mathematical statement and dependencies are unchanged.

## Repair of return L

The immutable-head compile imported the published module
`Sheaf.AlgebraicGeometry.InvertibleTorsionOrders` but referred to
`Scheme.invertibleTorsionIndices` and
`Scheme.IsTorsionEtaleSheafOfFieldInvertibleOrder`, which that module does not declare.
I read the current `def-kun-torsion-invertible` node and its full published module,
including a fresh `scompile.py --source` read. Its canonical declarations are
`AlgebraicGeometry.Etale.invertibleTorsionOrders` and
`AlgebraicGeometry.Etale.IsTorsionOfInvertibleOrder`.

The theorem now imports that module and uses both canonical declarations directly.
The index's underlying natural number is `n.val`. Its base is now bundled as
`T : Over (Spec (.of K))`, as the canonical conclusion expects; `T.left` is the
underlying scheme and `T.hom` its specified K-structure. This quantifies over exactly
all K-schemes, as the old scheme-plus-Over-instance form did. There is no new
hypothesis, coefficient restriction, or statement correction.

The sandbox's obsolete `FieldInvertibleTorsion` module and dependency-node copy
have been removed from the delivery. The published dependency is used as recorded;
no alternative order predicate or dependency replacement is delivered. The stored
Lean signature was updated verbatim. A line-length warning found during the repair
was fixed by wrapping the docstring. The prior second reading concerned the old
interface; a second reader must review this repaired version independently.

Hypotheses and conclusion, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| K is a field | `(K : Type u) [Field K]` |
| n belongs to I_K | `(n : Etale.invertibleTorsionOrders K)` |
| n is positive and invertible in K | The recorded set is `{n : ℕ | 0 < n ∧ (n : K) ≠ 0}`; a nonzero field element is a unit |
| Lambda is Z/nZ | `ULift.{u + 1} (ZMod n.val)` with its transported ring structure |
| Every scheme T over K | `(T : Over (Spec (.of K)))`, including its structure map |
| The small etale site | `T.left.smallEtaleTopology` |
| Constant coefficient ring sheaf | `(constantSheaf T.left.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of (ULift.{u + 1} (ZMod n.val)))` |
| Every sheaf of Lambda-modules | `F : SheafOfModules.{u + 1} (...)`, with no finiteness or constructibility restriction |
| Underlying abelian sheaf | `(SheafOfModules.toSheaf _).obj F` |
| Has orders invertible in K | `Etale.IsTorsionOfInvertibleOrder K T ((SheafOfModules.toSheaf _).obj F)` |

The canonical conclusion quantifies over every separably closed geometric point,
every element of its abelian stalk, and a positive annihilator nonzero in K which
may depend on that element. Algebraically closed geometric points are included;
separably closed points give the same etale stalk criterion. The stalk condition
also implies local torsion on the small etale site (the recorded torsion-sheaf
characterization). The proof docstring retains the direct local-torsion argument:
sections are already killed by n, so the identity covering suffices. The conclusion
does not impose a common annihilator even though n supplies one in this case.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`:
  `AlgebraicGeometry.Etale.invertibleTorsionOrders`,
  `AlgebraicGeometry.Etale.IsTorsionOfInvertibleOrder`. The former is exactly
  the positive nonzero field-cast condition; the latter uses the canonical
  `Scheme.pointSmallEtale` / `sheafFiber` abelian stalks.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
  The covering-family criterion is `ofArrows_mem_smallEtaleTopology_iff`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`:
  the recorded abelian/sheaf conventions and imported `CategoryTheory.Sheaf.IsTorsion`.
  The current module was read with `scompile.py --source` because the old source
  checkout does not contain it.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` transparently abbreviates Mathlib's
  `SheafOfModules`. `SheafOfModules.toSheaf` is the canonical underlying abelian sheaf.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  the sheafification of the constant presheaf. The proof imports
  `Mathlib.CategoryTheory.Sites.Sheafification` for `toSheafify` and
  `presheafToSheaf`, and `Mathlib.CategoryTheory.Sites.Point.Basic` for the
  colimit description of stalks.
- `Mathlib.Data.ZMod.Basic`: `ZMod`; the elementary annihilation calculation is
  `ZModModule.char_nsmul_eq_zero`, whose full declaration was read.

The docstring follows all three proof steps of the node: the canonical unital
constant-section map sends n times one to zero, the module axioms kill every
section by n, and additivity plus the stalk colimit universal property kills
every stalk element by n. Positivity gives local torsion and the allowed
annihilator. No proof is supplied beyond the required `sorry`.

Edge cases checked:

- n = 0 is excluded exactly by I_K's positivity; n = 1 is included. For n = 1
  the coefficient ring and every unital module are zero; no Nontrivial assumption
  excludes this case.
- In characteristic p, exactly integers with zero field cast are excluded.
  In characteristic zero every positive n is allowed.
- Empty K-schemes and empty geometric-point families remain allowed.
- Arbitrary infinite and nonconstructible module sheaves remain allowed. No
  finite-type, smoothness, separatedness, properness or quasi-compactness binder
  has been introduced.
- The site has object universe u+1 and morphism universe u; abelian groups and
  coefficients have universe u+1. `ULift` changes only the coefficient universe.
  No equality of the site's object and morphism universes is imposed.

Searches repeated for this repair (2026-10-16), with results in `searches.jsonl`:

- LeanFinder: "Every sheaf of modules over the constant ring sheaf ZMod n has
  torsion orders invertible in a field K if n is positive and nonzero in K".
  Eight hits, including `AddMonoid.IsTorsion.module_of_finite`,
  `ZModModule.char_nsmul_eq_zero`, and torsion-subgroup module structures;
  none states this constant-ring-sheaf theorem.
- Loogle: `ZMod, Module`. Twelve hits including
  `ZModModule.char_nsmul_eq_zero` and `ZMod.instSubsingletonModule`;
  these concern scalar annihilation and module structures only.
- Mathlib grep: `IsTorsionSheafOfInvertibleOrder|char_nsmul_eq_zero`.
  Five hits, the scalar-annihilation lemma and its uses; no complete sheaf theorem.
- `rg` in upstream `WeilConjectures` and the project's `lean/Sheaf` for
  `zmodSheaf_hasFieldInvertibleOrders|invertibleTorsionOrders|IsTorsionOfInvertibleOrder`
  found the published canonical dependency and its other consumer, but no copy
  of this theorem. The original delivery's upstream search also inspected
  `Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero`; it takes
  ModuleCat-valued sheaves and not this constant-ring-sheaf module encoding.
- Earlier LeanSearch requests returned service errors; they were not treated
  as absence evidence.

No statement dispute, new node, dependency repair, or statement correction is needed.
Validation uses the prescribed file-only `scompile.py` and then
`deliver2.py Q10 lem-kun-zn-sheaf-invertible-orders --no-push`.

## Second reading by Q10

Independent second reading of the repaired version, 2026-10-16. I opened the
sandbox node and Lean file, all three statement-dependency node records and their
source declarations, and the proof-dependency records. I read the original
blueprint files in
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`, including this
lemma, `def-kun-torsion-invertible`, and `def-weil-pbc-etale-sheaves`. The recorded
`literature/blueprint/` path is absent in the shared clone; these original files
supply the source text. This item cites a blueprint lemma rather than a Stacks
lemma. I also read the Stacks `etale-cohomology.tex` introduction and torsion
section: its quasi-compactness and quasi-separatedness assumptions belong to
cohomology/direct-image results, not to this elementary coefficient assertion.
There is no hidden finiteness assumption to add here.

The source statement, broken into its objects, hypotheses and conclusion, matches
as follows. All verdicts are PASS.

| Source item | Lean rendering and independent verdict |
| --- | --- |
| Arbitrary field K | `(K : Type u) [Field K]`; no algebraic closure or characteristic restriction. |
| Positive integer n in I_K | `(n : Etale.invertibleTorsionOrders K)`; I opened the definition, `{n : ℕ | 0 < n ∧ (n : K) ≠ 0}`. Over a field this is exactly positivity and invertibility. |
| Lambda = Z/nZ | `ULift.{u + 1} (ZMod n.val)` with the transported ring structure; the lift changes size only. |
| Every K-scheme T, with its K-structure | `(T : Over (Spec (.of K)))`; `T.left` is arbitrary and `T.hom` is its structure morphism. No property of the morphism is assumed. |
| T's small etale site | `T.left.smallEtaleTopology`; I read its definition and `ofArrows_mem_smallEtaleTopology_iff`, which gives the jointly surjective covering families. |
| Lambda's constant ring sheaf | `(constantSheaf T.left.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of (ULift.{u + 1} (ZMod n.val)))`; `constantSheaf` is the constant presheaf followed by sheafification. |
| Every sheaf of Lambda-modules in the node's sense | `F : SheafOfModules.{u + 1} (...)`; I opened Mathlib's structure: a presheaf of sectionwise modules whose underlying abelian presheaf is a sheaf. This is exactly the constant-ring-sheaf convention in the dependency node. |
| The underlying abelian sheaf has orders invertible in K | `Etale.IsTorsionOfInvertibleOrder K T ((SheafOfModules.toSheaf _).obj F)`; I read `toSheaf` and the predicate bodies. The former retains the underlying abelian presheaf and its sheaf proof. The latter quantifies over every separably closed geometric point, then every stalk element, then an allowed positive annihilator. |

The conclusion's existential annihilator is inside the stalk-element quantifier;
no common annihilator is required by the conclusion. The proof can use the fixed
n for every element. Separably closed geometric points compute the same small
etale stalks and include algebraically closed geometric points. I opened
`Scheme.pointSmallEtale` and `GrothendieckTopology.Point.sheafFiber`: the former's
fiber consists of lifts of the geometric point to etale neighborhoods, and the
latter restricts the presheaf colimit fiber functor to sheaves. Local torsion is
implicit in this canonical predicate by the geometric-stalk characterization,
not an omitted extra hypothesis. Here the proof also supplies local torsion
directly using n and the identity cover.

Edge cases: n = 0 is excluded exactly by I_K; n = 1 is admitted, including its
zero coefficient ring and zero unital modules. Zero sheaves and empty schemes
are admitted. There is no index-set binder or nonemptiness assumption; the empty
geometric-point family is harmless. Characteristic p excludes precisely positive
integers divisible by p, and characteristic zero admits all positive integers.
There is no constructibility, finite generation, Noetherian, finite-type,
separatedness or quasi-compactness hypothesis. The arbitrary universe u follows
the recorded dependency convention: schemes and geometric-point fields have
universe u, the site has object universe u+1 and morphism universe u, and module
and abelian-sheaf values have universe u+1. No equality of site universes or
extra smallness instance is imposed. Every variable and universe is explicitly
bound.

Independent searches on 2026-10-16:

- LeanFinder, "Sheaves of modules over a constant ring of positive characteristic
  are torsion abelian sheaves killed by that characteristic": eight hits,
  including `AddMonoid.IsTorsion.module_of_torsion`,
  `AddMonoid.IsTorsion.module_of_finite`, and sheaf-module abelian instances.
  None states this etale constant-ring-sheaf result.
- Loogle, `Module, ZMod, _ • _ = 0`: four hits, including
  `ZModModule.char_nsmul_eq_zero`, two constructions of ZMod-module structures,
  and `ModN.liftEquiv'`. I read the forward annihilation declaration; it supplies
  the scalar calculation only.
- LeanSearch, "Every sheaf of modules over the constant ring Z/nZ has geometric
  stalks annihilated by n": service returned Internal Server Error. This is
  recorded as unavailable and is not evidence of absence.
- Mathlib grep, `char_nsmul_eq_zero` together with both orders/sheaf word orders:
  five hits, all scalar annihilation or its uses. Direct searches of the
  sheaf-of-modules directory and `ConstantSheaf.lean` for annihilation, torsion
  and nsmul found no corresponding theorem.
- `rg` of upstream `WeilConjectures`, the shared upstream modules, and `lean/Sheaf`
  for `of_natCast_eq_zero`, the two invertible-order predicate names, and the
  proposed declaration found the published dependency and the upstream theorem
  `Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero`. I opened both its
  full signature and its predicate's signature: it takes
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and concludes the upstream
  module-valued predicate with units in global sections of a base scheme. It
  does not take `SheafOfModules` over the constant ring sheaf or conclude the
  recorded abelian-sheaf predicate. It therefore cannot replace this module
  verbatim. No duplicate declaration in the node's encoding was found.

No mismatch remains in the repaired version; I changed no Lean declaration or
node field. In particular I verified the worker's repair of the former dependency
name error against the actual published `InvertibleTorsionOrders.lean`, rather
than trusting its names or report. There are no new nodes or dependency modules
to audit and no `statement_change` requiring a citer audit. The single theorem
has only `sorry` as its proof; there are no hollow definitions or proved helpers.
Its docstring follows all three node proof steps: unital constant sections and
module axioms kill sections, the stalk-colimit universal property kills stalks,
and positivity and the field cast condition provide torsion and an allowed
annihilator. Source/blueprint markers and all line lengths check. The node's
`lean.statement` is verbatim equal to the file's signature.
