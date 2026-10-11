## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSupport` defines the set of points of bounded
residue-field transcendence degree and support for abelian etale sheaves and their derived
category. All three definitions have actual bodies; there are no theorems and no sorries.
No node statement was corrected, and no new nodes or dependency modules were necessary.

Clause-by-clause reading of `def-kun-support`:

- The field is `{k : Type u} [Field k]`, the scheme is `{X : Scheme.{u}}`, and its
  structure morphism is `p : X ⟶ Spec (.of k)`. This is the unbundled data of the
  dependency's `Scheme.Over`; it does not introduce an independent algebra structure.
- Finite type is `[LocallyOfFiniteType p] [QuasiCompact p]`, exactly the two predicates
  in the finite-type dependency. These are explicit binders of `Hom.pointsOfTrdegLE`.
- A point is an element `x : X`. The closed-point clause reuses `closedPoints X`, whose
  body is `Set.ofPred (IsClosed {·})`. It is described in the module rather than defined
  a second time. Neither E_a nor support is restricted to closed points.
- The residue field is `X.residueField x`. For its k-algebra structure the local instance
  `(p.residueFieldAlgebraMap x).toAlgebra` is used. The source declaration's full body is
  the composite of the canonical map k to the prime residue field of Spec k, the inverse
  of `Spec.residueFieldIso`, and `p.residueFieldMap x`. Thus it is precisely the field
  extension induced by p, rather than a free choice of algebra instance.
- Transcendence degree is `Algebra.trdeg k (X.residueField x)`. The nonnegative integer
  a is `a : ℕ`; the comparison is with `(a : Cardinal.{u})`. The set comprehension in
  `Hom.pointsOfTrdegLE` is exactly `{x | trdeg_k κ(x) ≤ a}`.
- The sheaf F is `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`. This is precisely
  the existing abelian-sheaf category in the recorded EtaleSheaves declaration.
- A geometric point is existentially quantified as `(Ω : Type u) (_ : Field Ω)
  (_ : IsAlgClosed Ω) (s : Spec (.of Ω) ⟶ X)`. The existential binders make these local
  instances, without an added separably-closed hypothesis (it follows from algebraic
  closedness). `s default = x` says that the unique point of Spec Ω lies over x.
- The stalk is `((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F`.
  Its nonvanishing is `¬ IsZero` of this abelian group object, the categorical meaning
  of a nonzero group, independent of how a zero group is represented. The existential
  quantifier is "some geometric point"; the independence lemma is not used.
- A derived object K is `DerivedCategory (Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1})`, with the source's global Grothendieck-abelian derived-category
  instance. Cohomology is the recorded `DerivedCategory.homologyFunctor` at degree q.
  `⋃ q : ℤ, etaleSheafSupport ((DerivedCategory.homologyFunctor _ q).obj K)` is exactly
  the union of the supports of all integer-indexed cohomology sheaves, without boundedness
  or torsion assumptions.

The support functions depend only on X, F and K, so are defined for every scheme. In the
node's context they apply to the given finite-type k-scheme and yield exactly the prescribed
sets. No conclusion or predicate is substituted for these definitions. There is no choice
of geometric point baked into the definition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over` is the structure-map
  data; the explicit p binder supplies that same data without a redundant instance.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`, reused without a wrapper.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.Spec.residueFieldIso`, `Scheme.SpecToEquivOfField`.
  `WeilConjectures.ZetaSeries`: `Scheme.Hom.residueFieldAlgebraMap`, read in full and used
  as the existing specialization of the residue-field dependency's induced embedding.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Sheaf.AlgebraicGeometry.EtaleSheaves`: its recorded abelian-sheaf category
  `CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` and global
  Grothendieck-abelian derived-category instance imported there.
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`; geometric points
  are the specialization of the recorded `Scheme.SpecToEquivOfField` with `IsAlgClosed`.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `GrothendieckTopology.Point.sheafFiber`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: its recorded unbounded abelian-sheaf
  `DerivedCategory` and `DerivedCategory.homologyFunctor` (the latter in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`). Both dependency modules
  were read in full; their new torsion predicates are not part of this node.

Edge cases checked before writing: a = 0 compares with cardinal zero without taking
`Cardinal.toNat` (which would have junk values at infinite cardinals); transcendental
residue fields are not excluded; the empty scheme gives empty sets because there is no
x; closedness is not imposed on support; a zero stalk is excluded by `¬ IsZero`; nonzero
stalks at any point enter by existence; the union ranges over all integers, including
negative degrees and unbounded complexes. There is no characteristic restriction. The
universe u is arbitrary; residue fields and their algebraic closures fit Type u, as in
Mathlib's geometric-point construction and the recorded dependencies, and abelian stalks
have the dependency's Type (u + 1) size.

Searches made (2026-10-11):

- msearch leansearch: "support of a sheaf is the set of points with nonzero stalk".
  Service returned Internal Server Error, recorded as unavailable, without a verdict.
- msearch leanfinder: "support of an etale sheaf of abelian groups and derived complex
  as points with nonzero geometric stalk". Eight hits, all etale-locus/module-support
  statements in `Mathlib.RingTheory.Etale.Locus`, not support of etale sheaves.
- msearch loogle: "Algebra.trdeg, Scheme.residueField". Zero hits, with unknown identifier
  `Scheme.residueField` (unqualified search name); full signatures were then read directly.
- msearch grep: "def .*support|trdeg.*residueField", all Mathlib. Returned ordinary
  function/finsupp support and unrelated definitions, no etale sheaf support or E_a.
- rg in Mathlib AlgebraicGeometry and CategoryTheory/Sites with
  `def .*support|trdeg.*residueField`: ideal-sheaf support only, not the requested notion.
- rg of support in WeilConjectures and lean/Sheaf: `WeilSheaf.support` in
  `WeilConjectures/WeilSheaf/Stalk.lean` is only a set of closed points for Weil sheaves,
  not all scheme points for arbitrary abelian etale sheaves. `ClosedPointField.lean`
  states a theorem involving trdeg zero, not a definition of E_a or support.
- grep -rn `def-kun-support` in WeilConjectures and rg in `dag/lean_names_upstream.json`:
  no match. rg for the three chosen declaration names in Mathlib, WeilConjectures and
  lean/Sheaf: no match before writing.

The locally absent blueprint source was opened read-only on the project server at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-support.md`.
Its definitions agree with the node. There is no STATEMENT-DISPUTED issue.

Server single-file compilation completed cleanly in 2.1 seconds, with no warnings.

## Second reading by E1

I reread the node statement and the module declaration by declaration. The node's objects and clauses render as follows: (1) a field and scheme structure morphism are `k : Type u`, `[Field k]`, `X : Scheme`, and `p : X ⟶ Spec (.of k)`; finite type is exactly `[LocallyOfFiniteType p] [QuasiCompact p]`; (2) closed points are represented by the existing `closedPoints X`; (3) the residue field and induced base algebra are `X.residueField x` and `(p.residueFieldAlgebraMap x).toAlgebra`; (4) `E_a(X)` is `Hom.pointsOfTrdegLE p a`, using `Algebra.trdeg k ... ≤ (a : Cardinal)`; (5) an abelian etale sheaf is `Sheaf X.smallEtaleTopology AddCommGrpCat`; (6) support is `etaleSheafSupport`, existentially over an algebraically closed field, a morphism `s : Spec Ω ⟶ X` with `s default = x`, and a nonzero `sheafFiber`; (7) for a derived object in `DerivedCategory (...)`, support is `etaleComplexSupport`, the union over all `q : ℤ` of supports of `homologyFunctor ... q`. Quantifier order and all clauses agree with the node.

The source and dependency declarations were checked. The Lean geometric-point quantifier uses `IsAlgClosed`, matching the node's algebraically closed geometric point. The finite-type hypothesis is the Mathlib pair used by the dependency definition. No extra characteristic, Noetherian, boundedness, torsion, or separatedness assumptions occur. Empty schemes and empty supports, `a = 0`, zero stalks, arbitrary residue transcendence degree, and negative/unbounded cohomological degrees are all covered. No mismatch was found and no source change was needed.

Searches (Mathlib, source repository, and project `lean/Sheaf`, via grep/LeanSearch/LeanFinder/Loogle) found no existing definition of these support or transcendence-degree strata notions; only unrelated module/ideal support and the separate `Algebra.trdeg` and residue-field declarations. The module compiled cleanly with `scompile.py`; its definitions have concrete bodies and no proofs or sorries.
