## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.OpenExchangeSeparableClosureReduction` as
`AlgebraicGeometry.Etale.isIso_openProductExchange_of_separableClosure`, with proof `sorry`.
Its helper `AlgebraicGeometry.Etale.openProductExchange` is a real construction of the
recorded canonical unbounded exchange evaluated at the degree-zero coefficient sheaf.
No stage-1 split is changed. The earlier worker's “already split and reviewed” diagnosis
concerned stage 1: the node is still missing its stage-2 `lean` record. This delivery adds it.

Read the entire standing stage-2 brief, stage-2 contract, delivery-errors H, worker role,
SETUP, GOAL, STATE, tools README, and the CompactObject example and node. Read the original
blueprint files for this item (order 1769) and def-kun-torsion-invertible (order 1680) on the
server; the local literature directory omits their regenerated contents. The item statement
agrees verbatim with its blueprint. Its expanded, reviewed proof is copied into the theorem
docstring as the five-step plan. No statement correction or disputed statement is needed.

Hypothesis and clause correspondence:

* “K a field”: `(K : Type u) [Field K]`.
* “K^sep”: `(L : Type u) [Field L] [Algebra K L] [IsSepClosure K L]`. This permits any
  model of the separable closure. Mathlib `IsSepClosure` means a separably closed separable
  extension; separability implies algebraicity. It adds no finite-degree or perfectness
  hypothesis. A separable closure has the same size as K, so the shared universe excludes
  no field or scalar-extension case up to the usual equivalence of models.
* “U, X, Y schemes over K”: `(U X Y : Over (Spec (.of K)))`. Their underlying schemes
  are `.left` and their structure maps are `.hom`.
* “j an open immersion over K”: `(j : U ⟶ X) [IsOpenImmersion j.left]`. Being a morphism
  in `Over` supplies the equation with the structure maps, rather than adding a hypothesis.
* “each of U, X, Y finite type over K”: the separate `LocallyOfFiniteType T.hom` and
  `QuasiCompact T.hom` binders for each of the three objects. Mathlib's finite-type notion
  is their conjunction. No properness, separatedness, smoothness or connectedness is added.
* “F an abelian sheaf on U_et”: `F : Sheaf U.left.smallEtaleTopology
  AddCommGrpCat.{u + 1}`. The coefficient size is the project's standard small-etale-site
  convention, with object universe u+1 and morphism universe u.
* “each stalk element torsion of order invertible in K”: `hF : IsTorsionOfInvertibleOrder K F`.
  Unfolding gives every separably closed geometric point, every element of its sheafFiber,
  and `∃ n : ℕ, (0 < n ∧ (n : K) ≠ 0) ∧ n • x = 0`. There is no common n.
  Testing separably closed points is equivalent to testing algebraically closed points:
  extending a separably closed point to an algebraic closure preserves its etale fiber.
* “form the cartesian square”: the definition constructs `Z = pullback Y.hom X.hom`,
  with `q = pullback.snd Y.hom X.hom`, then `V = pullback j.left q`, with
  `p = pullback.fst j.left q` and `h = pullback.snd j.left q`. The canonical
  `IsPullback.of_hasPullback j.left q` supplies the square. This is a chosen model of
  Y×_K U: a compatible pair `(u,(y,x))` necessarily has x=j(u), and therefore is exactly
  a compatible pair `(y,u)`. No extra object, map or cartesianness assumption is quantified.
* “beta is the exchange morphism”: `openProductExchange` is
  `(exactDerivedBaseChangeMap AddCommGrpCat square.toCommSq).app
  ((DerivedCategory.singleFunctor _ 0).obj F)`. Its explicit result type is precisely
  `q⁻¹ Rj_* F ⟶ Rh_* p⁻¹ F`. This is the adjunction mate of the canonical square
  comparison, not an arbitrary arrow or a chosen object isomorphism.
* “the analogous map after scalar extension”: write r for
  `Spec.map (CommRingCat.ofHom (algebraMap K L))`. The `hL` binder uses
  `(Over.pullback r).map j`, `(Over.pullback r).obj Y`, and
  `(upperStar AddCommGrpCat (pullback.fst U.hom r)).obj F`. The implicit U and X of the
  exchange are the same functor's images of U and X. Thus the entire square, its open
  immersion and its coefficient sheaf have been extended, not just the original arrow.
  The chosen iterated pullbacks identify canonically with the scalar extension of Z,V;
  the universal property identifies their projections. No independent scalar-extended
  square or compatibility hypothesis is introduced.
* “if beta_Ksep is an isomorphism, beta is”: `hL : IsIso (...)` and the conclusion
  `IsIso (openProductExchange j Y F)`.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`;
  imported through finite type, the recorded node declaration.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and the canonical
  `IsPullback.of_hasPullback`. The products and both projections use those declarations.
* `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed` and `IsSepClosure`. The dependency
  record is completed to name the second existing declaration too (see below).
* `Mathlib.CategoryTheory.Sites.Sheaf`, `CategoryTheory.Sheaf`, with
  `AlgebraicGeometry.Scheme.smallEtaleTopology`.
* `Mathlib.AlgebraicGeometry.Sites.EtalePoint`, `Scheme.pointSmallEtale`, and
  `Mathlib.CategoryTheory.Sites.Point.Basic`, `GrothendieckTopology.Point.sheafFiber`.
  Read their docstrings and full definitions, not just their names.
* `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`,
  `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`. Read both that definition and
  `exactDerivedSquareUpperStarIso`: exact inverse image descends termwise, and the
  unbounded exchange is its adjunction mate for exact pullback and total derived pushforward.
* `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, read with `scompile.py --source`,
  provides the recorded def-weil-pbc-etale-sheaves dependency. Its torsion notion is
  `CategoryTheory.Sheaf.IsTorsion` from
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`; read that definition
  and reused it rather than defining ordinary torsion again.
* The new dependency module's five declarations are listed below and in its `lean` record.

The already stated proof dependencies are imported without `public`:
`EtaleInverseImageModulesExact.etaleInverseImageModulesExact` (declaration namespace
`AlgebraicGeometry`), `GeometricStalkAsPullback.Scheme.geometricStalk_as_pullback`,
`DerivedInverseImageComposition.Etale.derivedInverseImageComposition`, and
`Paper.ExchangeIdentityPasting.Etale.derivedExchange_identity_pasting`. The first three
module names have prefix `Sheaf.AlgebraicGeometry`, and the last `Sheaf.Paper`;
all declaration namespaces have prefix `AlgebraicGeometry`. Their full declarations and
proof docstrings were read. The other proof-only prerequisites have no recorded Lean
module in the base and are therefore left to later stage-2 deliveries. Nothing in the
statement requires their proofs or an unstated canonical construction.

Edge cases checked before writing: U empty, X empty, Y empty, F zero, j the identity,
K already separably closed with L=K, characteristic zero, positive characteristic, and
stalkwise annihilators unbounded over F. All remain allowed. In positive characteristic
p, `(n : K) ≠ 0` excludes p-divisible n; it does not exclude the zero stalk element,
which is killed by n=1. In characteristic zero every positive n is allowed. No cohomology
boundedness, nonempty scheme, nonzero sheaf or single annihilator is imposed. The
cohomology property in the dependency quantifies all q : ℤ, including negative degrees.

Searches, with actual outcomes:

* `msearch.py leanfinder`, query “The etale derived open immersion exchange map is an
  isomorphism if it becomes an isomorphism over a separable closure”: eight hits on etale
  ring maps and standard etale presentations, none on this derived exchange reduction.
* `msearch.py loogle`, `IsSepClosure, IsIso`: zero hits, unknown identifier IsIso.
* `msearch.py grep`, `sep.*[Cc]los.*[Ii]so|[Ii]so.*sep.*[Cc]los|[Tt]orsion.*[Ii]nvertible`
  in AlgebraicGeometry: zero hits.
* `msearch.py leansearch`, “torsion abelian sheaf with stalk element orders invertible in
  a field”: service unavailable (Internal Server Error), recorded as unavailable.
* `msearch.py leanfinder`, “torsion abelian sheaf stalk annihilator positive integer
  invertible in a ground field”: eight hits about module stalks, support and germs, none
  about the field-dependent abelian-etale torsion predicate.
* `msearch.py loogle`, `CategoryTheory.Sheaf, Nat`: twelve hits on H, H', cohomology
  presheaves and cohomology maps, none defining orders invertible in a field.
* `msearch.py grep`, `Torsion.*Invertible|Invertible.*Torsion|etaleNTorsion|openProductExchange`
  over Mathlib: zero hits. Also `separable.*closure|separably.*closed` in CategoryTheory:
  zero hits.
* `rg` of the upstream `WeilConjectures` and side `lean/Sheaf` for
  `torsion.*[Ii]nvertible|[Ii]nvertible.*[Tt]orsion` found upstream
  `Scheme.IsTorsionSheafOfInvertibleOrder` in
  `SixFunctors/Etale/BaseChangeTheorems/TorsionSheaf.lean`. Read its full signature and
  docstring: it takes sheaves with ModuleCat coefficients and invertibility on a general
  scheme S, so it cannot directly state this node on AddCommGrpCat sheaves.
* Read the existing `allowableTorsionSheafProperty` in
  `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`: it parametrizes a set of
  allowed primes, not this node's integer index set or its specified annihilator predicate.
  The new field-specific predicate specializes the same stalkwise concept but is the
  exact positive-integer formulation of this unstated dependency, with no private
  replacement for any recorded dependency declaration.
* `rg` of the upstream and side library for
  `openProductExchange|IsTorsionOfInvertibleOrder|invertibleTorsionOrders|etaleNTorsion`:
  zero hits. `grep -rn` of the item ID in upstream: zero hits.
* Read upstream `AlgebraicGeometry/Sites/EtaleTorsion.lean` and
  `CategoryTheory/Sites/Point/Torsion.lean`: ordinary torsion exists and is not redefined.
* `scompile.py --source Sheaf.AlgebraicGeometry.TorsionInvertible` and
  `...TorsionInvertibleOrders` confirmed no such current server module; the actually
  needed existing EtaleSheaves source was found and used through the same wrapper.

Validation: `scompile.py Q31 lem-kun-0f1h-sep-reduction` compiled both delivered files
separately, in dependency order, cleanly with the default 60-second per-file limit.
`deliver2.py Q31 lem-kun-0f1h-sep-reduction --no-push` printed OK: commit
5364fe1e16 compiled and passed preflight except for the independent second reading, which
the second reader supplies. Nothing was pushed. The wrapper is rerun after this report update.

## Dependency modules

`def-kun-torsion-invertible`: this genuine dependency has no Lean record or Mathlib match.
The human's 2026-10-16 instruction requires stating it in this delivery. Its node is copied
with only `lean` changed. `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders` defines
`invertibleTorsionOrders` as the set of positive n with nonzero image in K,
`invertibleTorsionOrderDvd` as divisibility on its elements, `etaleNTorsion` as the kernel
of n times the identity, `IsTorsionOfInvertibleOrder` as the exact stalkwise annihilator
condition, and `HasTorsionCohomologyOfInvertibleOrder` by the same condition on every
homology sheaf. Ordinary torsion is the dependency's recorded `Sheaf.IsTorsion`, not
another definition. The divisibility relation uses natural-number divisibility, not the
usual numeric ordering. Every definition has actual data; there are no additional sorries.

`def-kun-separably-closed`: a record-only repair under §1(B). The old Lean record names
only `IsSepClosed`, although the node also defines a separable closure. The same existing
Mathlib module declares `IsSepClosure`, with separably closed top field and separable
extension (hence algebraic). Both names are now recorded, with `existing: true` and a
`lean.note` explaining the missing part. Neither definition is reintroduced.

## Second reading by Q31

I reread the item node, the corrected dependency records, the two Lean modules, the
blueprint source, and Stacks Project Tags 0F1H (`lemma-kunneth-localize-on-X`) and 0F1C
(`lemma-base-change-field-extension`). The item is the reduction implication, rather than
the unconditional theorem proved later by Tag 0F1H.

The node's objects and hypotheses match the file as follows:

* A field K is `(K : Type u) [Field K]`; a chosen separable closure is `(L : Type u)
  [Field L] [Algebra K L] [IsSepClosure K L]`. `IsSepClosure` is the recorded Mathlib
  notion, and allows the case L = K when K is separably closed.
* The three K-schemes U, X, Y are the bundled objects
  `(U X Y : Over (Spec (.of K)))`. The map `j : U ⟶ X` is over K and
  `[IsOpenImmersion j.left]` renders the open-immersion hypothesis.
* Finite type for each of U, X, Y is exactly the paired binders
  `[LocallyOfFiniteType T.hom] [QuasiCompact T.hom]`, with no properness,
  separatedness, smoothness, or connectedness assumption.
* The abelian sheaf is
  `F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}`. Its stalkwise
  invertible-order torsion is `hF : IsTorsionOfInvertibleOrder K U F`.
  The explicit `U` is the K-scheme on which the sheaf lives; the dependency module now
  requires `(T : Over (Spec (.of K)))`, so this hypothesis cannot be supplied for a
  scheme unrelated to K.
* The cartesian square is the chosen pullback `pullback Y.hom X.hom`, with `q` its
  second projection, and the pullback of `j.left` along `q`, with `p` its first and
  `h` its second projection. This is rendered by `openProductExchange`; its definition
  is the component of `exactDerivedBaseChangeMap` on
  `DerivedCategory.singleFunctor _ 0` applied to `F`, so it is the canonical exchange
  morphism of `def-kun-unbounded-exchange`.
* Scalar extension is along
  `Spec.map (CommRingCat.ofHom (algebraMap K L))`. The hypothesis `hL` applies
  `openProductExchange` to `((Over.pullback r).map j)`, `((Over.pullback r).obj Y)`,
  and the coefficient pullback
  `((upperStar ... (pullback.fst U.hom r)).obj F)`. Thus it is precisely the analogous
  map in the scalar-extended square, not an arbitrary map or an object-level isomorphism.
* The conclusion `IsIso (openProductExchange j Y F)` is exactly that the original
  exchange morphism beta is an isomorphism. The quantifier order is the node's order:
  K, L, the three schemes, j, finite-type instances, F, hF, hL, then the conclusion.

The dependency declarations were opened individually. `IsOpenImmersion`,
`LocallyOfFiniteType`, `QuasiCompact`, `pullback` and its projections, `Sheaf` on the
small etale site, geometric `sheafFiber`, `IsSepClosure`, `exactDerivedBaseChangeMap`,
and the recorded inverse-image/exchange modules are the same notions as the dependency
nodes. The `def-kun-torsion-invertible` module was the one mismatch: its first version
declared `IsTorsionOfInvertibleOrder K` for an arbitrary `{T : Scheme}` and therefore
dropped the node's hypothesis that T is a K-scheme. I changed it to
`IsTorsionOfInvertibleOrder K (T : Over (Spec (.of K))) ...`; the cohomology predicate
was transported to the same bundled K-scheme interface, and the item now passes `U`.
The corresponding dependency-node `lean.statement` was updated verbatim. No item
hypothesis or conclusion was weakened or strengthened.

Edge cases checked are empty U, X, or Y where the relevant morphisms exist; the zero
sheaf; `j` the identity; K already separably closed with L = K; characteristic zero;
positive characteristic p, where the predicate permits exactly orders with nonzero image
in K; and stalkwise annihilators with no common bound. The definitions remain meaningful
for all of them. In particular, n = 1 handles the zero stalk element, and no nonempty-
scheme or uniform-annihilator assumption was added. The universe uses one `u` for fields,
schemes, and geometric points and the standard `AddCommGrpCat.{u + 1}` coefficient size,
so the node's cases are not excluded by a smaller test universe.

I repeated the existing-definition searches with LeanFinder, Loogle, LeanSearch, and
grep over Mathlib, the read-only slopmaster2 source, and `lean/Sheaf`, using the queries
recorded in `searches.jsonl`. The only similarly named source declaration is
`Scheme.IsTorsionSheafOfInvertibleOrder`, which uses ModuleCat coefficients and a
different scheme-level class; it does not state this abelian, field-dependent predicate.
No exact `openProductExchange` or separable-closure reduction declaration exists.
The Mathlib and source declarations used by the item are therefore reused, while the
field-specific dependency is the one new module required by the node.

After the repair, `scompile.py` compiled both delivered files separately with no errors
or warnings beyond the theorem's permitted `sorry`. The delivery dry run is rerun after
this report update; no statement correction is needed.
