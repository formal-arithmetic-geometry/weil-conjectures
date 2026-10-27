## Worker report

The delivery states `AlgebraicGeometry.SchemeAction.finite_constant_torsor_map_isModuliStack`
in `Sheaf.AlgebraicGeometry.FiniteConstantTorsorMapEtaleStack`. Its sole proof is `sorry`.
It defines no object and introduces no axiom. The natural-language node statement and
its seven-step proof remain unchanged. The only other node change is adding the
already landed `def-sfb-etale-scheme-action-torsor-groupoid` to `stmt_deps`, as authorized
for landed dependencies by the current stage-2 brief. No new nodes or dependency modules
are needed. There is no statement dispute or correction.

Source read: `literature/stacks-project/examples-stacks.tex`,
`lemma-group-quotient-stack-in-groupoids` (0370), including its preceding definition
of objects and cartesian arrows, and `lemma-finite-etale-stack` (0BLZ). The former
proves effectivity by torsor descent followed by gluing the map; the latter supplies
the finite étale scheme descent used in this node's finite constant-group variant.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary base scheme is `{S : Scheme.{u}}`. `universe u v` and explicit binders
  implement the metatheoretic `def-weil-size-convention`; there is no field or
  Noetherian hypothesis. The group universe `v` is independent of the scheme universe.
- A finite abstract group is `(H : Type v) [Group H] [Finite H]`, with no abelianness,
  cardinality choice, decidable equality, or characteristic restriction.
- `G` is the presentation of the constant group scheme `H_S`. Specifically,
  `(G : Over S)`, `incl : H → (Over.mk (𝟙 S) ⟶ G)` and
  `hincl : IsColimit (Cofan.mk G incl)` say exactly that it is the coproduct of
  copies of the terminal S-scheme, indexed by H. Its group structure `[GrpObj G]`
  has `hincl_one` and `hincl_mul`, expressing the unit and multiplication of H
  on those coprojections. Multiplication on the product is determined by its
  H × H components; inversion is consequently the component permutation h ↦ h⁻¹.
  This is the coproduct-presentation convention in brief-stage2 and the same
  presentation used by the landed downstream `actionGroupoid_quotient_criterion`.
  It does not replace the constant group by an arbitrary finite étale group scheme.
  No `Nonempty` choice, arbitrary comparison map, or assumed stack property is used.
- `(V : Over S) [ModObj G V]` is the arbitrary S-scheme with its left action. Since
  G is the constant coproduct, an internal action is precisely the family of
  S-automorphisms indexed by H obeying the group law. Every abstract H-action
  gives this map by the coproduct universal property on G ×_S V = coproduct_H V;
  restriction to its summands recovers the H-action. Thus this presentation
  adds no restriction to the action in the node.
- `etaleTorsorGroupoid G V` is the landed definition, not a newly copied category.
  Its `TorsorObject.base` is T, `space` is the actual S-scheme P,
  `projection` is P → T, and `action : ModObj G space` with `invariant` is
  precisely a left H_T-action over T. Restriction of G along T gives H_T.
- `IsEtaleLocallyTrivial G V` quantifies over a covering sieve for
  `Scheme.etaleTopology.over S`. For each W → T in it, the map q from G ×_S W
  has a cartesian square and satisfies q(gh,w) = g q(h,w) on every test scheme.
  The square means q identifies this trivial torsor with P ×_T W, equivariantly.
  Covering sieves are equivalent to the jointly surjective étale families of
  the node. The existing `local_trivial` fppf proof field adds no mathematical
  hypothesis, since every étale cover is fppf.
- `TorsorObject.map` and `equivariant` give the specified equivariant S-map P → V.
- The full-subcategory arrows are `TorsorHom`, with a base arrow, a scheme map,
  `cartesian`, `equivariant`, and `commutes : map ≫ Y.map = X.map`.
  Over an identity base arrow a cartesian square is precisely an isomorphism;
  these are exactly the H_T-equivariant T-isomorphisms with f' b = f.
  The automorphisms are retained; objects are not replaced by isomorphism classes.
- Pullback is encoded by the same actual cartesian scheme squares. Over S,
  Mathlib's cartesian monoidal structure uses `Limits.pullback`; its canonical
  pullback object has the projections described by `def-pc-fibre-product`.
  The `IsFibredInGroupoids` conjunct of the conclusion asserts existence of
  these cartesian lifts over every base arrow and their strong universal property.
  The induced map to V is forced by the arrow's `commutes` equation.
- `IsModuliStack (etaleTorsorGroupoid G V)` uses exactly the dependency's total
  category definition. Its second conjunct quantifies over every test S-scheme
  T, every covering sieve in `Scheme.etaleTopology.over S`, and every descent
  diagram over that sieve. A cocone with point over T and all specified base
  maps is required to be colimiting. As the dependency docstring explains, for
  a category fibred in groupoids this is effectiveness of all object descent
  data and unique gluing of isomorphisms. It includes the given overlap cocycle,
  rather than only the existence of locally isomorphic objects. Quantification
  over all T includes every further base change T' → T, as required for the
  entire isomorphism presheaf to be a sheaf.
- No hypothesis concerns freeness on V, finite type of S or V, or invertibility
  of the order of H. In particular these cases are included, not deduced from
  an extra finiteness or free-action assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, the
  affine-local étale ring-map definition used by the topology.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` and `pullback.lift`;
  the scheme pullback exists by the public geometry imports.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsModuliStack` and `CategoryTheory.IsFibredInGroupoids`.
- `Sheaf.AlgebraicGeometry.EtaleSchemeActionTorsorGroupoid`:
  `AlgebraicGeometry.SchemeAction.etaleTorsorGroupoid` and `IsEtaleLocallyTrivial`.
  Their public dependency `Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids`
  supplies `TorsorObject`, `TorsorHom`, `IsLocallyTrivial` and `torsorGroupoid`.
- Mathlib's `GrpObj`, `ModObj`, group operations on `Hom(-,G)`, and the cartesian
  monoidal structure on `Over S` give exactly the internal group/action notation.
  `Cofan.mk` and `IsColimit` express the actual coproduct universal property.

The proof-dependency imports are private (`import`, not `public import`):
`Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` (fpqcCover_of_smallEtaleCover),
`WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover` (isFinite_of_fpqc_cover),
`WeilConjectures.AlgebraicGeometry.FpqcDescentEtale` (etale_of_fpqc_cover),
`WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent` (finiteEtaleDescent), and the
Mathlib modules `AlgebraicGeometry.Limits`, `AlgebraicGeometry.Morphisms.Basic`,
`AlgebraicGeometry.Sites.Fpqc`, `AlgebraicGeometry.Sites.MorphismProperty`.
These carry all recorded proof dependencies: coproduct spectra and disjoint
scheme coproducts, source-local étaleness and target-local finiteness and
finite-étaleness, fpqc subcanonicity, and stability of the étale precoverage
under base change and composition. None imports this theorem or its downstream
quotient-criterion module. The seven-step theorem docstring records every proof
step and the node IDs used, leaving that proof to stage 3.

Edge cases checked before writing:

- Empty S or T: its coproduct of H copies is empty, the action identities still
  make sense, and the empty covering family gives the required empty descent.
  No nonempty-point or inhabited-cover assumption occurs.
- The trivial group: the constant group is S; torsors are locally and hence
  globally the base, and the claim specializes to gluing maps to V.
- A nonfaithful or trivial H-action on V: the category retains torsor
  automorphisms and still has the asserted stack property.
- V empty: objects exist exactly on the appropriate empty bases; no existence
  of objects over every nonempty T is asserted by the stack axiom.
- Characteristic dividing |H|: constant finite groups remain étale; this is
  not a μ_n torsor or an order-invertibility statement.
- Nonseparated, non-quasi-compact and non-finite-type bases or action schemes
  are allowed. No restriction was introduced to make fpqc descent apply.
- An arbitrary finite group in `Type v` is small in every required scheme
  universe; the independent universe binder imposes no equality of sizes.

Searches actually run:

- msearch.py leanfinder, query `Finite constant group scheme torsors with
  equivariant maps form a stack for the etale topology`: 8 hits, including
  Scheme.etaleTopology, Scheme.Etale.forget and finite-type Galois-action
  instances, none the theorem.
- msearch.py loogle, query `"Torsor", "IsStack"`: 0 hits.
- msearch.py leansearch, query `Schemes with a finite constant group action
  that is locally trivial form a category fibred in groupoids`: 8 hits,
  including PreGaloisCategory.hasQuotientsByFiniteGroups and the type-level
  ActionCategory groupoid, none the scheme descent theorem.
- msearch.py grep, query `Torsor|torsor|IsStack`, subdirectory AlgebraicGeometry:
  0 hits. Separate Mathlib grep `etaleTorsorGroupoid|IsModuliStack`: 0 hits.
- Direct rg of torsor names in `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry`, followed by filename and precise declaration
  searches, found the general scheme torsor and étale subgroupoid modules above.
  They define the category but do not prove this stack property. The upstream
  étale torsor-descent modules concern sheaf torsors, not the present theorem.
- Direct rg for `etaleTorsorGroupoid|finite_constant.*torsor.*stack|torsor.*IsModuliStack`
  found only the étale torsor definition and its downstream quotient criterion.
  That criterion uses the current item in its proof and was not imported.
- grep for the exact item id in `lean/WeilConjectures` found no declaration.
  rg for the proposed theorem name in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf` found no name collision.
- The existing abelian-only `WeilConjectures.AlgebraicGeometry.ConstantGroupScheme`
  was read and not redefined or misused for nonabelian H. The colimit presentation
  from the downstream consumer avoids that abelian-only interface entirely.

Validation: scompile.py passed both the sandbox and library-module single-file
compiles cleanly (5.6 s and 6.9 s in the observed run). deliver2.py --no-push
returned OK: preflight and compilation passed for dry-run commit f4d796999a4.
All compilation and delivery use scompile.py and deliver2.py only. No shared source, compiled library, launcher
script, or repository Git state was edited directly.

## Second reading by Q123

This is a second pass by the same dispatched worker, not a claim of independent
review; the assigned workflow supplies an independent maintainer review after delivery.
I reopened the node and both existing torsor modules and checked the constant-group
presentation against the consumer `actionGroupoid_quotient_criterion`. Its H-coproduct,
unit, multiplication and internal action binders are exactly the same presentation
used here (with the harmless generalization to an independent group universe).
I checked the full-subcategory object proof is specifically étale local triviality,
not just fppf triviality, and the cartesian arrows preserve the map to V. I reopened
`IsModuliStack` to check both its CFG conjunct and its covering-sieve descent clause.
They include both clauses requested by the node, all base changes, and the specified
cocycle, without discarding automorphisms. No statement mismatch was found. The added
landed definition dependency was required to record the existing category used by
the signature. No mathematical node correction was made.
