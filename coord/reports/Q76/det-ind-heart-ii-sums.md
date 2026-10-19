## Worker report

Group Q76; item det-ind-heart-ii-sums; 2026-10-18 UTC. The module
Sheaf.Paper.ConstructibleExtSums states the finite-subextension and algebraic-closure
cases as constructible_ext_sums and constructible_ext_sums_padicAlgCl. Both proofs
are sorry. The helper constructibleExtSumComparison has real data: DirectSum.toAddMonoid
applied to postcomposition with the shifted degree-zero coprojections. No new notion,
dependency module, node statement correction, or additional postponed theorem is needed.
The only changed node field is lean.

Clause-by-clause correspondence:

- The Noetherian scheme X is `(X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]`.
  These are exactly the recorded locally Noetherian and quasi-compact predicates;
  there is no base-field, characteristic, finite-type or separatedness restriction.
- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure is PadicAlgCl ℓ.
  In the first theorem `(E : PadicAlgCl.FiniteIntermediateField ℓ)` is the finite
  intermediate extension of Q_l in that closure. The second theorem is independent
  of a chosen E, so it states the closure case for every allowed E automatically.
- Lambda = E is `padicSubfieldRingObj X ℓ E`; Lambda = Qlb is `padicAlgClRingObj X ℓ`.
  These are precisely the recorded dependency declarations, definitionally
  condensedRingObj (Profinite.continuousMapRingObj E) X and
  condensedRingObj (Profinite.padicAlgClRingObj ℓ) X, respectively. In particular
  Qlb is the project's finite-subextension-valued condensed coefficient object.
- The ambient category is `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X)
  Ab.{u + 1})` over the corresponding ring object. This uses the tensor-action
  module category required by sk-def-sfb-module-objects, not a substitute category.
- The source sheaf C is an object of that category with hC exactly the recorded
  IsConstantModelConstructible predicate. A full-subcategory object is represented
  equivalently by its underlying object together with this membership proof.
- IndCons is `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible ... X)`;
  hB asserts this for every B s. Reading Mathlib/ObjectProperty/Ind.lean: its
  definition quantifies over a small filtered category and a ColimitPresentation
  whose every stage satisfies the predicate. Thus these are actual small filtered
  colimits in the ambient module category, including isomorphic presentations.
- The degree q is any integer `(q : ℤ)`, not a natural degree. The index set is
  `(S : Type (u + 1))`, the framework's chosen small-index universe, with no
  finiteness or nonemptiness assumption. B has the same coefficient category as C.
- The module-sheaf sum is an arbitrary `(c : Cofan B) (hc : IsColimit c)`.
  This names any presentation of the ambient coproduct. Such coproducts exist in
  this Grothendieck category; using an arbitrary universal cofan is equivalent to
  using a chosen coproduct and is invariant under its unique compatible isomorphism.
  It does not replace sheaf sums with sectionwise sums, or with derived coproducts.
- The helper's source is `⨁ s : S, (singleFunctor A 0).obj C ⟶
  ((singleFunctor A 0).obj (B s))⟦q⟧`; its target has c.pt in place of B s.
  These are precisely Hom_D(C[0], B_s[0][q]) and Hom_D(C[0], (sum B)[0][q]).
  The ordinary unbounded DerivedCategory and singleFunctor are Mathlib's recorded
  definitions. The framework supplies their abelian and localization instances.
- The map is the additive hom induced by
  `Preadditive.rightComp _ ((shiftFunctor (DerivedCategory A) q).map
  ((DerivedCategory.singleFunctor A 0).map (c.inj s)))` on each summand.
  DirectSum.toAddMonoid_of gives exactly f mapped to iota_s[q] composed with f.
  `Function.Bijective` of this additive hom is precisely an isomorphism of abelian
  groups; the additive inverse exists exactly when its underlying function is bijective.

Dependency declarations read and used:

- pqf-def-locnoeth: Mathlib.AlgebraicGeometry.Noetherian,
  AlgebraicGeometry.IsLocallyNoetherian (class and docstring read).
- def-weil-pbc-quasi-compact-scheme: Mathlib.Topology.Defs.Filter, CompactSpace
  (class and no-separation-condition docstring read).
- Both coefficient nodes: WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility,
  AlgebraicGeometry.ProEtale.padicSubfieldRingObj and padicAlgClRingObj.
  Read their full signatures, docstrings and defining condensedRingObj expressions
  in the exact shared pro-etale framework, together with coord/pefw-upstream-framework.md.
- sk-def-sfb-module-objects: its closed slopmaster2 audit names Mathlib.CategoryTheory.Monoidal.Mod,
  CategoryTheory.ModObj, Mod, Mod.regular, Mod.forget. Read their full definitions:
  actions have unit and associativity laws; Mod bundles them and uses equivariant maps.
- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  DerivedCategory, HasDerivedCategory and DerivedCategory.singleFunctor; read the
  localization definition and the single-complex embedding's signature and docstring.
- sk-def-sfb-constructible: Sheaf.Paper.CondensedConstantConstructibility,
  AlgebraicGeometry.ProEtale.IsConstantModelConstructible. Read the full module,
  including HasFiniteConstantLocalModel and the finite constructible stratification.
  The recorded finite constant scalar model is used, not the different upstream
  arbitrary-matrix local finite-presentation predicate.
- Proof import lem-pur-ringed-site-grothendieck-abelian:
  WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian,
  SheafOfModules.grothendieckAbelian_with_localized_generator. Its module was absent
  in the older source clone; read its full current source with scompile.py --source.
- Proof import def-weil-triangulated-category: Mathlib.CategoryTheory.Triangulated.Pretriangulated.
  The ordinary derived category supplies its shift and triangulated instances.
- sk-lem-constructible-ext-continuity has no Lean declaration or Mathlib match on
  the read base. Its proof import is therefore deferred; this item does not need
  that theorem to type its statement. Its precise Noetherian field-coefficient
  constructible-sheaf clause is transcribed into both proof docstrings.

The proof docstrings contain all three DAG proof steps: finite biproduct identities
and compatibility, the finite-subset filtered-colimit universal property, and the
constructible Ext-continuity comparison identified on each singleton.

Edge cases checked before writing: S empty is allowed; the coproduct and both Hom
sums are zero. S singleton gives the usual coefficient-sheaf identity map under the
coproduct identification. C = 0 or all B s = 0 give zero groups. Negative q is included
literally and gives the expected vanishing for degree-zero sheaves in the standard
t-structure; q = 0 recovers the ordinary Hom comparison. Empty Noetherian schemes
are permitted. E may be the degree-one subextension. No extra characteristic or
ell-invertibility assumption is introduced, since the node and continuity clause
have none. The original blueprint's missing Noetherian scope was already corrected
in stage 1 with a disjoint-union counterexample; this delivery preserves that exact
corrected DAG statement, so there is no remaining statement dispute here.

Searches performed using the prescribed msearch.py wrapper (results also in searches.jsonl):

- LeanFinder: "Ext out of a constructible pro-etale sheaf commutes with arbitrary sums
  of ind-constructible sheaves". Eight generic sheaf, condensed and presentation hits;
  none states the result.
- Loogle: "DirectSum.toAddMonoid, Preadditive.rightComp". Unknown identifier
  Preadditive.rightComp; read the exact pinned source to validate the name instead.
- LeanSearch: "Ext of constructible sheaves preserves arbitrary direct sums".
  Eight generic Ext.additivity and colimit hits, no constructible comparison.
- Mathlib grep through msearch: "constructible.*[Ee]xt|[Ee]xt.*[Cc]onstructible"
  in CategoryTheory: no hits.
- rg in /home/ubuntu/weil-src-slopmaster2/WeilConjectures, the exact shared
  lean/WeilConjectures pro-etale framework and lean/Sheaf for the node id,
  indConstructible, and Ext/coproduct/constructible patterns: no exact existing
  declaration. IndConstructibleFilteredColimits supplies closure under sums, not Ext
  continuity. ConstructibleCompactnessBounded is a downstream, geometrically more
  restricted theorem about derived coproducts; its constructibleBoundedComparison
  takes a cofan in the derived category, whereas this item's comparison takes
  degree-zero images of a cofan in the abelian category. It cannot replace this
  statement or its helper and importing it would reverse the proof dependency.
- Read Mathlib's ObjectProperty.ind and DirectSum.toAddMonoid/rightComp definitions;
  these provide all notions needed, so no new definition node is necessary.

## Second reading by Q76

This is the author's self-check required by the direct-delivery brief; independent
review is performed by the maintainer. Reopened the node and the module side by side.
No hypothesis or conclusion mismatch found: the two theorems cover exactly the two
coefficient choices; both bind a Noetherian scheme without the stronger geometric
setting of some siblings. hC and hB use the actual recorded predicate and its ambient
ind closure. Every integer q and every small S are included. Checked the type of the
helper carefully: c.pt is first embedded in degree zero and then shifted; it is not
an arbitrary coproduct of derived objects. The summed morphism is obtained from c.inj,
then the degree-zero embedding, then the shift, and postcomposition; the order matches
the displayed natural map. Bijectivity of this additive hom is the asserted abelian-group
isomorphism. Checked the empty family and degree-zero/singleton cases. The only named
postponed theorems are the two coefficient clauses of this very node. No node statement
was changed, no data was postponed, and no helper from a downstream theorem was imported.

Validation: scompile.py compiled the complete delivered module successfully on the
server, both its sandbox check and library module check; no errors or warnings
were emitted (library check: 18.5 seconds, within the unchanged 60-second limit).
All variables and universes are explicitly bound with autoImplicit disabled.
