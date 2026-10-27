## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceHomsOverOpen` states
`AlgebraicGeometry.AlgebraicSpace.coherent_homs_over_open`, with one `sorry` and no
new definitions. Source read: `literature/stacks-project/spaces-cohomology.tex`,
Tag 07UM, `lemma-homs-over-open`, lines 2172–2204. Its first displayed canonical
isomorphism is the node's claim. No statement correction or disputed assertion.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `S : Scheme.{u}` and `X : AlgebraicSpace S` are the given base and algebraic space.
- `hln` asserts local Noetherianity on every etale scheme test, exactly as the node
  specifies. `hqc : CompactSpace (Point X.obj.obj)` is quasi-compactness in the existing
  atlas topology. `hqs` tests compactness of the diagonal's pullback on pairs of affine
  scheme tests. This is absolute quasi-separatedness; no condition on S or separatedness
  of X over S is imposed. This is the same three-part interface as the recorded
  `noetherian_affine_atlas_relation`.
- `F G I : X.Modules` uses sheaves of modules on the actual small etale ringed site.
  `hF` is quasi-coherence of F; `hGqc` is quasi-coherence of G; `hGcoh` is precisely
  `RingedSpace.IsCoherent` on every `schemeRestriction X T`, including its finite-type
  and finite-type-kernel clauses. In particular, coherence is not replaced by mere
  finite type. `hI` is quasi-coherence of the ideal sheaf. The monic module map
  `i : I ⟶ SheafOfModules.unit X.structureSheaf` presents its ideal inclusion.
- `U`, `j` and `hj` give an open immersion into X and its etale restriction functor.
  The first conjunct is representability by open immersions, using the existing
  `IsRepresentableWith` and Mathlib `IsOpenImmersion`. The next equivalence says that
  an etale test factors through U exactly when its ideal inclusion is surjective on
  sections. For a monic ideal sheaf this is exactly I|T = O_T: surjectivity contains 1,
  and conversely an isomorphism of sheaves is an isomorphism on sections. Thus it
  specifies the entire unit locus, not an arbitrary smaller open. On affine charts
  this is the complement of the common zero locus. U is unique up to unique
  isomorphism over X; it is not an arbitrary chosen open.
- `P n`, `p n : P n ⟶ G` with `Mono (p n)` and the section-image equality specify
  exactly I^n G as a subobject. The right side is the already recorded
  `idealPowerSubsheafSections i G (fun _ ↦ Set.univ) n T`, including the local
  sheaf-generation condition on nonaffine tests. No independent power convention
  is introduced. At n = 0 its image is all of G and the monic map is an isomorphism,
  giving I^0 G = G canonically. These data are determined up to the unique
  inclusion-preserving isomorphism on each power.
- `IsIso ((pullback j hj).map (p n))` gives (I^n G)|U = G|U canonically.
- `r n m h ≫ p n = p m` specifies the inclusion I^m G ⊆ I^n G for n ≤ m.
  Monicity of p n forces these maps uniquely, including identity and composition.
- `D : ℕ ⥤ AddCommGrpCat.{u+1}` with isomorphisms `e n` is the Hom diagram. The
  equation involving `D.map (homOfLE h)` explicitly requires precomposition by r.
  The ordinary node's n+1 transition is its m = n+1 case. Allowing all n ≤ m adds
  no extra mathematical assertion: composites of those inclusions are forced.
- `c` has target Hom(G|U,F|U). The equation `(pullback j hj).map (p n) ≫
  c.app n ((e n).inv χ) = (pullback j hj).map χ` forces c to be restriction using
  the canonical power identification, since the first factor is an isomorphism.
  `Function.Bijective (colimit.desc D ⟨_, c⟩)` is precisely the asserted canonical
  colimit bijection. The cocone legs and the comparison are not arbitrary maps.
- The final universal quantifier over `ψ`, with `∃ n χ` and the corresponding
  restriction equation, is the node's explicit extension clause, including n = 0.

Universes are explicit, `autoImplicit false` is set, and there are no local instances,
private definitions, statement lets, or coefficient lifts. X's site has object universe
u+1 and section universe u, hence its Hom groups naturally live in u+1. The Hom colimit
uses that actual universe without identifying site object and section universes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `IsRepresentableWith`, `IsEtale`, `pullback`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  slice sheafification instances, using Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, including its public import of
  `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent` (the
  exact finite-type-kernel predicate, rather than the QCoh/finite-type conjunction).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`,
  constructed from `schemeOpens` and the canonical `schemeOpensRingHom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  on `Point`, with the final topology for etale charts.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees`: `idealPowerSubsheafSections` and
  `idealSectionImage`, owned by `def-sfb-space-ideal-power-products`.

The latter three landed definition-node owners are added to stmt_deps; every previous
statement dependency is retained. No new node or dependency repair is needed.

Plain proof imports retain the recorded modules for
`lem-sfb-noetherian-affine-atlas-relation`,
`lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`,
`lem-sfb-space-qcoh-affine-chart-calculus`, and
`lem-weil-pbc-coherent-homs-over-open`. The colimit API is public through
`Mathlib.Algebra.Category.Grp.Colimits`; the elementwise filtered-colimit Mathlib
matches are imported through `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`
and `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`. The latter's
`Concrete.isColimit_exists_rep` and `Concrete.isColimit_rep_eq_iff_exists` were read.
The atlas, scheme-etale exact-finiteness, and groupoid-equivalence proof nodes have no
recorded Lean module, so those three proof imports are left for the maintainer when
stated. They are proof inputs, not extra hypotheses of this statement.

Edge cases checked before writing:

- I = O_X: U = X, every power inclusion is an isomorphism, and the diagram is constant.
- I = 0: U is empty, and every positive power is zero; the colimit and open Hom are zero.
- A nilpotent I likewise gives an empty unit locus and eventually zero powers.
- n = 0 is included and the actual section image is all of G; the inclusion identifies
  P 0 with G, even on an empty test covered by an empty sieve.
- X empty, F = 0, G = 0, and zero section rings impose no nonemptiness assumption.
- No finiteness hypothesis on F, no affine hypothesis on R, and no separatedness of X
  are introduced. A non-separated Noetherian scheme remains a valid algebraic space.
- The unit-locus equivalence is tested on every etale object, not just affines, but is
  still equivalent: I|T = O_T makes its section map surjective on every T, and containing
  a preimage of 1 forces equality on every restriction of T.

Searches made for an existing declaration:

- `msearch.py ... leanfinder "Morphisms from a coherent module over an open algebraic
  space are the colimit of Hom from ideal power multiples"`: 8 hits, local-cohomology
  diagrams, scheme module colimits, scheme ideal glue maps and generic presentations;
  no algebraic-space extension theorem.
- `msearch.py ... loogle '"SheafOfModules", "Hom"'`: 12 hits, generic
  `PresheafOfModules.Hom`, its additive structure, and unit-Hom equivalence; no match.
  An initial unquoted `SheafOfModules, Hom` query had no hits (unknown `Hom`); repeated
  with the quoted query above.
- `msearch.py ... leansearch "Restriction Hom over an open algebraic space is colimit
  Hom from powers of ideal times coherent sheaf"`: 8 hits, scheme restriction and
  scheme Hom interfaces; no match.
- `msearch.py ... grep 'idealModuleProduct|idealSheafPower|homs_over_open'`: zero
  Mathlib matches. `rg` of both `lean/WeilConjectures` and `lean/Sheaf` finds the scheme
  `Scheme.coherent_homs_over_open`, not the algebraic-space statement. Searching the
  item id finds only its mention in the generic-multiple-embedding proof docstring.
- Project searches for ideal powers found the existing Artin-Rees local section
  construction and its landed definition-node owner. They are reused without copying.

Compilation: `scompile.py Q10 lem-sfb-space-homs-over-open <module>` passes in both
sandbox mode (2.1 s) and its delivered module path (2.2 s), with no warnings. An initial
unnecessary nonexistent `Mathlib.Order.Category.Nat` import was removed; Nat's category
is already provided by the imported APIs. No local compiler or global build was run.

## Second reading by Q10

This is the worker's own final rereading; the dispatch brief forbids starting another
agent and reserves independent review for the maintainer. Read the completed theorem
against the unchanged node and Stacks 07UM again. Verified each hypothesis and every
clause using the correspondence above. In particular the open is the entire unit locus,
the power subobjects are fixed by their section images, transitions are forced by
monicity, c is forced by its restriction equation and the isomorphism on U, the Hom
universe is u+1, and the extension clause explicitly uses n in ℕ. No mathematical
mismatch or additional source hypothesis was found. No definitions or other theorems
were introduced; the single proof is `sorry` and its docstring carries all six DAG steps.
