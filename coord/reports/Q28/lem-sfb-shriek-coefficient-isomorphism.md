## Worker report

The retained statement packet now compiles cleanly on the server and passes the
required delivery preflight. All theorem proofs remain `sorry`, as stage 2 requires.

This module states all clauses of lem-sfb-shriek-coefficient-isomorphism in
Sheaf.Paper.ShriekCoefficientIsomorphism. All theorem proofs are `sorry`.
Definitions have actual data: scalar restriction, the composed canonical comparison,
and restrictions to full subcategories. No new definition node or dependency repair
is needed. The main declaration is shriekCoefficientIso_adjoints; lean.declarations
also lists the preceding constructions and clauses.

Hypotheses and objects, matched against the node:

- Arbitrary commutative condensed rings are the variables
  `Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, with MonObj and
  IsCommMonObj instances. This is the underlying-object encoding of the existing
  Profinite.CondensedRing, not a topological presentation. `e : Mon.mk Λ ≅ Mon.mk Λ'`
  is an isomorphism of ring objects, including both monoid-hom conditions.
- Schemes are `Scheme.{u}` and their sites are `Scheme.ProEt.topology T`, with
  object universe u+1 and morphism universe u. Abelian coefficients have Hom
  universe u+1. No site-universe equality or extra essential-smallness hypothesis
  is imposed; the existing small-site framework supplies its instances.
- The rings on T are the existing `condensedRingObj Λ T`, underlying
  `coefficientRing T (Mon.mk Λ)`, and similarly for Λ'.
  `shriekCoefficientTransport e T` is precisely
  `(Mod.comap (coefficientMap e.inv.hom T)).mapDerivedCategory`, so U_T is
  restriction along the pulled-back INVERSE of e, in the stated direction.
  It is termwise scalar restriction on ordinary unbounded derived categories.
- `shriekCoefficientCtf` transparently abbreviates the intersection of the
  existing `constantModelBoundedConstructible Λ T` and
  `DerivedCategory.finiteTorAmplitude _`. This uses finite CONSTANT local models,
  not the separate arbitrary-matrix constructibility predicate.
  `shriekCoefficientLocalizing` is that property's existing `localizingClosure`:
  the intersection of replete triangulated properties closed under ambient
  coproducts indexed by Type (u+1), the fixed ambient Hom universe.
- `c : Compactification.BoundaryCompactification f` has underlying
  `c.obj.obj : Compactification f`, with proper p, open j, and j ≫ p = f.
  Its intermediate QuasiCompactObjects property retains quasi-compactness of j.
  No density or finiteness condition on X, Y or f is imposed.
- H and H' are exactly the existing
  `CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj`
  and its Λ' version. These derive the two factors separately, D(j_!) then Rp_*;
  no replacement by the derived underived composite occurs.

Conclusions, clause by clause:

- `shriekCoefficientIso_transport` states U_T.IsEquivalence,
  U_T.IsTriangulated, preservation of every Discrete I colimit for
  I : Type (u+1), the constructible-finite-Tor iff, and the localizing-closure iff.
  The functor carries the existing canonical derived commutation with shifts.
- `shriekCoefficientLocalizingTransport` is the actual lift of
  L_T.ι ⋙ U_T to L'_T, using the preceding closure-preservation proof only.
  `shriekCoefficientIso_localizing` states this restricted functor is an
  equivalence and triangulated, with the ambient-induced triangulations.
- `shriekCoefficientCompactificationIso` CONSTRUCTS the canonical ambient
  comparison H ⋙ U_Y ≅ U_X ⋙ H'. It first uses
  CondensedRing.derivedComapLowerStarIso for e.inv.hom and p, then the termwise
  derived CondensedRing.comapOpenImmersionLowerShriekIso for j, with the
  associators and mapDerivedCategoryCompIso inserted. The flatness instance
  required by the first comparison is obtained from extendScalarsIsoComapInv,
  since restriction along the inverse ring isomorphism is exact.
- The hypothesis h of shriekCoefficientIso_preservesLocalizing is exactly
  H(L_X) ⊆ L_Y. Its conclusion is H'(L'_X) ⊆ L'_Y, with no independent
  primed preservation assumption. `shriekCoefficientLowerShriekLocalizing c h`
  defines F by an actual full-subcategory lift. Its primed version uses the
  transferred preservation theorem.
- `shriekCoefficientLocalizingIso` constructs a by restricting each component
  of the specific ambient canonical comparison with ObjectProperty.isoMk.
  Its naturality is inherited from that comparison on the underlying morphisms.
- `shriekCoefficientIso_adjoints` takes arbitrary G and G' on the two localizing
  categories and the GIVEN adjunctions adj : F ⊣ G and adj' : F' ⊣ G'.
  Its first conjunct is `∃! b : G ⋙ U_X ≅ U_Y ⋙ G', ...`, with U here the
  restricted transports. For every N its equation is, in Lean's composition order,
  `a.hom.app (G.obj N) ≫ F'.map (b.hom.app N) ≫
    adj'.counit.app (U_Y.obj N) = U_Y.map (adj.counit.app N)`.
  This is exactly the printed counit equation, including the direction of a.
  Uniqueness quantifies over the whole natural isomorphism, not merely an
  unnormalized choice of right adjoint.
- The second conjunct of that theorem is precisely the iff of the two
  constructible-finite-Tor preservation inclusions. It quantifies over objects
  of each target localizing category, tests C on the underlying ambient object,
  and tests C on the underlying object of its image under the given G or G'.

Dependency declarations read and used:

- Sheaf.Topology.ProfiniteCondensedRing: read Profinite.CondensedRing, whose body is
  exactly `Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`. The module
  uses this existing ring-object encoding unbundled, as required by the upstream
  coefficient APIs. It introduces no alternative condensed-ring definition. The
  unused re-export import is omitted; see the validation repair below.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology;
  def-weil-size-convention has a convention-only record and no declaration.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: coefficientRing,
  condensedRingObj, upperStarFromPoint, preservation of commutativity.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions:
  Functor.rightDerivedFunctorOfQuasiIsoResolutions (the recorded unbounded
  derived-category convention); ambient categories use Mathlib.DerivedCategory.
- WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars: Mod.comap,
  extendScalars and the scalar adjunctions; ModuleObjects.MapMod supplies
  comapEquivalenceOfIsIso and extendScalarsIsoComapInv.
- Sheaf.Paper.CondensedConstantConstructibility:
  IsConstantModelConstructible, constantModelBoundedConstructible,
  ConstantModelConstructibleFiniteTor.
- Mathlib.CategoryTheory.Triangulated.Subcategory:
  ObjectProperty.IsTriangulated, inherited full-subcategory structure;
  WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure:
  ObjectProperty.localizingClosure and its repleteness/triangulation instances.
- Sheaf.Compactification.BoundaryRefinement: BoundaryCompactification,
  QuasiCompactObjects; WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek:
  CondensedRing.rightDerivedLowerShriekOfCompactification.
- Mathlib.CategoryTheory.Adjunction.Basic: Adjunction.mkOfHomEquiv and
  homEquiv_counit, for the normalized mate proof plan.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients:
  coefficientMap, derivedComapLowerStarIso, comapOpenImmersionLowerShriekIso.
- Proof-only imports retain the recorded sheaf tensor, module-object
  Grothendieck, derived coproduct, exact-functor factorization,
  equivalence-colimit, coefficient-constructibility and mate-isomorphism tools.
  In particular Sheaf.Paper.CondensedCoefficientIsoConstructible supplies
  constantModelCtf_coefficientIso, and Sheaf.CategoryTheory.MateIsoAlongEquivalences
  supplies isIso_mateEquiv_of_isEquivalence_of_fullyFaithful.

Searches performed in this attempt (and the retained searches.jsonl records the
previous attempt's searches):

- msearch leansearch: “An isomorphism of condensed coefficient rings transports
  unbounded derived compactification pushforward and identifies its given right
  adjoints on localizing constructible subcategories”. Eight hits, including
  presheaf/sheaf pushforward adjunctions, pushforwardCongr and discrete condensed
  module comparisons. None includes the derived compactification/localizing/mate
  assertion of this node.
- msearch leanfinder: “An isomorphism of condensed ring coefficients transports
  compactly supported derived pushforward on localizing constructible subcategories
  and its counit-normalized right adjoint”. Eight hits: condensed discrete-module
  adjunctions, condensed-set counits and sheaf-pushforward adjunctions. None says
  the full statement.
- msearch loogle: “CategoryTheory.Adjunction, CategoryTheory.Equivalence”. Six hits,
  including Equivalence.toAdjunction and Adjunction.toEquivalence; these are
  categorical ingredients, not the coefficient/compactification theorem.
- msearch grep, CategoryTheory: “coefficientIso|coefficient.*shriek|shriek.*coefficient|mateEquiv”.
  Twenty hits, chiefly Adjunction.Mates and bicategorical mate formulas. No exact
  match for this node.
- rg over lean/WeilConjectures and lean/Sheaf for
  “coefficientIso|coefficient.*shriek|shriek.*coefficient”, and a node-id grep of
  lean/WeilConjectures: no declaration of this node. Hits include the existing
  constantModelCtf_coefficientIso (only its constructibility clause), coefficient
  comparison infrastructure, and unrelated ordinary/finite scalar comparisons.
- rg for the proposed declaration names in Mathlib/project sources and
  dag/lean_names_upstream.json: no collision.

Edge cases checked against the definitions and the source argument: e = id;
isomorphisms involving zero coefficients; empty schemes; j = id; and the empty
coproduct indexing family. No nonzero-ring, nonempty-scheme, finite-type,
admissibility, bounded-below or nonempty-index hypothesis was introduced.
The unique mate is normalized by the given counits, so changing adjunction data
is not silently ignored. No statement correction or disputed statement is needed.

Validation repair: the required initial dry run reproduced the earlier 60-second
prerequisite timeout in `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`.
Tracing the import graph found exactly one direct import leading to that closure:
`Sheaf.Topology.ProfiniteCondensedRing`, via `ContinuousCoefficientCommRing`,
`ModuleObject.BaseChangeTheorems.MorphismDefs`, `Derived.BoundedConstructible`,
`ComparisonDirectImage`, `Comparison`, and `Comparison.LowerStarAcyclic`.
That re-export supplies no declaration used by this file: the coefficient APIs and
this statement already use the existing unbundled tensor ring objects. Removed this
unused import. No definition, mathematical statement, upstream source or launcher
script was changed. The prescribed scompile.py then checked the sandbox form in
10.3 seconds and the library module in 9.3 seconds, without errors or warnings.
The subsequent deliver2.py --no-push passed the server preflight and compilation
(commit 9adaba1f605). The earlier report's claim that this task was blocked is
superseded by this successful repair.

## Second reading by Q28

The dispatcher requires this worker to deliver directly and prohibits additional
agents. This section records a second pass by the same worker; the independent
review is the maintainer's, as specified in the brief.

Read the node and its source coefficient-comparison section and
sk-thm-existence/det-existence-restriction proof alongside the module. The retained
attempt omitted all restricted-functor and adjoint clauses; these are now stated.
Checked that the scalar map is e inverse, that both C predicates use finite
constant local models, that L is the actual intersection-defined closure, and
that c retains quasi-compactness of j. Checked every conclusion in the mapping
above, especially the left/right comparison orientations and the three factors
in the counit equation. The comparison a is the restriction of the constructed
ambient one, and the iff concerns the same two given right adjoints. Every
postponed theorem belongs to this node and carries its corresponding complete
natural-language proof; definitions contain no postponed data.

## Final self-check

Re-read the saved module and the current node statement, its ten proof steps,
the recorded dependency signatures and docstrings, and the blueprint coefficient
comparison and existence-restriction sources. The statement, statement dependencies
and proof dependencies are unchanged from the live node. The stored lean.statement
matches the main theorem signature verbatim, with all universes and variables
explicitly bound. Every helper is listed in lean.declarations and has a source and
blueprint docstring; every postponed proof is a whole named theorem with its proof
plan. No theorem was proved. Checked the 100-character line limit and searched the
project again for declaration collisions: none. Only the item module, its node's
lean record and this worker report are delivered. No new or dependency nodes and no
statement correction are needed.
