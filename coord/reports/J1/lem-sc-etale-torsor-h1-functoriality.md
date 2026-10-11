## Worker report

The module `Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality` states
`CategoryTheory.Sheaf.Torsor.etale_torsor_h1_functoriality`, with one `sorry` and no new
definitions. Its conclusion is the conjunction of the two independently universally
quantified clauses of the node. Neither clause assumes that its inverse-image or contracted
product torsor has already been constructed: both assert existence with the requisite
identification and class equality.

The source was read at https://stacks.math.columbia.edu/tag/03AJ (the local literature
checkout is absent). The source constructs the class as the boundary of 1 for the canonical
torsor extension; the upstream `Torsor.classH1` is this canonical map, characterized by
`classH1_lifts`. The declaration docstring carries all four proof steps of the item,
including the connecting-map ladder, degree-zero pullback, pushout extension and naturality
of boundaries.

Hypotheses and clauses, individually matched:

- The preliminary canonical bijection is the existing `Torsor.classH1 G terminalIsTerminal`.
  Applying it to `⟦T⟧` gives the class of the isomorphism class of the existing `Torsor G`.
  This uses the named canonical map, not a choice of an arbitrary bijection from the
  dependency's weaker existence theorem.
- Clause (1), schemes X and Y and morphism u:Y→X: `(X Y : Scheme.{u}) (f : Y ⟶ X)`.
- Clause (1), arbitrary abelian étale sheaf G: `Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1}`. No constructibility, torsion, geometric, finite type or field
  hypothesis is present.
- Clause (1), G-torsor T: `(T : Torsor G)`, the recorded dependency's structure.
- Clause (1), inverse image is a torsor under the inverse-image group:
  `∃ T' : Torsor ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G)` and
  `eT : (Scheme.etaleSetPullback f).obj T.sheaf ≅ T'.sheaf`. The latter is exactly the
  sheafified presheaf set inverse image, identified with the underlying sheaf of T'.
- Clause (1), induced action: the universally quantified equality for each `W : X.Etale`
  and each g,t says that pulling back `T.vadd g t` via the set-adjunction unit and `eT`
  equals the `T'.vadd` of the group-unit pullback of g and the set-unit pullback of t.
  These units are from the same sheafified Kan-extension construction. Their generators
  locally generate the inverse-image sheaves, so the equality specifies the induced
  action; it does not allow an unrelated action on an isomorphic underlying sheaf.
- Clause (1), class compatibility: `Etale.cohomologyMap f G 1
  (classH1 G terminalIsTerminal ⟦T⟧) = classH1 ... terminalIsTerminal ⟦T'⟧`.
- Clause (2), a scheme S, two abelian sheaves and their morphism:
  `∀ (S : Scheme.{u}) (G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
  (φ : G ⟶ G')`. This clause has no dependence on f,X,Y from clause (1).
- Clause (2), arbitrary G-torsor T: `(T : Torsor G)`.
- Clause (2), contracted product is a G'-torsor: `∃ T' : Torsor G',
  Nonempty (ContractedProductPresentation.{u, u} S φ T T')`. The existing presentation
  includes the natural quotient from T×G', the relation `(g +ᵥ t,h - φ(g)) ∼ (t,h)`,
  translation by G' on the second factor, and the universal property against every sheaf
  of sets. This universal property is precisely sheafification of the orbit presheaf.
  Additive subtraction is the node's multiplicative `φ(g)⁻¹g'` in abelian-group notation.
  Every such presentation describes the same torsor up to equivariant isomorphism: its
  universal property induces mutually inverse maps commuting with the quotient and the
  second-factor action. Consequently existence with the class equality states the class
  of the canonical quotient and is independent of a representative.
- Clause (2), induced coefficient map and class compatibility: `H.map φ 1
  (classH1 G terminalIsTerminal ⟦T⟧) = classH1 G' terminalIsTerminal ⟦T'⟧`.

Dependency declarations read and used:

- `WeilConjectures.CategoryTheory.Sites.Torsor`: `CategoryTheory.Sheaf.Torsor`,
  `Torsor.setoid`, `Torsor.classH1`, `Torsor.classH1_lifts` (the canonical map's docstring
  and characterization), and `Sheaf.nonempty_equiv_H_one_torsor` (the recorded
  lem-sc-torsor-h1 declaration). The named canonical map from that same module is used.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to
  `Scheme.smallEtaleTopology` and `AddCommGrpCat` as its dependency record requires.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar` and `upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `AlgebraicGeometry.Etale.cohomologyMap`. Its docstring specifies the exact functor and
  constant-sheaf comparison. The existing dependency explicitly records this Ext spelling
  of pullback and the stage-3 bridge to the resolution recipe; this delivery reuses it.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H.map`, the
  induced map of cohomology under a coefficient morphism. The dependency
  lem-weil-pbc-cohomology-pullback-functorial has neither lean nor mathlib_match on this
  checkout; the only notion its citation supplies to this statement is H¹(φ), which is
  already this Mathlib definition. No duplicate general functoriality theorem is needed
  to state the item, and no dependency has been re-recorded.
- `Sheaf.AlgebraicGeometry.EtaleSheaves`: `AlgebraicGeometry.Scheme.etaleSetPullback`.
  Its existing node def-weil-pbc-etale-sheaves is added to stmt_deps.
- `Sheaf.CategoryTheory.Sites.ContractedProductPresentation`:
  `CategoryTheory.Sheaf.Torsor.ContractedProductPresentation`. Its existing node
  def-sc-contracted-product-presentation is added to stmt_deps.

There are no new nodes or dependency modules. The two stmt_deps additions cite definitions
already landed on sheaf-dag, under the standing rule STMT_DEPS MAY GAIN LANDED NODES.
The node's mathematical statement and proof are unchanged.

Edge cases checked: empty schemes and arbitrary disconnected schemes are included, with no
nonempty or connected hypotheses. The trivial torsor and zero sheaf are admitted. For φ=0
the quotient is the trivial G'-torsor and its class is zero; for φ=id it is T. Identity
scheme pullback and pullback into an empty scheme are allowed. No injectivity or
surjectivity is required of φ or f. Universes are explicitly bound; schemes lie in u and
sheaf values in u+1, exactly as the recorded coefficient and pullback declarations. One
can raise u to accommodate arbitrary larger small sheaves; this imposes no cardinality
restriction. `terminalIsTerminal` is a supplied terminal-object instance, not an extra
hypothesis. The compiler runs with the project auto-implicit restrictions.

Searches (performed with msearch.py and rg):

- LeanSearch, `torsor cohomology H1 functorial pullback`: unavailable, Internal Server Error.
- LeanFinder, `etale torsor classification H1 natural under inverse image and change of
  coefficients`: eight unrelated étale-ring and cotangent H1 results; no match.
- Loogle, `CategoryTheory.Sheaf.H.map`: twelve hits including the existing coefficient-map
  definition, its composition laws and naturality of degree zero; no torsor pullback theorem.
- Mathlib grep, `torsor|Torsor` in CategoryTheory/Sites and `classH1|[Tt]orsor` in
  CategoryTheory: no hits.
- Source rg, `lem-sc-etale-torsor-h1-functoriality`: no hits. Source rg for
  `classH1.*(pull|inverse|map)|torsor.*(pull|inverse)` found the generic
  `Torsor.classH1_eq_map_of_equivariant`, which supplies coefficient naturality but does
  not state either the existence of the quotient or scheme-pullback compatibility. Other
  hits concern represented constant torsors, not arbitrary abelian sheaves.
- Project rg for torsors and `ContractedProductPresentation|InverseImagePresentation`
  identified the landed quotient presentation and the inverse-image-extension theorem.
  The latter supplies the action-unit compatibility used here, but states extension
  isomorphisms with an extension-presentation parameter rather than this H1 compatibility.
  Project rg for `etale_torsor_h1_functoriality|classH1.*pullback` found no declaration.

Validation: the server compiler is used via scompile.py; the delivery dry run is run via
`deliver2.py J1 lem-sc-etale-torsor-h1-functoriality --no-push`. Independent second reading is
left to the dispatcher’s second reader, as requested. No STATEMENT-DISPUTED issue found.

## Second reading by J1

I independently matched the node statement to the declaration
`CategoryTheory.Sheaf.Torsor.etale_torsor_h1_functoriality` in
`lean/Sheaf/CategoryTheory/Sites/EtaleTorsorH1Functoriality.lean`.

- Objects and hypotheses in clause (1): the Lean binders `(X Y : Scheme.{u})`,
  `f : Y ⟶ X`, `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`, and
  `T : Torsor G` render exactly the scheme morphism, arbitrary abelian etale
  sheaf, and torsor of the node.  The existential `T'`, isomorphism `eT` from
  `Scheme.etaleSetPullback f` applied to `T.sheaf`, and the displayed
  equivariance equation render that the sheafified inverse image is a torsor
  under the inverse-image group.  The final equality is exactly the node's
  pullback H¹ class equality, using `Etale.cohomologyMap` and `classH1`.
- Clause (2): the Lean binders `(S : Scheme.{u})`, `G G'`, `φ : G ⟶ G'`, and
  `T : Torsor G` match the node.  The existential `T' : Torsor G'` and
  `Nonempty (ContractedProductPresentation ... )` render the sheafified
  contracted product with its stated relation and second-factor action; the
  final `H.map φ 1` equality is exactly the coefficient-functoriality clause.
  The two clauses are independently universally quantified as in the node.
- Dependency declarations were checked in their source modules: `Torsor`,
  `classH1`, `Scheme.etaleSetPullback`, `Etale.upperStar`,
  `Etale.cohomologyMap`, `Sheaf.H.map`, and
  `ContractedProductPresentation` are the recorded notions, with no private
  replacement.

Edge cases checked: empty and disconnected schemes, the trivial torsor, the
zero sheaf, `φ = 0`, `φ = id`, identity and empty-target pullbacks, and `n = 1`
(the only degree used).  No nonemptiness, connectedness, finiteness,
characteristic, injectivity, or surjectivity hypothesis is introduced.  The
universe `u` and coefficient universe `u + 1` are explicit and match all
recorded dependencies.

Searches were rechecked with `rg` over `lean/Sheaf` and
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, plus the worker's
LeanSearch, LeanFinder, Loogle, and Mathlib searches.  They found no existing
statement of etale torsor H¹ functoriality; the only relevant declarations are
the recorded torsor, inverse-image, cohomology-map, and contracted-product
notions.  The module compiles cleanly with `scompile.py`.  I found no mismatch
and made no statement or dependency change.
