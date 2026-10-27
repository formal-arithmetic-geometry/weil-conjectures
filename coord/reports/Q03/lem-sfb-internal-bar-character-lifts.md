## Worker report

The new module `Sheaf.CategoryTheory.InternalBarCharacterLifts` states
`Profinite.CondensedAction.InternalBarCharacter.exists_lifts`, with proof `sorry`.
Its conclusion is existence of a `Lifts` specification, retaining all the maps and
identities of the node. No definitions choose data from this existence theorem.
The auxiliary definitions construct the underlying complex and canonical component
transports from the recorded resolution using Mathlib's extension and shift functors.

Hypothesis and clause correspondence:

* A commutative condensed ring is `A : CategoryTheory.CondensedBar.Ring.{u}`;
  `A.toMon` is exactly the general `Profinite.CondensedRing` of the dependency,
  with its bundled commutativity instance. No topological presentation of A is imposed.
* A profinite group is `G : Type u` with `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`.
  Tests range over all `Profinite.{u}` and coefficients live in `AddCommGrpCat.{u+1}`,
  the dependencies' prescribed site/coefficient universe convention.
* The homogeneous augmented resolution is any `D : InternalBar.Resolution A.toMon G`.
  Its `objects`, `freeIso`, `diagonal`, `boundary`, `boundary_generator`,
  `boundary_boundary`, `augmentation` and `augmentation_generator` supply exactly
  the free internal modules, diagonal action, alternating deletion and unit augmentation.
  `chains` uses these actual boundaries; `complex` extends it along
  `ComplexShape.embeddingDownNat`. Thus degree -n is P_n and positive degrees are zero,
  including zero outgoing differential in degree zero. `termIso` is the canonical
  identification, not a further choice of resolution.
* A condensed additive group map is the EXISTING
  `CategoryTheory.CondensedDerivedRestriction.Character A G`: its `app`, `one`,
  `mul`, `naturality` quantify over every profinite section and every base change.
  The node `def-sfb-condensed-unipotent-class`, already carrying this declaration,
  is added to stmt_deps. Nothing in its unipotent extension or derived class is assumed.
* `lift` and `lift_spec` give actual cochain maps `P ⟶ P⟦1⟧`.
  `IsLift` includes equivariance at each P_(n+1) to P_n component and precisely
  `a.app S ((x 0)⁻¹ * x 1) • [x 1,...]` on all generalized generators.
  `component` uses the canonical shift component isomorphism without inserting a sign.
  `lift_unique` asserts uniqueness from those formulas; `lift_zero` gives L^0=0.
  `anticommutation` states boundary L + L boundary = 0 at all n >= 0;
  the endpoint identities are already included in the integer-indexed cochain map.
  Mathlib's cochain shift multiplies the differential by `Int.negOnePow`, so [1]
  has the requested negative differential. Internal-module maps with equivariance on
  all nonzero components are precisely equivariant cochain maps; using this equivalent
  encoding avoids assuming or choosing a second abelian structure on the action category.
* An ordered list is `a : List (Character A G)`, with q=`a.length`.
  `iterate_nil` is the identity under the canonical zero-shift isomorphism.
  `iterate_snoc` appends b by `F_a ≫ (lift b)⟦q⟧'` and the canonical shift-add
  comparison, giving exactly L_last[q-1] ... L_first in categorical composition order.
  `iterate_equivariant` retains equivariance of each nonzero component.
  `iterate_below` states vanishing for n<q. `iterate_generator` covers n>=q by
  writing the input degree as n+q, with the Fin-indexed ordered scalar product and
  remaining tuple `[g_q,...,g_(n+q)]`.
* `augmentation` is an actual cochain map to A[0]; `augmentation_zero` fixes its
  only possible nonzero component to `D.augmentation.val`.
  `augmented_component` identifies the equivariant arrow `augmented a` with
  the degree -q component of `iterate a ≫ augmentation⟦q⟧'`.
  `augmented_sole` makes all other components zero, `augmented_closed` is
  `boundary_(q+1) ≫ f_q = 0`, and `augmented_nil` is f_0=e.
* The given internal-function description is
  `H : CondensedBar.InternalFunctions A`, with its normalized
  `B : CondensedBar.BarDiagram (G := G) H`. These are the compatible function
  and diagram specifications from the recorded dependency, not arbitrary replacement
  cochain groups. `cochains B` is its alternating coface complex, with B's first face
  acting, interior faces multiplying neighbours and last face dropping the last entry.
  It is evaluated on the existing trivial regular action. `CondensedBar.extend`
  gives its ordinary integer-indexed complex U.
* `cocycle a` is an actual cochain map from the single complex concentrated at q,
  Mathlib's canonical encoding of A[-q], to U. `cocycleComponent` reads its degree-q
  map A to U^q in `B.term` function coordinates. `cocycle_formula` is the full linear
  formula: at every S, scalar r, base change f:T→S and tuple g of continuous T-sections,
  evaluation is r restricted to T times the product of the a_k(g_k).
  In particular r=1 is exactly the node's z and the empty list gives c_0=1.
  Source concentration makes all its other components zero.
* `coordinates` equates evaluation of f_q on `[g_0,...,g_q]` with evaluation of
  that very cocycle at successive ratios `g_(k-1)⁻¹*g_k`. Together with
  `cocycle_formula` this also explicitly determines the homogeneous augmented formula.
  Every equality is on arbitrary profinite sections, not just global G-points.
  All maps are internal-module morphisms, hence commute with restriction; the cocycle
  formula additionally tests arbitrary slice arrows f. No projectivity, flatness,
  internal-Hom acyclicity, injectivity or categorical exactness hypotheses are introduced.
* The abstract-derived-category dependency supplies the ordinary complex and shift
  conventions. This lemma itself is before localization, as is its mathematical statement;
  no separate derived category or comparison map is fabricated.

Dependency declarations read and used:

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`,
  module objects and their underlying maps.
* `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.Modules`,
  `sectionModule`, `ActionModule`, `Equivariant`, `trivial`.
* `Sheaf.CategoryTheory.CondensedInternalBarResolution`: `InternalBar.Resolution`,
  `basis`, `onSections`, `regularOne` and all its normalized boundary/augmentation fields.
* `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `CondensedBar.Ring`,
  `InternalFunctions`, `BarDiagram`, `power`, `tupleMap`, `cochains`, `extend`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: ordinary-derived-category framework;
  Mathlib's `HomotopyCategory.Shift`, `Single`, `Embedding.CochainComplex` interfaces
  provide the canonical shifts, single complexes and extensions actually used.
* Added landed dependency `Sheaf.CategoryTheory.CondensedUnipotentClass`:
  `CategoryTheory.CondensedDerivedRestriction.Character` (full signature and laws read).
* Proof-only import `Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful`:
  `equivariant_iff_on_generators` and the normalized exact-forgetful infrastructure.
  `lem-sfb-condensed-free-linearization-tensor` has no recorded Lean module or match
  in the current node; there is accordingly no proof import to add for that node.
  Its mathematical universal property remains in the theorem proof docstring;
  canonical free objects and generators already come from the resolution module.

Edge cases checked before and during the second reading:

* q=0: empty product 1, zero-shift identity, f_0=e, source A[0], constant unit cochain.
* n<q: the target positive degree is zero and `iterate_below` retains this explicitly.
* n=q: the last remaining generator has arity one and augmentation value 1.
* n=0 and n=1 in the chain identity: the zero endpoint and the unaugmented zero
  differential avoid erroneously using the augmentation as d_P^0.
* The trivial group and zero characters cause no problem: positive-length products vanish.
  Zero coefficient rings and characteristic two are included; the sign convention is integral.
* Empty profinite test objects and arbitrary restrictions are included in all section
  quantifiers. Sheafified free modules are never asserted to be sectionwise free.
* No universe constraint beyond the already fixed profinite-site/coefficient convention
  is added. Lists cover all finite ordered lists without selecting a degree q>0.

Searches for an existing statement/notion:

* msearch.py / LeanFinder, query `Internal homogeneous bar complex additive characters
  give degree one chain lifts and ordered products of inhomogeneous cocycles`:
  eight hits on discrete inhomogeneous cochains, their differential and coordinate
  isomorphism; no internal condensed character-lift theorem.
* msearch.py / Loogle, query `"Rep.barComplex"`: six discrete Rep bar-complex hits,
  none the internal condensed maps or ordered normalization.
* msearch.py / grep, query
  `(character|Character).*(barComplex|chainMap)|barComplex.*(character|Character)`:
  zero hits.
* msearch.py / LeanSearch, query `Additive condensed group characters induce equivariant
  degree one maps on the internal homogeneous bar complex with ordered product cocycles`:
  eight hits including `Rep.barComplex`, `CharacterModule`, `AddChar`; none this statement.
* rg across `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-sfb-internal-bar-character-lifts|CharacterLift|characterLift|orderedCocycle`:
  no existing declaration. Broader `barComplex|character.*(bar|Bar)` search finds
  discrete `WeilConjectures/RepresentationTheory/GroupCohomology/CupNonvanishing.lean`,
  not the internal sheaf lemma.
* Broader `Character|character|additive.*condensed` search finds the exact reusable
  `CondensedDerivedRestriction.Character` in `CondensedUnipotentClass.lean`.
  It is used directly; no duplicate Character definition remains.
* DAG dependency traversal from the added definition node checked that it does not reach
  this item (297 reachable nodes checked), so adding it introduces no dependency cycle.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
and the item's six-step agent-written calculation. As the node says, the blueprint itself
invokes open direct-image stability rather than spelling out this formal calculation;
the exact independent internal-category reference remains WANTED in the inherited source.
No statement correction or mathematical dispute is asserted.

## Second reading by Q03

A separate reread of the node's entire statement and the completed module checked the
above correspondence, especially the signs, direction of the shift-add isomorphism,
zero-degree endpoints, and scalar multiplication after arbitrary T→S. It found a duplicate
candidate for Character in the initial draft: this was removed and replaced by the landed
`CondensedDerivedRestriction.Character`, adding its owning node to stmt_deps. It also found
one overlong line, now wrapped. The integer-indexed single complex at q is A[-q], while
augmentation uses A[0] shifted by +q, so the two displayed source/target shifts agree with
the node. The ordered recurrence shifts the newest lift by the previous list length;
no character permutation or additional Koszul sign is introduced. Full arbitrary-slice
linearity is asserted for the cochain, not merely the scalar-one product formula.
The `coordinates` clause compares the actual augmented composite with that same cochain,
not an unrelated cocycle. The only theorem has `sorry`, and all helper definitions are
real transports of existing constructions. No independent sub-agent was started, in
accordance with the dispatcher's instruction; independent review is the maintainer's.
