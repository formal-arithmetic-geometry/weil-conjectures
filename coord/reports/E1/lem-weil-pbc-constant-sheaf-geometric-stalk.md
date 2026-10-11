## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk` states
`AlgebraicGeometry.Scheme.constantSheaf_geometricStalk_isIso`. Its only proof is `sorry`.
There are no new definitions, new nodes, dependency modules, or statement corrections.

Hypothesis and clause correspondence:

- A scheme T is `(T : Scheme.{u})`; no Noetherian, separation, connectedness, or other
  hypothesis is imposed.
- An arbitrary abelian group E is `(E : AddCommGrpCat.{(max u v) + 1})`. The independent
  universe v permits coefficients larger than the scheme universe. No finiteness,
  torsion, nontriviality, or finite-generation condition is imposed.
- The small etale site is `T.Etale` with `T.smallEtaleTopology`.
- The constant presheaf is `((Functor.const T.Etaleᵒᵖ).obj E)`, whose maps are identities.
- The constant abelian sheaf is
  `((constantSheaf T.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}).obj E)`.
  Mathlib defines this as `Functor.const ⋙ presheafToSheaf`; its `.obj` is its underlying
  abelian-group-valued presheaf, not a replacement definition.
- The canonical component iota_T is
  `(toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj E)).app
    (op (Etale.mk (𝟙 T)))`.
  `toSheafify` is exactly the unit of `sheafificationAdjunction`.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `(t : Spec (.of Ω) ⟶ T)`. Algebraic closedness implies the separable closedness
  needed by `pointSmallEtale`; it is not replaced by a different hypothesis.
- The pointed etale neighbourhood (T,t) is literally `Etale.mk (𝟙 T)` with
  `ULift.up (Over.homMk t (Category.comp_id t))` as its fibre element. The supplied
  equality states `t ≫ 𝟙 T = t`. No unspecified terminal object or chosen lift is used.
- The stalk is the presheaf fibre of the underlying constant sheaf at
  `(pointSmallEtale t).ulift.{(max u v) + 1}`, equivalently this point's `sheafFiber`.
  Its `toPresheafFiber` at the displayed neighbourhood is the colimit coprojection,
  so it sends a section to its germ/class there. Composing it after the iota_T component
  sends e to exactly the class of iota_T(e), as requested.
- The conclusion is `IsIso` of this composite morphism in `AddCommGrpCat`, which says
  that this specific homomorphism is an isomorphism of abelian groups. It does not merely
  assert an unspecified isomorphism between the two groups.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its morphisms,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.Etale` and
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, `Mathlib.AlgebraicGeometry.Sites.Etale`
  (the former is defined in `Mathlib.AlgebraicGeometry.Morphisms.Etale`).
- `def-weil-pbc-sheafification`: `CategoryTheory.presheafToSheaf`,
  `sheafificationAdjunction` and `toSheafify`, `Mathlib.CategoryTheory.Sites.Sheafification`.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf`,
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `def-weil-pbc-abelian-etale-sheaves`: `CategoryTheory.Sheaf`,
  `Mathlib.CategoryTheory.Sites.Sheaf`, instantiated with `AddCommGrpCat` and this site.
- `def-weil-geometric-point`: the morphism from the spectrum of an algebraically closed
  field, as its recorded Mathlib match specifies. Read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField`; no need to transport to its equivalent
  residue-field description.
- `def-weil-pbc-geometric-stalks`: `GrothendieckTopology.Point.sheafFiber`,
  `presheafFiber`, and `toPresheafFiber`, `Mathlib.CategoryTheory.Sites.Point.Basic`,
  with `Scheme.pointSmallEtale` from `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `def-weil-pbc-pointed-etale-neighbourhoods`: `Functor.Elements` and
  `categoryOfElements`, `Mathlib.CategoryTheory.Elements`, used by the preceding
  stalk definition. Read the fibre definition of `pointSmallEtale`, which gives lifts
  over T and their commuting morphisms exactly as the dependency specifies.

Technical imports: `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
provides sheafification on essentially small sites at the coefficient universe.
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic` provides `Point.ulift` and
`uliftSheafFiberIso`. `ulift` replaces each lift by its ULift copy; its category of elements
is equivalent to the original pointed-neighbourhood category, and `uliftSheafFiberIso`
identifies the resulting stalk with the recorded one. This is universe bookkeeping,
not another definition of the stalk. All variables and both universes are explicit.

Source check: the local clone has only literature lists, so read the official Stacks pages
https://stacks.math.columbia.edu/tag/03PT (2),
https://stacks.math.columbia.edu/tag/040R and
https://stacks.math.columbia.edu/tag/03PQ. They support respectively invariance under
sheafification, the neighbourhood-colimit definition, and cofilteredness. The docstring
carries all three proof steps from the node and their named DAG dependencies.

Edge cases checked mathematically before writing: the zero group gives the zero stalk
and its identity isomorphism; arbitrary infinite groups are permitted; an empty scheme
has no geometric point so the morphism binder has no inhabitants; disconnected schemes
are permitted since a stalk is local (there is no false assertion that all global sections
are E). Any field characteristic is permitted. The neighbourhood category is nonempty
because (T,t) is an object. There is no empty-colimit counterexample. Enlarging the
coefficient universe reindexes the same stalk, with no bound on E relative to T.
No statement fault or dispute was found.

Searches made (the tool log is `searches.jsonl`):

- `msearch.py leansearch`, query `constant sheaf stalk canonical map is isomorphism`:
  service unavailable, Internal Server Error; no verdict from that service.
- `msearch.py leanfinder`, query `The canonical map from an abelian group to the geometric
  stalk of its constant etale sheaf is an isomorphism`: eight hits, including
  `TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso` and `ModuleCat.Tilde.stalkIso`;
  none states this map on the small etale site.
- `msearch.py loogle`, query
  `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber, CategoryTheory.toSheafify`:
  zero hits.
- `msearch.py grep`, pattern
  `IsIso.*toPresheafFiber|constantSheaf.*stalk|constantSheaf.*[Ff]iber` in
  `CategoryTheory/Sites`: only `Point/Presheaf.lean:58`, about a bottom-topology point.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for the node id and for
  constant/stalk/IsIso phrases: the upstream Point/ConstantSheaf module supplies
  `sheafFiberConstantSheafIso`, read in full. It gives an isomorphism stalk-to-E, whose
  inverse equals our specified E-to-stalk map by naturality and
  `toPresheafFiber_presheafFiberConstIso_hom`; it does not state that exact map is an
  isomorphism. The node's `lean_candidates` already explains this distinction.
  Project `LisseTensorScalarExtension.lean` has a module-coefficient specialization,
  not the arbitrary abelian-group statement; that also uses this item in its docstring.
- `rg` in `dag/lean_names_upstream.json` for constantSheaf/fibre names, and in Mathlib,
  upstream, and project sources for `constantSheaf_geometricStalk_isIso`: no conflicting
  declaration or exact statement found.

The server compile passes with no errors or warnings. The delivered theorem remains
unproved, as stage 2 requires. A second reader must supply their own independent reading.

## Second reading by E1

I independently opened the sandbox node and Lean module, all eight statement-dependency
nodes, and the source declarations they record. The following is my inventory of the
node's objects, hypotheses and conclusion, with its Lean correspondence and verdict.

1. Arbitrary scheme T: `(T : Scheme.{u})`. Mathlib `Scheme` extends
   `LocallyRingedSpace` with the affine-local condition; its morphisms are scheme
   morphisms. No properness, Noetherian, connectedness, separation or finiteness
   instance appears. PASS.
2. Arbitrary abelian group E: `(E : AddCommGrpCat.{(max u v) + 1})`, with no torsion,
   cardinality, finite-generation or nonzero hypothesis. The category carries exactly
   abelian groups and homomorphisms. PASS.
3. Small etale site of T: `T.Etale` and `T.smallEtaleTopology`. I read
   `Morphisms/Etale.lean` (the `MorphismProperty.Over` definition, `Etale.forget` and
   `Etale.mk`) and `Sites/Etale.lean` (`smallEtaleTopology` and
   `ofArrows_mem_smallEtaleTopology_iff`). Objects are etale maps to T, morphisms are
   T-morphisms, and coverings are jointly surjective families, as required. PASS.
4. Constant presheaf with identity restrictions: `((Functor.const T.Etaleᵒᵖ).obj E)`.
   I read `Functor/Const.lean`; the object and all transition maps are constant. PASS.
5. Constant abelian sheaf obtained by sheafification:
   `((constantSheaf T.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}).obj E)`.
   `Sites/ConstantSheaf.lean` defines `constantSheaf` as `Functor.const` followed by
   `presheafToSheaf`. `Sites/Sheaf.lean` defines the sheaf category as the full
   subcategory satisfying `Presheaf.IsSheaf`. This uses the dependency notions,
   rather than a private constant-sheaf or sheaf-category definition. PASS.
6. Canonical component iota_U: `toSheafify` applied to the constant presheaf, evaluated
   by `.app`; the displayed component uses `op (Etale.mk (𝟙 T))`, exactly iota_T.
   `Sites/Sheafification.lean` defines `presheafToSheaf` as the left adjoint and
   `toSheafify` as its adjunction unit. Thus the map is the stipulated canonical one.
   The other components are already supplied by that natural transformation; there
   is no missing universal-U assertion in the conclusion. PASS.
7. Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
   followed by `(t : Spec (.of Ω) ⟶ T)`. I read `SpecToEquivOfField` in
   `ResidueField.lean` and `pointSmallEtale` in `Sites/EtalePoint.lean`: its fibre is
   `Etale.forget T ⋙ coyoneda.obj (op (Over.mk t))`, hence precisely lifts over T.
   Its separably-closed-field requirement is automatically supplied by algebraic
   closedness. No additional point or field condition is assumed. PASS.
8. Pointed neighbourhood (T,t): `Etale.mk (𝟙 T)` and
   `ULift.up (Over.homMk t (Category.comp_id t))`. The underlying lift is literally t,
   and the triangle equality is `t ≫ 𝟙 T = t`. I read `Functor.Elements` and
   `categoryOfElements` in `CategoryTheory/Elements.lean`: objects and morphisms
   agree with `def-weil-pbc-pointed-etale-neighbourhoods`. PASS.
9. Stalk of the constant sheaf: `toPresheafFiber` at that pointed neighbourhood
   applied to the underlying presheaf `.obj` of the constant sheaf. I read
   `Point.presheafFiber`, `toPresheafFiber` and `sheafFiber` in `Sites/Point/Basic.lean`.
   The first is the colimit over the opposite elements category, the second its
   specified coprojection, and the third restricts the first to sheaves. Hence this
   codomain is precisely the dependency's geometric stalk. PASS.
10. The specified homomorphism and the entire conclusion: `IsIso` of the composite
    `iota_T ≫ toPresheafFiber ...`. Lean composition first applies iota_T and then
    the coprojection, so e goes to the class of iota_T(e) at (T,t). `IsIso` asserts
    invertibility of this exact homomorphism in abelian groups, with no weakening to
    existence of an unrelated isomorphism. T, E and the geometric point are universally
    quantified in the node's order. PASS.

Source reading: this clone does not contain the Stacks .tex. I independently read the
official raw source at
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
including the beginning of `section-stalks`, `definition-geometric-point`,
`lemma-cofinal-etale`, `definition-stalk` and `lemma-stalk-exact`. I also checked the
rendered [03PT](https://stacks.math.columbia.edu/tag/03PT),
[040R](https://stacks.math.columbia.edu/tag/040R) and
[03PQ](https://stacks.math.columbia.edu/tag/03PQ) pages. These impose only a scheme and
an algebraically closed geometric point. The natural sheafification map induces the
stalk identification, and the identity neighbourhood supplies nonemptiness. The
statement agrees with this source; no correction or citer-verdict audit is needed.

Universe check: u and v are explicitly bound. The coefficient universe is allowed to
exceed the scheme universe by arbitrary v. As usual, groups in a smaller universe can
be represented in this coefficient category by ULift; no cardinal bound on coefficients
is imposed. Scheme and geometric-point field use the same scheme universe required
by the recorded `SpecToEquivOfField`/`pointSmallEtale` signatures. I read upstream
`Point.ulift`, `uliftPresheafFiberIso` and `uliftSheafFiberIso`: the ULift category of
lifts is equivalent to the original category, and its fibre is canonically isomorphic
to the original stalk. This changes only the universe presentation. The imported
`GrothendieckAbelian/HasSheafify.lean` supplies sheafification for the coefficient
category; it adds no binder or mathematical hypothesis to the theorem.

Edge cases: the zero group is allowed and its stalk is zero; infinite groups and
disconnected schemes are allowed. The empty scheme has no morphism from Spec of a
field, so the assertion has no point to instantiate there. The neighbourhood index
cannot be empty because the displayed identity neighbourhood is an object. There is
no n parameter, so n = 0 is not a separate case. Field characteristic is unrestricted.
No variable or universe is unbound.

Independent searches (different queries from the first worker; recorded by msearch):

- LeanFinder: `unit of sheafification composed with colimit injection constant presheaf
  point invertible`. Eight hits, including `sheafificationAdjunction_unit_app` and
  module-presheaf unit comparisons; none states this canonical stalk map is invertible.
- Loogle: `"toPresheafFiber"`. Twelve hits in `Sites.Point.Basic`, concerning
  coprojections, naturality, joint surjectivity and equality relations; no constant
  sheaf canonical-map isomorphism statement.
- msearch grep in `CategoryTheory/Sites`:
  `toSheafify.*toPresheafFiber|toPresheafFiber.*toSheafify|[Ii]sIso.*[Cc]onst`.
  Five hits, all about the constant-sheaf/global-section counit; none is this statement.
- Independent rg of upstream `WeilConjectures`, project `lean/Sheaf` and
  `dag/lean_names_upstream.json` for those composites, `presheafFiberConstIso`,
  `sheafFiberConstantSheafIso` and the proposed theorem name. I opened upstream
  `Mathlib/CategoryTheory/Sites/Point/ConstantSheaf.lean` in full. Its isomorphism
  is stalk-to-E, and its named lemmas concern the constant-presheaf coprojection and
  sheafification separately; the displayed E-to-stalk composite is not a declaration
  there. I also opened the hits in `AlgebraicGeometry/Sites/ConstantSheafSections.lean`
  and `PointFunctions.lean`: they prove injectivity into a sheaf of functions, global
  section bijectivity under connectedness, or a functions-sheaf comparison under
  discreteness. Their local bridge calculations do not supply an existing declaration
  of our theorem. No exact attachment or name conflict was found.

No new definition node or dependency module is present or needed. No hollow definition
is present: the module has only one theorem, whose proof is `sorry`. Its docstring
carries all three node proof steps and their named dependencies, the source tags, and
the required blueprint marker. The header, namespace, imports and line lengths follow
the example and conventions. I checked the node's `lean.statement` against the actual
signature as literal strings: equal. No Lean or node mismatch was found; I changed only
this report by adding the independent reading. The server single-file compile passed
in 1.8 seconds with no errors or warnings.

## Reviewer fix (R-csg1530, stage 2)

The stalk was taken at `(pointSmallEtale t).ulift.{(max u v) + 1}` with lift `ULift.up (...)`,
a second presentation of the geometric stalk (H4/H12). `pointSmallEtale t` has fibre in
`Type u` and `presheafFiber` needs only `HasColimitsOfSize.{u, u}` of the coefficients, which
`AddCommGrpCat.{(max u v) + 1}` has, so the ulift is unnecessary. The fix uses the recorded
point directly: `(pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t))`,
whose codomain is by `rfl` `(pointSmallEtale t).sheafFiber.obj` of the constant sheaf
(checked), and drops the now unused import of `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic`.
The ulift remarks in the reports above no longer apply.
