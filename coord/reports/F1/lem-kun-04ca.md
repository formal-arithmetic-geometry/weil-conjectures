## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage` states
`AlgebraicGeometry.Etale.lowerStar_closedImmersion_fullyFaithful_leftInverse_essImage`.
It has one theorem with a `sorry` proof and no definitions. The statement of the node is
unchanged. No new nodes or dependency modules are needed.

Hypotheses and clauses, matched to Lean:

- Arbitrary schemes Z and X: `{Z X : Scheme.{u}}`, with the universe `u` explicitly declared.
- A closed immersion i: `(i : Z ⟶ X) [IsClosedImmersion i]`. No base field, finite-type,
  Noetherian, reducedness, or etaleness hypothesis is imposed.
- Abelian etale sheaves: `Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}` and the same
  category over X. These are sheaves of abelian groups, rather than structure-sheaf modules.
- The direct image i_* is the recorded `lowerStar AddCommGrpCat.{u + 1} i`.
- Fully faithful: `(lowerStar ... i).Full ∧ (lowerStar ... i).Faithful`, i.e. surjectivity
  and injectivity of every map on Hom sets.
- The inverse image i^{-1} is the recorded `upperStar AddCommGrpCat.{u + 1} i`.
  Its being a left inverse is
  `Nonempty (lowerStar ... i ⋙ upperStar ... i ≅ 𝟭 (Sheaf Z.smallEtaleTopology ...))`.
  Composition applies i_* first and i^{-1} second. This is a natural isomorphism, with
  existence asserted in Prop rather than choosing data as an extra conclusion.
- Every sheaf F on X is quantified by `∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  Membership in the essential image is `(lowerStar ... i).essImage F`, whose Mathlib
  definition is existence of G and an isomorphism i_*G ≅ F.
- Exactly the sheaves supported in Z: the membership clause is an `↔` with
  `Scheme.etaleSheafSupport F ⊆ Set.range i.base`. The range is the underlying closed
  subset Z inside X, without identifying the domain scheme with the target.
- The node's explanatory condition on every geometric point off Z is precisely this subset
  condition. The recorded support definition consists of points x admitting a field
  Ω with `IsAlgClosed Ω`, a map `s : Spec (.of Ω) ⟶ X` with `s default = x`, and
  `¬ IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj F)`. Thus absence of x from support
  says every such stalk is zero. In AddCommGrpCat, categorical `IsZero` means the zero
  abelian group. No stalk-independence result is required for this equivalence.
- The finite-type-over-a-field parenthetical uses the same recorded `etaleSheafSupport`.
  Its definition is already available for arbitrary schemes, so this parenthetical
  introduces no extra hypothesis and needs no separate definition or theorem.

Dependency declarations read and used:

- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; its full signature and
  docstring identify sections with base change. The derived declaration is not needed.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` in the same module;
  its full signature and docstring give the sheafified left Kan extension left adjoint
  to lowerStar. The recorded `upperStarLowerStarAdjunction` is used in the natural-language
  proof; the theorem's signature only needs its two functors.
- `def-weil-pbc-geometric-stalks`: Mathlib's
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber` in
  `Mathlib.CategoryTheory.Sites.Point.Basic`, used by the imported support definition.
  Read the definition as sheafToPresheaf followed by the presheaf fiber colimit.
  `Scheme.pointSmallEtale` in `Mathlib.AlgebraicGeometry.Sites.EtalePoint` realizes the
  pointed-etale-neighbourhood fiber; its signature and definition were read.
- `def-weil-geometric-point`: `Scheme.SpecToEquivOfField` and `IsAlgClosed`, as recorded
  in `Mathlib.AlgebraicGeometry.ResidueField`; the signature/docstring identifies maps
  from field spectra with pairs of points and residue-field maps. The support definition
  uses precisely the recorded specialization with an algebraically closed field.
- `def-kun-support`: `AlgebraicGeometry.Scheme.etaleSheafSupport` in
  `Sheaf.AlgebraicGeometry.EtaleSupport`; read its full definition and docstring.
  The additional declarations for complex support and transcendence-degree strata are
  irrelevant to this node and are not used in the signature.
- `def-weil-pbc-scheme-conventions`: its record explicitly says it has no declaration
  of its own. Use `Scheme` and `IsClosedImmersion` under the node's conventions.
- Mathlib's `CategoryTheory.Functor.essImage` in `Mathlib.CategoryTheory.EssentialImage`
  is used for essential image; `Functor.Full` and `Functor.Faithful` supply the usual
  Hom-map conditions. Their definitions/docstrings were read.

Source check: opened https://stacks.math.columbia.edu/tag/04CA, Proposition 59.46.4,
part (2) and its final sentence. It states the three clauses for arbitrary closed
immersions and abelian sheaves, matching this signature. The local literature checkout
contains only citation lists and import tools, not the blueprint text or Stacks sources;
the source node and its complete recorded proof were read locally, and the cited Stacks
proposition was read online. The theorem docstring carries the complete node proof:
counit/full faithfulness, cofinal neighbourhoods off Z, and the stalkwise unit argument.

Edge cases checked before writing:

- Identity immersion: the closed image is all of X, so the support clause is automatic;
  both functors are equivalent to identity and all sheaves are in the essential image.
- Empty closed subscheme: support containment means all geometric stalks vanish; only the
  zero sheaf is in the essential image, as stalk conservativity predicts.
- Empty X: necessarily Z is empty, and the sheaf categories are trivial; every clause
  continues to make sense with no geometric points.
- Zero sheaf: its support is empty and it is the direct image of the zero sheaf.
- Nilpotent closed thickenings with image all of X: no reducedness assumption is added;
  etale invariance is consistent with the unrestricted essential image.
- Universes: schemes are arbitrary in `u`, the existing functor and support definitions
  use abelian groups in `u + 1`, and geometric fields in `u`, exactly as the recorded
  dependencies. No cardinality condition is added.

Searches (2026-10-11):

- msearch.py LeanFinder, query `closed immersion direct image abelian etale sheaves fully
  faithful essential image support`: eight hits, including Scheme.Modules.instFullPushforward
  (structure-sheaf modules and open immersions), IsClosedImmersion.overEquivIdealSheafData,
  Scheme.Etale.forgetFullyFaithful, and ideal-sheaf support facts. None states this theorem.
- msearch.py Loogle, query `CategoryTheory.Functor.essImage`: twelve hits, finding the
  reusable essential-image definition and its API, but not this closed-immersion statement.
- msearch.py grep in Mathlib/AlgebraicGeometry, query
  `lowerStar.*[Cc]losed|[Cc]losed.*lowerStar|essImage.*support`: zero hits.
- msearch.py LeanSearch, query `closed immersion direct image etale abelian sheaves
  essential image support`: unavailable, Internal Server Error. No mathematical verdict
  is inferred from that service failure.
- rg in WeilConjectures and lean/Sheaf for `fullyFaithfulLowerStar`, closed-immersion
  lowerStar, `essImage`, `support`, and `lem-kun-04ca`: existing declarations prove full
  faithfulness and counit invertibility in OpenClosed.ClosedImmersion and
  Etale.UpperLowerStar.ClosedImmersion; they do not state the essential-image condition.
  EtaleSupport supplies the notion of support, reused here. No declaration says all clauses
  of this node, so an existing:true record would be incomplete.
- rg for `lowerStar_closedImmersion_fullyFaithful_leftInverse_essImage` in Mathlib/source
  declarations, upstream names, and lean/Sheaf: no name clash found.

Validation: scompile.py F1 lem-kun-04ca on the module returned exit code 0,
compiled in 2.1 seconds, with no warnings. All variables and universes are explicitly bound.
No statement dispute or node fault was found. The independent second reading is left to
its designated reader.

## Second reading by F1

I independently opened the node and theorem together, all six statement-dependency
nodes and their recorded signatures, and the Stacks source. The downloaded Stacks
`etale-cohomology.tex`, section `section-closed-immersions`, assumes throughout only
that i is a closed immersion. Proposition `proposition-closed-immersion-pushforward`
(Tag 04CA), part (2) and the final sentence, agree with the node. There is no
`statement_change`, new node, or dependency module in this delivery.

My object/hypothesis/conclusion checklist, with verdicts:

- Schemes Z and X: `{Z X : Scheme.{u}}`; correct, arbitrary schemes.
- Closed immersion i: `(i : Z ⟶ X) [IsClosedImmersion i]`; correct, with no field,
  finite-type, Noetherian, reducedness, or etaleness assumption added.
- Abelian sheaves on the small etale sites: `Sheaf Z.smallEtaleTopology
  AddCommGrpCat.{u + 1}` and the corresponding category on X; correct, not modules
  over the structure sheaf or sheaves of sets.
- Direct image: `lowerStar AddCommGrpCat.{u + 1} i`; correct. I read its definition
  in `UpperLowerStar.Defs`: continuous pushforward along etale base change, with
  sections G(V ×_X Z), for arbitrary scheme morphisms.
- Full faithfulness: `(lowerStar ... i).Full` and `(lowerStar ... i).Faithful`;
  correct, respectively surjectivity and injectivity on Hom sets.
- Inverse image as left inverse: `Nonempty (lowerStar ... i ⋙ upperStar ... i ≅
  𝟭 (Sheaf Z.smallEtaleTopology ...))`; correct natural isomorphism, applying
  direct image first and inverse image second. I read `upperStar` and
  `upperStarLowerStarAdjunction`: sheafified presheaf pullback, left adjoint to
  this same direct image, with no etaleness requirement on i.
- Every sheaf F on X: `∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`;
  correct universal quantifier, after the functor-level assertions.
- Essential image exactly the supported sheaves: `(lowerStar ... i).essImage F ↔
  Scheme.etaleSheafSupport F ⊆ Set.range i.base`; correct in both directions.
  I read Mathlib `Functor.essImage`: existence of G with an isomorphism i_*G ≅ F.
  The range is precisely the underlying closed subset meant by Z.
- Vanishing at every geometric point off Z: correct via the support definition.
  I opened `EtaleSupport.lean`: support means existence of an algebraically closed
  field Ω and `s : Spec (.of Ω) ⟶ X` over x with nonzero geometric stalk.
  Thus support containment forbids every such nonzero stalk off the image.
  I also read `pointSmallEtale`, `Point.presheafFiber`, `Point.sheafFiber`, and
  `SpecToEquivOfField`: these are exactly the pointed-neighbourhood colimit and
  geometric points recorded by the dependencies. `IsZero` expresses zero abelian
  group, without selecting a distinguished underlying group presentation.
- Finite-type-over-a-field parenthetical: correct. The recorded support definition
  applies to arbitrary schemes and specializes to the node's kunsupp condition;
  no extra hypothesis is imposed on this theorem. The scheme-conventions dependency
  explicitly introduces no separate notion, and its closed-immersion convention
  agrees with the Mathlib instance used here.

Edge cases: the identity immersion has full image and unrestricted essential image;
for an empty closed subscheme support containment forces all stalks zero; empty X
also forces empty Z. The zero sheaf has empty support. Nilpotent thickenings with
full image remain covered. There is no degree, index set, or characteristic binder
that could exclude n = 0, empty families, or positive characteristic. Universe u is
explicit; the categories and geometric fields follow the recorded dependencies'
universes. Taking u arbitrarily large covers objects of any size, with no finite
cardinality or base-field constraint.

Independent searches (2026-10-11):

- msearch LeanFinder: `abelian sheaf vanishes outside closed subscheme essential
  image pushforward`; eight hits, about quasi-separated schemes, ideal sheaves,
  and zero loci, none the abelian etale essential-image statement.
- msearch Loogle: `CategoryTheory.Functor.essImage`; twelve hits, reusable essential
  image API, no match for the present theorem.
- msearch grep: `essImage.*[Ss]upport|[Ss]upport.*essImage|lowerStar.*[Cc]losed`;
  no Mathlib hits.
- Direct rg in Mathlib, WeilConjectures and repository lean/Sheaf for support with
  essImage and the proposed theorem name: no duplicate declaration. I opened
  `SixFunctors.OpenClosed.ClosedImmersion` and
  `Etale.UpperLowerStar.ClosedImmersion`: they supply full faithfulness/counit
  results, not the essential-image clause. The upstream name index also has no
  proposed-name clash. The existing support notion is reused, not copied.

No mismatch was found; the Lean and node were left unchanged. The docstring gives
all node proof steps: counit/full faithfulness, cofinal complement neighbourhoods,
vanishing off Z, the stalkwise unit on and off Z, and conservativity. The sole
proof is `sorry`; there are no definitions or hollow data. Imports, namespace,
source citations, blueprint marker, line widths, and explicitly bound variables
are correct. The node's lean.statement is exactly equal to the signature in the
file. Independent scompile returned exit 0 in 2.1 seconds with no warnings.
