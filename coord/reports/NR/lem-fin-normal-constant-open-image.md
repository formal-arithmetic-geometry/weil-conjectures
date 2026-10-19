## Worker report

The module `Sheaf.AlgebraicGeometry.NormalConstantOpenImage` states
`AlgebraicGeometry.Etale.isIso_constantSheaf_to_open_lowerStar`, with proof `by sorry`.
It defines no new notion and leaves the natural statement and all dependencies unchanged.

Hypothesis and conclusion correspondence:

- Schemes Y and V: `{Y V : Scheme.{u}}`.
- Y Noetherian: `[IsNoetherian Y]`, Mathlib's locally Noetherian and compact scheme class.
- Y normal: `(hY : IsNormalScheme Y)`, the recorded predicate requiring integrality and
  domain, integrally closed stalk rings. The separately stated integrality of Y is
  `[IsIntegral Y]`. These express exactly the node's “normal integral”.
- Open immersion v: `(v : V ⟶ Y) [IsOpenImmersion v]`.
- Nonempty open: `[Nonempty V]`. No density assumption is added: nonempty opens of an
  integral scheme are dense.
- Finite module M: `(Λ : Type (u + 1)) [CommRing Λ]`,
  `(M : ModuleCat.{u + 1} Λ) [Finite M]`. The coefficient ring is the commutative ring
  explicitly identified in proof step 1; it is arbitrary, not assumed finite. Here finite
  means the underlying finite set, as in the blueprint proof's finite constant sheaf and
  the neighboring finite locally constant module material. The zero module is included.
- Constant sheaves are `(constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M`
  and the corresponding expression on V, using sheafification of the constant presheaf.
- Direct image on small etale sites is `lowerStar (ModuleCat.{u + 1} Λ) v`.
- The canonical map is the unit of `upperStarLowerStarAdjunction` at the constant sheaf,
  followed by `lowerStar.map` of `(Scheme.upperStarConstantSheafIso ... v).app M).hom`.
  The latter comparison is constructed by `Adjunction.leftAdjointUniq` from the
  constant-sheaf/global-section adjunctions and the terminal-section formula for direct
  image. Consequently its adjoint sends m to the constant section m, precisely as the
  node's proof step 3 specifies. The displayed arrow has source M_Y and target v_* M_V.
- “Is an isomorphism” is `IsIso` of this specific composite; it asserts no arbitrary
  existence of a comparison and does not replace the map by an unrelated isomorphism.

Dependency declarations and source reading:

- `def-weil-pbc-scheme-conventions` is a convention-only record; the relevant notions are
  Mathlib `AlgebraicGeometry.Scheme`, `IsIntegral`, `IsOpenImmersion`, and `IsNoetherian`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`; signature, fields and docstring read.
- `def-sbc-normal-dominant-galois`: `Sheaf.AlgebraicGeometry.NormalScheme`,
  `AlgebraicGeometry.IsNormalScheme`; full definition and docstring read and used.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; signature and docstring read. This is available
  through the public imports of the normal-scheme and Noetherian modules.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; its full class and docstring and the stronger
  `IsNoetherian` class encoding the item's Noetherian hypothesis were read.
- `def-constructible-constant`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.Sheaf.IsConstant`, `constantSheaf`, and `constantSheafAdj`; the complete
  declarations and documentation were read. This theorem needs the actual constant
  functor rather than the essential-image predicate.
- `def-weil-pbc-etale-sheaves`: recorded module
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` is publicly imported; its source and
  mixed record explain the existing `Sheaf ... (ModuleCat.{u + 1} Λ)` encoding used here.
- `def-weil-pbc-direct-image` and `def-weil-pbc-inverse-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `Etale.lowerStar`,
  `Etale.upperStar`, and `Etale.upperStarLowerStarAdjunction`; definitions and docstrings
  read, including the objectwise base-change formula for direct image.
- `lemma-constructible-pullback-constant`: `WeilConjectures.ConstructibleSheaf.Defs`,
  `Scheme.upperStarConstantSheafIso`; complete declaration, section parameters and body
  read. Its canonical isomorphism is used directly in the signature.
- Proof dependency `lem-weil-pbc-normal-constant-generic-open-unit`:
  `Sheaf.AlgebraicGeometry.NormalConstantOpenUnit`,
  `Etale.isIso_unit_constantSheaf_open_unit`; full theorem and proof read. Its module is
  imported without `public` as required for a proof-only dependency. Its arbitrary-module
  result supplies the unit-isomorphism step, but is not the item's exact statement.

Sources: read the item's entire blueprint statement and proof in
`sec-smooth-purity/sk-prop-a1-kummer/lem-fin-normal-constant-open-image.md` and the local
Stacks `etale-cohomology.tex`, label `lemma-push-constant-sheaf-from-open` (Tag 09Z5),
including both assertions and their proofs. No statement correction is needed.

Edge cases checked before writing: the empty Y is excluded by integrality and empty V by
nonemptiness, as in the node; M = 0 is allowed, including coefficients in the zero ring;
V = Y and v the identity is allowed; a proper dense open is allowed with no surjectivity,
affineness or quasi-compactness assumption on v. No characteristic, ring-finiteness or
Noetherian coefficient hypothesis is imposed. The shared scheme universe u and coefficient
universe u+1 follow the recorded six-functor and constant-sheaf interfaces.

Searches (the launcher also records the msearch responses in searches.jsonl):

- `msearch.py leanfinder`, “A constant finite module etale sheaf on a normal integral
  Noetherian scheme equals its direct image from a nonempty open subscheme”: eight hits,
  concerning structure-sheaf sections and integrality, no exact statement.
- `msearch.py leansearch`, “A constant sheaf of modules on a normal integral scheme is
  isomorphic to direct image from a nonempty open subscheme”: eight hits on constant
  sheaves, their essential image, and structure-sheaf modules, no normal-open theorem.
- `msearch.py loogle`, `"constantSheaf", "IsIso"`: one hit on the counit of the
  constant-sheaf adjunction; different statement.
- `msearch.py grep`, `constantSheaf.*[Oo]pen|[Oo]pen.*constantSheaf`, in Mathlib's
  AlgebraicGeometry: zero hits.
- `rg` of `normal.*constant|constant.*normal|normalConstant|NormalConstant|normal_constant`
  in both the source project and `lean/Sheaf` found the existing generic/open unit
  theorems, generic-point comparison and references from the neighboring lisse theorem;
  none gives this exact Noetherian, finite-module canonical-map statement.
- `rg` of the item id in the source project and the upstream name index: no declaration.
  `rg` of `isIso_constantSheaf_to_open_lowerStar` in project sources: no existing name.

The previous attempt mistook the Q01 reviewed stage-1 split for a stage-2 completion.
The base node has no lean record. This delivery supplies that missing statement rather
than resplitting or altering the already reviewed DAG proof. No new nodes, dependency
repairs or disputed statements.

## Second reading by NR

I independently opened the sandbox node and Lean file, the blueprint source at
`sec-smooth-purity/sk-prop-a1-kummer/lem-fin-normal-constant-open-image.md`, and
Stacks `etale-cohomology.tex`, label `lemma-push-constant-sheaf-from-open`
(Tag 09Z5), including the whole statement and proof. The blueprint explicitly calls
M a finite set in its component argument; Stacks proves the underlying assertion
for any set E. Thus the item's finite-module hypothesis means finite underlying
set here, not merely finite generation over an arbitrary ring. Stacks assumes
integral and normal, without any additional standing coefficient or characteristic
hypothesis. The blueprint's explicit Noetherian hypothesis is retained.

The independent object/hypothesis/conclusion checklist is:

- Y and V are schemes: `{Y V : Scheme.{u}}`. Exact; no affineness, separation,
  finite type over a field, or base scheme is assumed.
- Y is Noetherian: `[IsNoetherian Y]`. Exact: I read the Mathlib class in
  `Mathlib.AlgebraicGeometry.Noetherian`; it extends local Noetherianity and
  `CompactSpace`, the usual Noetherian-scheme condition, rather than only the
  locally Noetherian predicate recorded at `pqf-def-locnoeth`.
- Y is integral: `[IsIntegral Y]`. Exact: the dependency's Mathlib class in
  `Mathlib.AlgebraicGeometry.Properties` requires nonemptiness and domain sections
  on every nonempty open, equivalent to the node's reduced irreducible condition.
- Y is normal: `(hY : IsNormalScheme Y)`. Exact: I read the actual definition in
  `Sheaf.AlgebraicGeometry.NormalScheme`; it is `IsIntegral Y` together with
  `IsDomain` and `IsIntegrallyClosed` for every stalk. Its integrality conjunct
  repeats the explicitly given integral condition without strengthening it.
- The named arrow is an open immersion: `(v : V ⟶ Y) [IsOpenImmersion v]`.
  Exact: I read the abbreviation in `Mathlib.AlgebraicGeometry.OpenImmersion`,
  which uses the open-immersion property of locally ringed spaces.
- The open is nonempty: `[Nonempty V]`. Exact; no extra density or surjectivity
  hypothesis. Nonempty opens of the given integral Y are dense.
- M is a finite module over its commutative coefficient ring:
  `(Λ : Type (u + 1)) [CommRing Λ]` and
  `(M : ModuleCat.{u + 1} Λ) [Finite M]`. Exact in the blueprint's finite-set
  sense explained above. Λ is the ring introduced by step 1 of the DAG proof;
  no finiteness, Noetherianity, field, nontriviality, or invertibility is assumed.
- The source is the constant module sheaf M_Y:
  `(constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M`.
  Exact: I read `constantSheaf`, `constantSheafAdj`, and `Sheaf.IsConstant` in
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`; the functor sheafifies the
  constant presheaf and is adjoint to sections at the terminal object.
- The target is v_* M_V: the inner comparison ends in
  `(constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M`,
  and `lowerStar (ModuleCat.{u + 1} Λ) v` sends it to the sheaf on Y.
  Exact: I read the recorded `lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, including its
  objectwise base-change formula. This is direct image on the small etale sites,
  not pushforward of modules over the structure sheaf or derived direct image.
- The map is canonical: the signature composes
  `(upperStarLowerStarAdjunction ... v).unit.app M_Y` with
  `(lowerStar ... v).map ((Scheme.upperStarConstantSheafIso ... v).app M).hom`.
  Exact: I read `upperStar`, its adjunction, and the full construction of
  `Scheme.upperStarConstantSheafIso` in `WeilConjectures.ConstructibleSheaf.Defs`.
  The latter is `Adjunction.leftAdjointUniq` for the constant/global-section
  adjunctions after the terminal-section direct-image comparison. Its adjoint
  therefore sends m to the constant section m. The composite is precisely c_v
  of DAG proof step 3, with the correct direction and the same coefficient module.
- This specific map is an isomorphism: `IsIso` of that composite. Exact; there
  is no existentially chosen map, arbitrary isomorphism, or missing clause.
  All objects precede the assertion, as in the node.

I also opened every statement-dependency node and its recorded Lean interface.
`def-weil-pbc-scheme-conventions` is explicitly convention-only.
`def-constructible-constant` supplies the Mathlib constant-sheaf construction above;
`def-weil-pbc-etale-sheaves` explicitly permits the existing
`Sheaf T.smallEtaleTopology (ModuleCat.{u+1} Λ)` encoding used by this theorem.
I read its actual `WeilConjectures.AlgebraicGeometry.EtaleSheaves` module as well
as the coefficient convention in `ConstructibleSheaf.Defs`. The recorded direct
and inverse images accept precisely this encoding. I opened the proof dependency
`Sheaf.AlgebraicGeometry.NormalConstantOpenUnit`: its theorem accepts an integral
scheme with all stalks integrally closed, an arbitrary module, and a nonempty open
immersion. It supplies the unit-isomorphism step with no hidden instance. The
canonical pullback comparison supplies the second factor. No new definition node
or dependency module was delivered, so there is no sibling interface to repair.

Edge cases: empty Y is excluded by integrality and empty V by the explicitly
nonempty-open hypothesis, exactly as in the sources. A zero module and a zero
coefficient ring are allowed. The identity open and proper nonempty opens are
allowed; v need not be given as a particular `Opens` inclusion. No index set or
integer n occurs, and there is no characteristic restriction. Universe u is
bound explicitly; schemes use u and coefficients/modules use u+1, precisely the
recorded small-etale six-functor convention. There is no independent smaller
universe of test objects, additional universe equation, or quantified hypothesis
that becomes vacuous. All variables and universes in the signature are bound.

Independent searches used different terms from the first worker:

- LeanFinder, "Restriction to a dense open subscheme preserves the sections of a
  constant etale sheaf over a normal integral scheme": eight hits concerning
  structure-sheaf sections and restriction, none the stated module-sheaf map.
- LeanSearch, "A finite constant sheaf of modules is the direct image of its
  restriction to a dense open in a normal scheme": eight hits on constant sheaf
  predicates and structure-sheaf module restriction, none this statement.
- Loogle, `"lowerStar", "IsIso"`: zero hits.
- `rg` over Mathlib, upstream `WeilConjectures`, and this project's `lean/Sheaf`,
  for direct image/constants and dense/constants, and inspection of the normal
  constant modules: only the generic-point theorem, the normal-open unit theorem,
  their conjunction, and related coefficient/coherence constructions. I opened
  upstream `ConstructibleSheaf/FinitePushforward.lean`: its conjunction states
  the adjunction units for arbitrary modules, not this specific composite with
  the item's Noetherian and finite hypotheses. It is a usable stronger proof
  dependency, not an exact existing declaration of this item. The generic-point
  canonical-map theorem has a different morphism and abelian-group coefficients.
- `rg` of the proposed full declaration name and the item id in upstream Lean
  and `dag/lean_names_upstream.json` found no exact existing declaration or name
  collision. The project's lisse theorem contains only a docstring citation.

H5/H6/H8/H9: the module introduces no definitions, hollow data, private copies,
local notation, or local instances. Its single theorem has only `by sorry` as
proof. Module and theorem docstrings give the source and exact blueprint tag;
the theorem docstring follows DAG proof steps 1, 2, and 3, including the
canonical-map identification and inverse of the composite. Imports and naming
follow the convention; lines fit 100 characters.

No mathematical, signature, dependency, or docstring mismatch was found. I left
the Lean module and node unchanged and appended only this independent audit.
The node's `lean.statement` was checked verbatim against the file's signature.
The required `scompile.py NR lem-fin-normal-constant-open-image` compile passed
for the delivered module, in both sandbox and library contexts, with no errors
or warnings (2.4 seconds per context).
