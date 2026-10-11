## Worker report

The module `lean/Sheaf/AlgebraicGeometry/NormalGenericConstant.lean` states
`AlgebraicGeometry.Etale.isIso_constantSheaf_to_generic_lowerStar`, with its sole proof
`sorry`. It gives exactly the generic-point assertion of the node; no statement correction,
new definition node, or dependency module was needed.

Hypothesis and clause correspondence:

- A scheme V: `(V : Scheme.{u})`.
- Noetherian: `[IsNoetherian V]`, the Mathlib class meaning locally Noetherian and compact.
  The scheme-conventions node is a convention collection with no declaration of its own.
- Integral: `[IsIntegral V]` from `Mathlib.AlgebraicGeometry.Properties`, the recorded
  declaration of `def-pc-integral-scheme`. This supplies nonemptiness and irreducibility.
- Normal in the node's specified sense: `(hV : IsNormalScheme V)`, importing
  `Sheaf.AlgebraicGeometry.NormalScheme`. This is the recorded declaration of
  `def-sbc-normal-dominant-galois`: integrality and an integrally closed domain at every stalk.
- Generic point eta: `genericPoint V`, uniquely determined on an integral scheme.
- K = kappa(eta): `V.residueField (genericPoint V)` occurs in the domain of e.
  `Scheme.residueField` in `Mathlib.AlgebraicGeometry.ResidueField` is precisely the stalk
  modulo its maximal ideal, as recorded by `def-weil-residue-field`.
- Generic inclusion: `V.fromSpecResidueField (genericPoint V)` (written out at each occurrence). Its domain is
  `Spec (V.residueField (genericPoint V))`, and its image is the generic point. This uses the
  residue field itself, rather than substituting the separately defined stalk function field.
- Finite abelian group M: `(M : AddCommGrpCat.{u + 1}) [Finite M]`. This is a finite underlying
  type with an additive commutative group structure, without a chosen enumeration.
- Constant sheaf on V: `(constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M`.
  `CategoryTheory.constantSheaf` in `Mathlib.CategoryTheory.Sites.ConstantSheaf` is the
  sheafification of the constant presheaf, the match of `def-weil-pbc-constant-sheaf`.
- Abelian etale sheaves: `Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}` is the category
  in which the map is elaborated. `CategoryTheory.Sheaf` in
  `Mathlib.CategoryTheory.Sites.Sheaf` and `Scheme.smallEtaleTopology` in
  `Mathlib.AlgebraicGeometry.Sites.Etale` give the recorded specialization of
  `def-weil-pbc-abelian-etale-sheaves`.
- Direct image: `Etale.lowerStar AddCommGrpCat.{u + 1} e`, imported through
  `WeilConjectures.ConstructibleSheaf.Defs` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, uses the recorded declaration of
  `def-weil-pbc-direct-image`. It evaluates F on base-changed etale objects.
- The natural map: the unit of `Etale.upperStarLowerStarAdjunction`, composed with
  `Etale.lowerStar.map` of `(Scheme.upperStarConstantSheafIso ... e).app M`'s hom.
  The latter declaration is in `WeilConjectures.ConstructibleSheaf.Defs`, and identifies
  the pullback of the constant sheaf on V with the constant sheaf on Spec K. Thus the
  composite has exactly source M_V and target e_* M_K. The isomorphism is the canonical
  comparison from the constant-sheaf/global-sections adjunctions, so this composite is the
  section-restriction natural map described in the node, not an arbitrary map.
- The conclusion that this map is an isomorphism: `IsIso` of the displayed composite.

The source blueprint file was absent from local literature. I read its complete statement
and proof on the project server at the exact recorded path. They agree with the node.
The declaration docstring carries the full corrected componentwise proof recorded by stage 1,
with the cited lemma ids; in particular it uses the localization-domain argument rather than
an unsupported identification of generic fibres with fields.

Edge cases: integrality excludes the empty scheme, as the node requires. The trivial finite
abelian group is included. Schemes that are fields, arbitrary characteristic, and positive
-dimensional normal schemes are included; there is no separatedness, affine, smoothness,
or finite-type assumption on V. Empty etale test objects have empty component sets and
trivial section groups, so the proposed proof applies there. The coefficient universe is
one above the scheme universe, the universe used by the existing direct-image API. Finite
abelian groups admit representatives in this universe; no cardinality restriction is imposed
on the mathematical finite groups. Every variable and the universe u is explicitly bound.

Searches performed using `/home/ubuntu/weil-launcher/msearch.py` (logged in searches.jsonl):

- LeanSearch, "constant abelian etale sheaf on normal integral scheme is direct image from
  generic point": service returned Internal Server Error; recorded unavailable.
- LeanFinder, "constant etale sheaf on normal integral scheme direct image generic point":
  eight hits, including normalizationDiagram and germToFunctionField; none is this theorem.
- Loogle, "CategoryTheory.constantSheaf, CategoryTheory.IsIso": three hits about the
  constant-sheaf/global-sections adjunction counit, none about a generic inclusion.
- Mathlib grep, "constant.*generic|generic.*constant|isIso.*constantSheaf": five hits in
  ConstantSheaf.lean, all unrelated constant-sheaf counit results.
- Project rg over WeilConjectures and lean/Sheaf for normal/constant/generic combinations
  located `Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed` in
  `WeilConjectures.ConstructibleSheaf.FinitePushforward`. Its signature and docstring were
  read in full: arbitrary module coefficients and a conjunction with every nonempty open
  immersion, no Noetherian or finiteness hypotheses. It is a stronger related theorem,
  not exactly this node's statement, and was not recorded as an existing realization.
- `grep -rn 'lem-fin-normal-generic-constant' WeilConjectures` found no declarations.
  `dag/lean_names_upstream.json` records the related theorem under the other blueprint id
  `lem-weil-pbc-normal-constant-generic`. Searches of Mathlib, WeilConjectures and lean/Sheaf
  for the new full declaration suffix found no collision.

Server compilation by scompile.py succeeded in 2.0 seconds, without warnings or errors.
No node faults or STATEMENT-DISPUTED concerns were found.

## Second reading by E1

I independently read the node statement, its recorded source place (blueprint node
`lem-fin-normal-generic-constant`, order 1606, whose Stacks content is the generic
constant-sheaf lemma), and the complete Lean declaration.

The correspondence is exact item by item:

- The Noetherian scheme (V) is `(V : Scheme.{u}) [IsNoetherian V]`.
- Integrality is `[IsIntegral V]`, and normality in the dependency's specified sense is
  `(hV : IsNormalScheme V)`; `IsNormalScheme` is the recorded integral, stalkwise
  domain and integrally-closed condition.
- The generic point η is rendered by `genericPoint V`.
- The residue/function field (K=\kappa(\eta)) and generic inclusion
  `Spec K -> V` are rendered by `V.fromSpecResidueField (genericPoint V)` at every
  occurrence.  This is the canonical map from the residue field of the generic point.
- A finite abelian group (M) is `(M : AddCommGrpCat.{u + 1}) [Finite M]`.
- The constant sheaf \(\underline M_V\) is
  `(constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M`.
- The target category is the abelian etale-sheaf category supplied by the explicit
  `constantSheaf` and `Etale` APIs, and direct image is
  `Etale.lowerStar AddCommGrpCat.{u + 1} e`.
- The natural map is the adjunction unit followed by the lower-star image of the
  canonical `Scheme.upperStarConstantSheafIso` comparison.  Its displayed composite
  has exactly source \(\underline M_V\) and target (e_*\underline M_K).
- The conclusion `IsIso` applies to this map, exactly matching the source's assertion
  that it is an isomorphism.

No hypothesis, object, quantifier, or conclusion clause is missing or strengthened.
The separate `[IsIntegral V]` is the explicit integral hypothesis in the node and is
logically consistent with the integral conjunct inside `IsNormalScheme`; it introduces
no additional mathematical restriction.  No separatedness, finite type, affine,
smoothness, or characteristic assumption is present.

Edge cases checked: integrality rules out the empty scheme as in the source; the trivial
finite abelian group is admitted; (n=0) is irrelevant to this statement; arbitrary
characteristic and field-valued schemes are admitted; empty etale test objects give the
usual trivial section groups; and the explicit universe (u), with coefficients in
`AddCommGrpCat.{u + 1}`, does not exclude finite coefficient groups.  The generic-point
map is defined for every integral scheme.

I repeated the duplicate-definition searches with `msearch.py`, `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`, and checked the upstream name index.  The only
near match is `Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed`, which is a
different theorem (module coefficients, a stalk map, and an additional open-subscheme
conjunction), so it cannot realize this node.  No exact declaration exists.

The first worker's statement and module are correct.  I found no mismatch and made no
source or statement correction.  Recompilation with `scompile.py` succeeded with only
the permitted `sorry` proof warning.

The first dry run exposed a signature-parser limitation with an internal `let e :=` in
the theorem type. The final signature writes the generic inclusion at each occurrence,
so the parser and Lean read the same complete signature.
