## Worker report

The module `Sheaf.Paper.ZlImmersionFilteredReductionTransport` states
`WeilConjectures.zlImmersionFilteredReductionTransport` with `sorry`. Its two
Prop-valued helper definitions only package the image-filtration and actual-unit
transport clauses of this node. Their data are explicit propositions. There are
no new DAG nodes, dependency repairs, or changes to the mathematical statement.

Source read: the current `literature/blueprint/latest/blueprint/` file
`sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`,
paragraph beginning “For a general constructible sheaf” and the final gluing
paragraph, including the exact localization sequence and the zero-stalk purity
argument. The item's seven accepted proof steps are reproduced in the theorem
docstring. This is stage 2: no theorem is proved here.

Hypothesis and clause correspondence:

- The finite-field datum, prime power and algebraic closure are `D : FiniteFieldDatum.{u}`.
  The coefficient prime and its inequality are `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
  The algebraic closure of Q_l is `Ω : Type v`, with the existing field, Padic-algebra
  and `IsAlgClosure` instances. The specified complex identification is
  `iota : Ω ≃+* ℂ`, coerced to the ring homomorphism expected by punctual weights.
  The coefficient universe v remains independent of the scheme universe u.
- `X`, `Y` and `V` are schemes over `Spec D.k₀` in `Over`. The paired
  `LocallyOfFiniteType` and `QuasiCompact` hypotheses mean finite type;
  `IsSeparated` supplies separatedness. For Y and V these are inherited properties
  of the closed and open subschemes of the given finite-type separated X,
  recorded explicitly because the heart interfaces require those structures.
- `j : V ⟶ X` with `[IsOpenImmersion j.left]` and `i : Y ⟶ X` with
  `[IsClosedImmersion i.left]` are independent. There is no complement, disjointness,
  reducedness or reality hypothesis. The existing `zlFiberMap` inside the recorded
  operations performs their geometric base changes.
- All objects and arrows belong to `sfCommonStageWeilSheaf D l hl _ Ω`, the existing
  full heart subcategory of actual common-stage fixed pairs. The restriction is
  existing `zlWeilPull`, owned by `def-zl-weil-ind-sheaf-category`. Open image is
  the existential J, pinned by `_adjJ : J ⊣ zlWeilPull D l hl Ω j`. This universal
  property determines extension by zero and its Weil action up to unique
  adjunction-compatible isomorphism; no declaration owned by the open-image
  theorem is used in the signature.
- The existential I is the restriction of the existing actual closed derived
  image: the carrier equality is `I ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙
  sfModelWeilDerivedPush ... i`. The actual inverse-image/direct-image adjunction is
  supplied as `adj`; its unit is normalized by `HEq` with
  `(sfModelWeilDerivedAdjunction ... i).unit.app H.obj`. Thus neither the functor
  nor its unit is an arbitrary substitute. Restricting the existing functor
  changes only heart membership proofs, so the carrier equality is available.
- `ZlImmersionImageFiltration` asserts `PreservesFiniteLimits T` and
  `PreservesFiniteColimits T`, exactly the dependency's definition of exactness.
  Its next clause quantifies over every sheaf F and every real weight w and
  preserves `SfIsPunctuallyPureOfWeight` at precisely w. The theorem asserts this
  package for both the specified open image and I.
- A specified finite filtration is `G : Fin (n + 1) ⥤ sfCommonStageWeilSheaf ...`.
  `IsZero (G.obj 0)` gives its zero beginning; monicity of its maps gives its
  subobjects. This is equivalent to monicity of the consecutive maps, since all
  other arrows are their composites. Its ambient sheaf is its last object;
  identifying that object with any given G is harmless and reversible.
- The successive quotient is exactly `cokernel (G.map
  (homOfLE s.castSucc_le_succ))`. The arbitrary list `weights : Fin n → ℝ`
  assigns each quotient its given weight. Neither sorting nor distinctness is
  imposed. The output filtration is literally the diagram `G ⋙ T`, rather than
  an independently selected filtration.
- Every output consecutive quotient has an isomorphism e to T of the input
  quotient. The equation `cokernel.π _ ≫ e.hom = T.map (cokernel.π _)` makes it the
  quotient comparison. Since e lives in the Weil heart, it is a Weil isomorphism.
  The adjoining purity clause retains the same `weights s`. Initial zero and
  monicity of all image arrows are explicitly asserted.
- For every common upper bound w on that particular list, the last image term is
  `SfIsMixedOfWeightsAtMost ... w`. The final clause also preserves the existing
  mixedness predicate for every sheaf and every bound, independently of choosing
  a presentation. Unbounded mixedness follows by taking an upper bound of any
  finite list of real weights (0 for an empty list).
- The final clause assumes only `Surjective i.left` in addition to closedness,
  then quantifies over every H and asserts `IsIso (adj.unit.app H)`. General i
  may be any closed immersion; specializing it to e supplies the second paragraph
  without any relation to j.
- `ZlImmersionUnitFiltration` accepts a specified diagram G ending at the actual
  restriction K via `last : G.obj (Fin.last n) ≅ K`, with its original weights.
  It produces a filtration P of H, a natural isomorphism `P ≅ G ⋙ I`, and
  `finish : P.obj (Fin.last n) ≅ H`. The endpoint equation
  `finish.hom ≫ eta = comparison.hom.app (Fin.last n) ≫ I.map last.hom`, together
  with naturality, says at every term that inclusion into H followed by eta is
  the prescribed inclusion of I(G_s) into I(K). Since eta is invertible, these are
  precisely the inverse-image subobjects `eta^{-1}(I G_s)`. This is the universal
  pullback characterization, including its actual map to H; an unrelated
  filtration could not satisfy this equation.
- The transported filtration explicitly starts at zero, has monic inclusion maps,
  has quotient isomorphisms to I of the original quotients, is pure at each
  original assigned weight, and retains every common upper bound on that list.
- Reduction is a specialization of this general surjective-closed clause:
  take `Y = Over.mk (X.left.nilradical.subschemeι ≫ X.hom)` and i the corresponding
  arrow induced by `X.left.nilradical.subschemeι`. The reduction theorem cited in
  the proof docstring supplies closedness and surjectivity. Finite type and separatedness follow by
  composition with the closed immersion. Thus no reducedness assumption on X is
  needed and no reduction case is lost.

Dependency interfaces read and used:

- `Sheaf.Paper.AdicPunctualWeights`: `SfIsPunctuallyPureOfWeight`,
  `SfIsMixedOfWeightsAtMost`, and `SfPunctualEigenvalue`; read their full definitions.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilForget`, and `sfCommonStageWeilSheaf`; their full definitions
  identify the existing fixed pairs and heart carrier.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`,
  `sfCommonStageHeart`, and the recorded rational-heart definitions.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded
  `commonStageDerivedPullback` and its normalized representative characterization;
  `zlWeilPull` in `Sheaf.Paper.WeilIndSheafCategory` restricts that actual pullback.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the recorded
  `sfQcqsCompactSupportRealization` and its projection-normalized specification.
  The open image is now quantified as J with its adjunction to the recorded
  restriction; `Sheaf.Paper.ExtensionByZeroPunctual` is not imported.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage` and
  `sfDirectImageReductionComparison`. The added owner node
  `def-weil-common-stage-derived-direct-image` records
  `Sheaf.Paper.SfCommonStageDirectImage`, giving the normalized common-stage and
  fixed-pair extension `sfModelWeilDerivedPush`
  and `sfModelWeilDerivedAdjunction`, which are used directly in the signature.
- Mathlib: `AlgebraicGeometry.IsOpenImmersion` (OpenImmersion.lean, lines 38--44),
  `AlgebraicGeometry.IsClosedImmersion` (Morphisms/ClosedImmersion.lean, lines 42--47),
  `Scheme.nilradical`, `Scheme.IdealSheafData.subscheme` and `subschemeι`
  (IdealSheaf/Basic.lean and Subscheme.lean, lines 454 and 472).
  `PreservesFiniteLimits` and `PreservesFiniteColimits` are the recorded exactness
  interface (Limits/Preserves/Finite.lean); `exactFunctor_iff` confirms their conjunction.
  The scheme-properties dependency is an index of these notions, not a separate definition.

The twelve private proof-only imports of the returned head have been removed,
as requested by H9. The proof route remains in the theorem docstring. The public
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` import, referenced only in that
docstring, has also been removed. Statement-owner imports are public, including
`Sheaf.Paper.WeilIndSheafCategory` and `Sheaf.Paper.SfCommonStageDirectImage`.

Searches actually run (all through the required wrapper where indicated):

- LeanFinder: “Exact open extension by zero and closed direct image of Weil sheaves
  preserve prescribed pure quotient filtrations, and surjective closed immersion
  adjunction unit is an isomorphism”. Eight hits, mostly scheme-module open
  adjunction results and affine localization; none states this Weil-heart assertion.
- Loogle: `CategoryTheory.Functor, CategoryTheory.Limits.cokernel`. Twelve hits,
  including `cokernelComparison`, `PreservesCokernel.iso` and their equations.
  These are generic quotient comparison tools, not the immersion/weight/unit theorem.
- LeanSearch: “An exact functor preserves a specified finite filtration and its
  cokernel quotients”. Eight hits on exact functor definitions and their bundling,
  not this assertion about actual Weil functors and assigned weights.
- Mathlib grep via msearch: `cokernelComparison|mapCokernel|IsLeftAdjoint` in
  CategoryTheory: 25 hits, generic adjunction tools. The more specific
  `Weil.*(filtration|reduction)|filtration.*(cokernel|pure)` gives zero hits.
- Direct rg on `lean/WeilConjectures` and `lean/Sheaf` for immersion/filtered/reduction,
  prescribed filtrations, and filtration declarations found generic decreasing
  filtrations, classical heart transport and `ReducedFrontierMixedGluing`. The latter
  has a related partial `ZlFrontierFiltrationPreservation`, but omits the arbitrary
  real-weight purity clause and actual quotient isomorphisms and only states the
  frontier gluing conclusion. It does not state this item. Importing its consumer
  module would also reverse the mathematical dependency. This delivery packages
  the additional clauses directly without copying its notions or any operation.
- Direct rg on the two project source roots for this node id and for
  `zlImmersionFiltered`, `sfModelWeilDerivedAdjunction`, `zlClosedWeil` and
  `zlWeilPull_isLeftAdjoint` found the actual common-stage derived adjunction and
  local-stalk interfaces; no theorem matching the item. A separate full-name
  search in Mathlib, both project roots and `dag/lean_names_upstream.json` found
  none of this delivery's three declaration names already defined.

Edge cases checked: n=0 gives a singleton zero diagram and no quotient conditions;
for unit transport its endpoint identifies H with zero. Empty V, Y or X are
permitted without nonemptiness assumptions. The identity immersion and a surjective
nilpotent thickening such as Spec(F_q[epsilon]/epsilon^2) admit the same actual-unit
statement. Repeated terms have identity arrows and zero cokernels; the existing
purity predicate is vacuous on zero, so any assigned weight is allowed. Repeated,
unordered and negative weights are unrestricted. No reality or reducedness test
appears. The independent coefficient universe is retained.

Validation of the returned head was successful mechanically but did not detect
the missing owner dependencies and theorem-owned open declaration. The repaired
source is compiled and delivered afresh; see the repair record below.

## Second reading by Q20

Author's second reading, with the original JSON statement and final source open;
the maintainer supplies the independent review. The hypothesis list is exactly
finite-field/coefficient data, separated finite-type schemes, and independent open
and closed immersions. Finite-type and separated structures on their source
subschemes are inherited, not mathematical restrictions. Both image assertions
contain exactness and purity of every real weight, plus the actual termwise image
filtration and quotient comparisons. The quotient comparison equation was checked
for its direction: it starts at T(G_{s+1}), through the cokernel of T(phi_s), and
ends at T(cokernel(phi_s)); the other side is T of the original cokernel projection.
The output purity clause uses the cokernel of T(phi_s), so no identification of
nonidentical quotient objects is silently assumed.

For transport, naturality of `comparison` plus the endpoint equation was checked
at an arbitrary s: composing `P.map (s → last)` with `finish.hom` and eta equals
`comparison.hom.app s` followed by I of the specified inclusion into K. As eta
is the actual normalized unit and is asserted invertible, P is exactly its
inverse-image filtration. The original list of weights remains the index of all
quotient and bound assertions. Reduction specializes the same general clause.
The return identified dependency ownership and import defects, repaired as below.
No mathematical clause, filtration helper, closed-image pin, or unit-transport
clause was changed. The new open quantifiers supply J and its actual left
adjunction; the same image-filtration predicate now applies to J. This preserves
the previous mathematical content because a left adjoint to the fixed restriction
is unique up to its unique adjunction-compatible isomorphism.

## Repair of returned head dfe995b4d70f

1. H2, ownership: added the existing landed definition nodes
   `def-zl-weil-ind-sheaf-category` (owner of `zlWeilPull`) and
   `def-weil-common-stage-derived-direct-image` (owner of `sfModelWeilDerivedPush`
   and `sfModelWeilDerivedAdjunction`) to `stmt_deps`. Read both nodes' complete
   statements and Lean records, and re-read the declarations and docstrings in
   `WeilIndSheafCategory.lean` and `SfCommonStageDirectImage.lean`. The latter node
   is in `sec-smooth-purity`; its declarations are the existing finite-field
   common-stage adjoints, precisely the interfaces used here.
2. H2, open operation: removed the signature's use of `zlOpenWeilShriek` and
   replaced it with existential J and `_adjJ : J ⊣ zlWeilPull D l hl Ω j`.
   The image-filtration clause now applies to J. Removed the public import
   `Sheaf.Paper.ExtensionByZeroPunctual`, replacing it with the actual definition
   owner's `Sheaf.Paper.WeilIndSheafCategory`. No theorem node was added to
   `stmt_deps`; the accepted proof citation remains in the proof docstring only.
3. H9: removed all twelve private proof-dependency imports and the public
   `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` import. The retained imports
   provide the recorded statement interfaces and their types. No imports solely
   for the natural-language proof remain.

The sandbox node was compared with the current read-only base: before repair
only `lean` differed; the mathematical statement and accepted split were identical.
The repaired copy preserves the current base verbatim except for its updated Lean
record and the two explicitly authorized landed-owner additions to `stmt_deps`.
The delivery wrapper performs the authorized refresh and rebase; no direct git
command or edit of the shared repository was used. This is a content repair,
including the Lean signature and import list, not an unchanged re-push.

Second reading of the repair: the helper predicates are byte-identical. The
closed-image equality, actual unit HEq, surjective-unit IsIso, endpoint square,
assigned quotient weights and bound clauses are byte-identical. J has the same
source and target as the former open extension and is characterized by the
correct adjunction direction J ⊣ j*. Scheme hypotheses and universe binders are
unchanged. Rechecked length zero, repeated inclusions/zero quotients, arbitrary
weight lists, empty sources, and nonreduced ambient schemes: none is excluded.

Repair validation: scompile.py compiled the sandbox module in 14.4 s and the
literal library module in 8.2 s, without errors or warnings. The repaired record
has exactly two changed fields relative to the current base: `lean` and
`stmt_deps`. The signature record matches the source verbatim; all lines are at
most 100 characters; the sole theorem proof is `sorry`; no private imports or
use of `zlOpenWeilShriek` remain. The prescribed deliver2.py --no-push returned
`OK (dry run)` for ad3221284bb, passing server preflight and compilation.
