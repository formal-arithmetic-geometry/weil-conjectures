## Worker report

The delivery states `CategoryTheory.nonempty_yonedaDerivedExtComparison` in
`Sheaf.CategoryTheory.YonedaDerivedExtComparison`, with its sole theorem proof `sorry`. Mathlib's existing `ShortComplex.Splitting` is used for the split predicate.
The theorem asserts existence of the fully specified `YonedaDerivedExtComparison A`.
All helper definitions belong to the notions introduced in this very node: finite
extensions, their endpoint-fixed zigzags and quotient, splitting, splicing, the
geometric Baer sum, and the canonical comparison data. They are all recorded in
`lean.declarations`. No other DAG node is stated, and no statement, dependency,
proof, or source field of the item changes.

The source read was `literature/stacks-project/derived.tex`, the definition of a
Yoneda extension and the roof construction immediately before `lemma-yoneda-extension`,
the whole proof of that lemma (Tag 06XU), `lemma-ext-1` (Tag 06XV), and the following
composition discussion. For endpoint operations and Baer addition I also read
`literature/stacks-project/homology.tex`, Section 010I, the pullback and pushout
constructions and `lemma-baer-sum`. The declared proof docstring records all eleven
steps in the DAG proof, including the strictification of the refinement homotopy.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| An arbitrary abelian category A | `(A : Type u) [Category.{v} A] [Abelian A]`, using the recorded `CategoryTheory.Abelian` of `def-sp-abelian`. Object and morphism universes are independent. |
| Derived Ext groups as in `def-pc-ext` | `[HasExt.{w} A]` and the actual `CategoryTheory.Abelian.Ext U V (n + 1)`. `w` is independent of `u` and `v`. This is Mathlib's small model of the shifted morphisms, as recorded by that dependency; `HasExt.standard` supplies the unrestricted standard universe. No resolution or enough-injectives assumption is imposed. |
| Objects U,V and every positive degree i | `classGroup`, `comparison`, naturality, Baer addition, and vanishing quantify over all `V U : A` and `n : ℕ`, with degree `n + 1`. These are precisely all positive degrees. |
| Exact sequence `0 → V → E_(i-1) → … → E_0 → U → 0` | `YonedaExtension.sequence : ComposableArrows A (i + 1)`, `leftIso`, `rightIso`, `sequence.Exact`, `first_mono`, `last_epi`. There are `i` middle objects, with the leftmost one indexed by 1 and the rightmost by i. Monicity/epicity are exactness at the omitted zero endpoints. Endpoint isomorphisms only identify the named objects with the diagram endpoints. |
| Endpoint-fixed morphisms generate equivalence | `Related E F` is an actual natural transformation of sequences with `leftMap = 𝟙 V` and `rightMap = 𝟙 U`; `Equivalent` is `Relation.EqvGen Related`. `Classes` is the actual `Quot` of those sequences and `classOf` its quotient map. It is not a second copy or a definition in terms of derived Ext. |
| The canonical sequence-to-derived-class map | `shortExact_class` normalizes degree one by the actual Mathlib `ShortComplex.ShortExact.extClass`, transported through the endpoint isomorphisms. `splice_class` fixes every higher degree by composition of these connecting classes. `Splice` identifies the retained terms, the first injection, the composite at the cut, and the final augmentation. These equations characterize the roof map `Q(f_E) Q(s_E)⁻¹`: cut an arbitrary sequence at the image of its first differential, use the corresponding short exact sequence, and induct on its degree. They exclude an arbitrary additive bijection, including a change of sign or a constant map. |
| Isomorphism of abelian groups | `classGroup` is an `AddCommGroup` on that actual quotient, and `comparison` is an `AddEquiv` from it to the recorded derived `Ext`. Thus equality is exactly equality of extension classes and every Ext element is attained. |
| Natural in both variables | `naturality` quantifies over every map of extension sequences, with arbitrary endpoint maps, and equates derived postcomposition by the induced V-map with precomposition by the induced U-map. In particular a pushout arrow gives covariance in V; a pullback arrow gives contravariance in U. These arrows are the usual endpoint operations of the source, rather than arbitrary proposed group actions. |
| Baer sum = direct sum, diagonal pullback, addition pushout | `BaerSum E F G` specifies a termwise binary product T with the two projections, a last-arrow pullback P along `Limits.prod.lift (𝟙 U) (𝟙 U)`, and a first-arrow pushout into G along `Limits.prod.fst + Limits.prod.snd`. Earlier, respectively later, terms are unchanged up to isomorphism. Binary products are binary direct sums in this abelian category. `baer_exists` asserts existence for every E,F, and `baer_sum` identifies every such G with addition for `classGroup`. This makes the group operation exactly the specified Baer construction. |
| In degree one zero iff split | `split_iff` says `comparison V U 0 E.classOf = 0 ↔ E.IsSplit`. `IsSplit` is `Nonempty` of Mathlib's `ShortComplex.Splitting` for this exact short complex. This includes a compatible retraction of its first arrow and section of its last arrow; it is the existing splitting notion, not a private copy. The additive bijection also identifies this condition with the zero of the Yoneda group. |
| If V is injective, the groups vanish in every positive degree | `injective_vanishing (V U : A) [Injective V] (n : ℕ) : Subsingleton (Ext U V (n + 1))`. Through `comparison` the same holds for the Yoneda group. This uses the recorded `CategoryTheory.Injective`, with no sufficient supply of injectives assumed. |

The `Nonempty` conclusion is existence of these canonically characterized data,
not existence of an unspecified natural isomorphism. In particular the short-exact
and splice equations specify the value on every representative. No object is
defined by choosing arbitrary data from an unproved existence statement. Every
definition has actual data; the one mathematical theorem remains unproved for
stage 3.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic` (its `mathlib_match`, since the node is a
  Mathlib leaf). Its finite-product, kernel/cokernel, normal mono/epi formulation
  is the recorded definition, and it supplies the binary products used here.
- `def-pc-ext`: `CategoryTheory.Abelian.Ext`, `HasExt`, `Ext.mk₀`, `Ext.comp`, and
  `Ext.homAddEquiv` in `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`.
  `Ext` is the small localized shifted-Hom carrier; the recorded old
  `ProjectiveResolution.isoExt` declaration is not used to restrict this theorem
  to categories with enough projectives. `ShortComplex.ShortExact.extClass` and
  its docstring were read in `Ext.ExtClass`; that actual canonical class is used
  in `shortExact_class`.
- `def-sp-injective-resolutions`: the injective-object clause uses
  `CategoryTheory.Injective` in `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
  I read `InjectiveResolution` in its separate Resolution module too; the node
  at hand only needs injectivity, so does not assume a resolution.
- The already stated proof prerequisites are imported with non-public imports:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `Mathlib.Algebra.Homology.DerivedCategory.Fractions`,
  `Mathlib.CategoryTheory.Localization.CalculusOfFractions`, and
  `Sheaf.CategoryTheory.PushoutShortExactSequence`. The derived-category definition
  and Ext prerequisite are available through its direct non-public Basic import; the statement modules Abelian.Basic and Ext.Basic also have direct public imports. Their
  source signatures match the recorded proof-dependency interfaces.

Edge cases checked before and after elaboration:

- For i=1, the sequence has precisely `V → E₀ → U`, and exactness and mono/epi
  give a short exact sequence. In the Baer construction its unique middle term
  is the pullback and then the pushout; the ranges of unaffected middle terms
  are empty. `split_iff` tests Mathlib's splitting of this very short complex.
- For i=2, the splice with a short extension omits the intermediate kernel
  object and composes its adjacent arrows. `tailIso` identifies precisely the
  second middle term and U; it does not retain an extra copy of the kernel.
- Degree zero is outside the theorem's family. No arbitrary fixed i, n=0
  exception, boundedness restriction, or enough-injectives assumption is hidden.
- Zero endpoints and the zero abelian category are allowed. The quotient and all
  endpoint operations remain defined; injective vanishing uses `Subsingleton`
  for an underlying group type, not `IsZero` on a bare type.
- The group carrier has universe `max u v`, while Ext may have any supplied
  universe w. The comparison permits these different universes. No equality of
  universes is imposed to use a specialized API.
- Replacing endpoint equalities by named isomorphisms does not alter the classes:
  the induced endpoint maps are conjugated by exactly those isomorphisms, and
  the generating relation fixes the actual named V,U. All representatives with
  literal endpoints embed by identity isomorphisms.

Searches actually run (the structured results are retained in `searches.jsonl`):

- `msearch.py leanfinder`, query `Yoneda extensions of all positive lengths
  classified by derived Ext with Baer sum`: 8 hits, including `Abelian.Ext`,
  `HasExt.standard`, and `ShortComplex.ShortExact.extClass`. No higher Yoneda
  quotient or comparison.
- `msearch.py loogle`, query `CategoryTheory.ShortComplex.ShortExact.extClass`:
  12 hits for degree-one classes, their naturality, and exact Ext sequences.
  The degree-one construction is reused, not redefined.
- `msearch.py grep`, query `YonedaExtension|yonedaExtension|extClass` in
  `Algebra/Homology`: 18 hits for derived Ext and the degree-one class.
- `msearch.py leansearch`, query `Yoneda higher extension classes are naturally
  isomorphic to derived Ext and preserve Baer sum`: 8 hits for the Yoneda lemma,
  derived Ext, its small model and `homAddEquiv`; none for this statement.
- Direct `rg` of Mathlib, upstream `WeilConjectures/`, this project's `lean/Sheaf/`,
  and `dag/lean_names_upstream.json` for `YonedaExtension`,
  `yonedaExtension`, `YonedaDerivedExtComparison`, and the main theorem name found
  no duplicate. Upstream grep for this node id also found none. The unrelated
  `freeYonedaExtensionIso` concerns the free presheaf, and
  `FlatCotorsionFoundation` uses only derived Ext.
- `tools/lean_names_upstream.py show` consulted the upstream declaration lists.
  `tools/blueprint_refs.py search Yoneda extension` returned only an unrelated
  exceptional-inverse-image blueprint statement, not a node carrying the finite
  Yoneda quotient. The present item's statement introduces these notions, so its
  helper declarations stay in this owning module under the authorized helper rule.

No disputed statement or source-based statement correction was needed. There are
no additional node files and no dependency repairs. The compile wrapper reports
both the sandbox elaboration and the module elaboration clean, with no warnings,
within the prescribed 60-second per-file limit. The required delivery dry run is
performed after this report and the exact Lean record have been synchronized.


## Second reading by Q24

I read the node's complete statement and eleven-step proof, the delivered module,
all three statement-dependency records, and the declarations named below. I read
Stacks `derived.tex`, definition-yoneda-extension, the roof construction, all of
lemma-yoneda-extension (06XU), lemma-ext-1 (06XV), and the subsequent composition
paragraph; and `homology.tex`, section-extensions (010I), including both endpoint
operations and lemma-baer-sum. The source works in an arbitrary abelian category;
it assumes neither enough injectives nor enough projectives. There is no repair
note for this item, no statement_change, no new node, and no dependency module.
The following is my independent object/hypothesis/conclusion checklist.

| Node item | Lean rendering and second-reader verdict |
| --- | --- |
| Arbitrary abelian category A | `A : Type u`, `Category.{v} A`, `Abelian A`. Read `Abelian.Basic`: preadditivity, finite products, kernels/cokernels and normal monos/epis give exactly def-sp-abelian. PASS; no ring, field, finiteness or resolution assumption. |
| Derived Ext groups of def-pc-ext | `HasExt.{w} A`, `Abelian.Ext U V (n + 1)`. Read Ext.Basic: `SmallShiftedHom` of the quasi-isomorphism localization, `homAddEquiv`, `mk₀` and `comp`; these are the recorded derived-Hom notion and its endpoint maps. `HasExt.standard` gives the general universe case. PASS. The older projective-resolution declarations also listed in the dependency are not used. |
| Every pair U,V and every i >= 1 | The fields of `YonedaDerivedExtComparison A` quantify over `V U : A`, `n : ℕ`, degree `n + 1`; the theorem supplies all fields simultaneously. PASS; every positive degree and every pair is included. |
| Actual exact sequence with i middle objects | `YonedaExtension.sequence : ComposableArrows A (i + 1)` has vertices 0 through i+1. `leftIso` and `rightIso` name vertices 0 and i+1 as V and U; `exact` is exactness at vertices 1 through i, and `first_mono`/`last_epi` supply exactness at the zero endpoints. Read ExactSequence and ComposableArrows.Basic. PASS; endpoint isomorphisms merely transport names. |
| Equivalence generated by endpoint-fixed sequence maps | `Related` requires a natural transformation with `leftMap = 𝟙 V` and `rightMap = 𝟙 U`; `Equivalent` is its `Relation.EqvGen`, and `Classes` is its actual `Quot`. PASS. Although Stacks defines a common refinement, 06XU identifies it with equality of roofs, hence with precisely these generated zigzags. |
| Canonical sequence-to-roof class | `shortExact_class` and `splice_class` characterize the positive-projection roof on every representative by induction after cutting at the image of its first differential. I found and repaired a SIGN mismatch here; detailed calculation below. PASS after repair. These fields exclude an arbitrary additive bijection. |
| Abelian group with geometric Baer addition | `classGroup` is on the actual sequence quotient; `BaerSum` requires termwise products with their two limit projections, the last-arrow pullback along the diagonal, and the first-arrow pushout along addition. Its natural transformations preserve all other terms up to isomorphism. Products are direct sums in this preadditive abelian category. `baer_exists` and `baer_sum` specify existence and the quotient addition. PASS. |
| Natural isomorphism of groups | `comparison` is an `AddEquiv` from that quotient group to Ext. `naturality` is the usual equality after postcomposition in V and precomposition in U for every map of sequences with arbitrary induced endpoint maps. Applying it to the canonical pullback/pushout arrows gives both source functorialities; bijectivity makes the induced class actions unambiguous. PASS. |
| Degree-one zero exactly split | `split_iff` relates the comparison's zero to `E.IsSplit`, which uses the existing `ShortComplex.Splitting` of this very sequence. Read ShortComplex.Exact: compatible retraction and section. PASS; no duplicate splitting notion. |
| Injective V implies vanishing in every positive degree | `injective_vanishing (V U) [Injective V] (n : ℕ) : Subsingleton (Ext U V (n + 1))`. Read Injective.Basic.factors and the dependency's separate InjectiveResolution declaration. Only injectivity is needed here; no enough-injectives assumption. The additive equivalence gives the identical vanishing on the Yoneda quotient. PASS. |

Mismatch and repair (H3/H8): the original worker report asserted that Mathlib's
`extClass` was the source's positive-projection roof and that unsigned splice
composition characterized that roof. This is incorrect with the actual library
conventions. In `HomotopyCategory/MappingCone.lean`, `inl_v_d` gives the positive
original arrow as the differential in the two-term cone. In
`HomotopyCategory/Pretriangulated.lean:54`, `mappingCone.triangle` uses
`-mappingCone.fst`; `inl_v_triangle_mor₃_f` explicitly computes its negative
projection. Ext.ExtClass defines `extClass` by inverting the augmentation and
composing this very third map. Consequently the degree-one roof using the
positive projection is **minus** `extClass`, also after endpoint transport. I
changed `shortExact_class` to that negative transported class.

For completeness I checked the higher-degree sign rather than merely changing
the first field. Write r = n+1 for the degree of the tail F, and cut a degree
r+1 extension E into the short sequence S and F. There is a quasi-isomorphism
C_E -> C_F given by S.g on its first middle term, the identity on later terms,
and zero on its extra left term. It represents the denominator for delta(F).
The comparison C_E -> C_S[r] is the identity on the first middle term and
(-1)^r on V, since the differential of C_S[r] is (-1)^r S.f. Thus
`delta(F).comp delta(S) = (-1)^r • delta(E)`. Substituting
`delta(S) = -extClass(S)` gives
`delta(E) = (-1)^n • (delta(F).comp extClass(S))`.
I changed `splice_class` to this exact formula. I read the actual shift
implementation (`HomotopyCategory/Shift.lean:46,102,139,144`) and ShiftedHom.comp:
shifts multiply differentials by (-1)^r, shifted maps are their original
components, and the shift-add isomorphism contributes no scalar. Ext.comp_hom
transfers precisely that composition. In degree two the new formula has no
additional scalar in front of delta(F).comp extClass(S); in degree three it
has a minus. Together with degree-one normalization, induction now specifies
exactly the node's positive-projection roof, not the old differently signed
bijection. The node's statement and proof remain unchanged: they already name
that roof. No source-based statement correction or citer audit is required.

I updated the module overview, both field comments, the theorem's proof step 8,
and the node's lean.note to explain these signs. The existing Worker report is
preserved above; its claims of unsigned normalization are superseded by this
second reading. All other definitions and clauses were correct and retained.

Edge cases independently checked:

- Degree one: exactly V -> E₀ -> U, with both endpoints exact. In BaerSum only
  the left endpoint of the pullback arrow and the right endpoint of the pushout
  arrow must be unchanged; the unaffected-middle-term ranges are empty.
- Degree two: `Splice.tailIso` identifies F with its left endpoint removed with
  E with its first two vertices removed. The intervening kernel object is
  omitted, and `splice_comm` composes the two arrows through it. This supplies
  all degree-two sequences by cutting at their image, with the sign above.
- Degree zero is outside the node: n=0 represents i=1, rather than losing that
  case. Definitions accepting i=0 do not add a degree-zero theorem obligation.
- Zero endpoints and the zero abelian category are included. An empty category
  cannot satisfy Abelian (it needs a zero object). There is no independent
  index set, scheme, or characteristic restriction; integer signs also cover
  groups of exponent two without a special hypothesis.
- Universes u (objects), v (morphisms), w (Ext carrier) remain independent.
  `Classes : Type (max u v)` is the actual quotient; AddEquiv permits its carrier
  and Ext's carrier to have different universes. HasExt.standard provides the
  unrestricted standard case, including large categories in a higher universe.
  No equality of site object/morphism universes is imposed.
- Isomorphic named endpoints cause no extra equivalence classes: identity-on-V/U
  means identity after exactly the endpoint conjugations in leftMap/rightMap.
  Literal endpoints are recovered using identity isomorphisms.

Independent searches (different queries from the first reader; wrapper results
are appended to searches.jsonl):

- LeanFinder: `finite exact sequence extensions modulo endpoint fixed chain maps
  classify all higher Ext` returned eight hits, namely existing derived-Ext
  exactness statements and `ShortExact.extClass`, not a higher-sequence quotient.
- Loogle: `CategoryTheory.ShortComplex.Splitting` returned twelve hits; I opened
  its definition and reused the existing notion already used by IsSplit.
- LeanSearch: `Equivalence classes of exact sequences of arbitrary positive
  length give Yoneda Ext with Baer addition` returned eight hits for derived
  Ext, mk₀, addEquiv₀, extClass and resolution facts. None states this comparison.
- Wrapper grep: `BaerSum|YonedaExtension|ShortComplex.Splitting` returned twelve
  uses of existing Splitting and no competing higher Yoneda construction.
- Direct rg with `yoneda.?extension|extension.?class|baer.?sum` over Mathlib's
  homology/category-theory trees, upstream WeilConjectures and project lean/Sheaf
  found the existing ExtOneExtensionClassification. I opened that entire
  declaration: it states only degree-one representative existence, middle-term
  isomorphism, and exact-functor compatibility, with no higher-degree quotient,
  Baer group law or injective vanishing. It does not replace this node. Existing
  freeYonedaExtensionIso is about presheaves, and FlatCotorsionFoundation uses
  derived Ext only. There is no duplicate for this node or any newly defined
  higher-sequence notion. All helpers belong to the notions explicitly
  introduced by this node, so no additional definition node is needed.

I also opened the proof-dependency interfaces: DerivedCategory.Basic/Fractions,
Localization.exists_rightFraction, RightFractionRel and RightFraction.map_eq_iff,
and the project PushoutShortExactSequence module. They have the advertised
arbitrary-category/abelian-category hypotheses and are imported. No dependency
repair is needed. All definitions and structures have real data. The sole
postponed theorem is named, has the node's complete eleven-step proof docstring,
and has proof `sorry`; nothing mathematical was proved in this stage.

Validation: the repaired module compiled cleanly through scompile.py in both
sandbox and library elaboration (2.4 and 3.3 seconds), with no errors or warnings.
Every variable and universe is explicitly bound, no line exceeds 100 columns,
and lean.statement is verbatim the unchanged theorem signature. Delivery dry run
and final delivery follow this second reading.
