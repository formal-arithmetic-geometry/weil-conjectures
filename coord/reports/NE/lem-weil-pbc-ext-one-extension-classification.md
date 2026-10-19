## Worker report

The module `Sheaf.CategoryTheory.ExtOneExtensionClassification` states
`CategoryTheory.ext_one_extension_classification`, with the whole proof `sorry`.
The node statement is unchanged. No new definitions, nodes, or dependency modules are needed.

Hypothesis and clause correspondence:

- The abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`.
  Its chosen derived category is `[HasDerivedCategory.{t} C]`.
  `[HasExt.{w} C]` chooses a small model of its Ext groups, exactly as the recorded
  def-pc-ext interface requires. This imposes no enough-injectives or enough-projectives
  assumption: `HasExt.standard` exists, and the derived Hom comparison is
  `Abelian.Ext.homAddEquiv`.
- The fixed endpoints are `(P Q : C)`. A sequence is a middle object `B`, maps
  `a : P ⟶ B`, `b : B ⟶ Q`, the complex equation `z : a ≫ b = 0`, and
  `h : (ShortComplex.mk a b z).ShortExact`. The last predicate says exactness at B,
  monicity of a and epicity of b, hence exactness of the sequence with zero endpoints.
- The connecting class is the existing `h.extClass : Abelian.Ext Q P 1`.
  `ShortComplex.ShortExact.extClass_hom` identifies its derived Hom image with
  `h.singleδ`, the canonical boundary of the single-complex triangle.
- The first conjunct quantifies over every `ξ : Abelian.Ext Q P 1` and supplies a
  short exact sequence with `h.extClass = ξ`: surjectivity onto all degree-one classes.
- The second conjunct compares arbitrary two sequences with those same P and Q.
  Its equivalence `h.extClass = h'.extClass ↔ ∃ e : B ≅ B',
  a ≫ e.hom = a' ∧ e.hom ≫ b' = b` states both well-definedness on isomorphism
  classes and injectivity there. The two equations are exactly h composed with u
  equals u', and v' composed with h equals v. Endpoint automorphisms are not allowed.
  Surjectivity and this equivalence together express precisely the stated bijection
  on classes, without introducing a quotient or an arbitrary chosen bijection.
- The last conjunct universally quantifies over another abelian category D with its
  own independent object, morphism, derived-category and Ext universes. The additive
  exact functor is `F : C ⥤ D` with `[F.Additive] [PreservesFiniteLimits F]
  `[PreservesFiniteColimits F]`. For additive functors between abelian categories these
  are precisely exactness. `h.map_of_exact F` is the short exact image sequence, and
  `h.extClass.mapExactFunctor F = (h.map_of_exact F).extClass` is the required equation.
  The source of `Abelian.Ext.mapExactFunctor_hom` was read: it gives the termwise
  derived functor with the source single-object inverse comparison, shift comparison
  (inside ShiftedHom.map), and target single-object comparison. Thus the equation
  uses D(F), not an unrelated map on extension classes.

Dependency declarations read and used:

- def-sp-abelian: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic.
- def-weil-abstract-derived-category: `HasDerivedCategory`, `DerivedCategory` and
  `DerivedCategory.Q`, Mathlib.Algebra.Homology.DerivedCategory.Basic.
- def-pc-ext: `CategoryTheory.Abelian.Ext`, `Abelian.Ext.homAddEquiv`,
  Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic.
- def-weil-pbc-exact-sequence: `CategoryTheory.ShortComplex.ShortExact`,
  Mathlib.Algebra.Homology.ShortComplex.ShortExact, through its recorded module
  Mathlib.Algebra.Homology.ExactSequence (public import).
- The canonical class and image are Mathlib's `ShortExact.extClass`,
  `ShortExact.extClass_hom`, `ShortExact.map_of_exact`, and `Ext.mapExactFunctor`;
  their declaration sources and docstrings were read in ExtClass.lean and Map.lean.

Proof-dependency modules are imported non-publicly: TStructure (standard heart and
concentration), FullyFaithful (single functor), ShortExact (complex SES triangle),
and WeilConjectures.DeligneLaumon.Reduction.FormalSteps (the recorded heart lemma).
The triangulated-category and triangle-isomorphism APIs are already imported through
these modules. Ext.Map is public because the final clause uses its map; it also
contains the recorded exact-functor triangle comparison. No proof-import cycle arises.

Node fault noticed: the existing proof dependency lem-weil-heart-short-exact-triangles
records `AlgebraicGeometry.WeilSheaf.exact_map_higherLowerShriek` in FormalSteps, whose
signature is a specialized cohomology exactness theorem, not the generic standard-heart
criterion used in this node's proof plan. This is not a statement dependency and does
not prevent stating this item. Its recorded module is retained as required; the generic
heart proof interface must be repaired before stage 3 follows that step. No dependency
record was changed, and no substitute notion was introduced.

Edge cases checked: P or Q zero, and both zero, are included without exclusions;
the zero Ext class has split representatives, and equality allows different isomorphic
middle objects. Proof witnesses for the zero composite and short exactness are propositions,
so the classification does not distinguish them. Arbitrary (possibly large) abelian
categories and independent universes for D remain permitted. There are no assumptions
of enough injectives, enough projectives, nonzero objects, or finite generation.

Searches performed before drafting:

- msearch.py leanfinder: "Degree one Ext classes classify short exact sequences up to
  endpoint identity isomorphism": 8 hits, including ShortExact.extClass,
  ShortExact.extClass_hom, Ext.ext_iff and exact-sequence lemmas; none states classification.
- msearch.py loogle: `"extClass"`: 10 hits, including extClass_naturality and
  mapExactFunctor_extClass; the latter covers only the final clause, not the full item.
- msearch.py grep: `extClass|extension.*[Bb]iject` in Algebra/Homology/DerivedCategory:
  18 hits in ExtClass, Map, exact-sequence and enough-injectives/projectives modules;
  none provides the endpoint-fixed classification.
- msearch.py leansearch: "Short exact sequences with fixed endpoints classified by
  Ext one": unavailable (Internal Server Error).
- rg `extClass|extension.*[Bb]iject` over the source project's WeilConjectures and
  the group's lean/Sheaf: naturality, cohomology and special module statements,
  no general classification. rg for the item id and proposed declaration name over
  those trees and dag/lean_names_upstream.json: no matches.

Source checked directly in literature/stacks-project/derived.tex, labels
lemma-yoneda-extension and lemma-ext-1 (Tags 06XU and 06XV). These assert representation
of every degree-one class and equivalence exactly for equal classes. The degree-one
endpoint-fixed equivalence is rendered by the middle-object isomorphism explicitly.
The exact-functor clause was checked against Mathlib Ext.Map's full signatures.

Validation: scompile.py compiled the delivered module cleanly on the server in 1.8 s,
with nice 19, two threads, and the default 60-second per-file limit. No local Lean
compiler or library build was run. The final dry run is recorded below when completed.

Dry run: deliver2.py --no-push printed OK: compilation and preflight pass except
for the independent second-reading section, which the second reader must write.
Nothing was pushed.


## Second reading by NE

Independent second reader: opened the base node, sandbox node and module, and
Stacks derived.tex at definition-yoneda-extension, lemma-yoneda-extension (06XU)
and lemma-ext-1 (06XV), including the preceding discussion. The source assumes
only an abelian category; it explicitly does not require enough injectives or
projectives. In degree one a morphism of extensions with identity endpoints is
an isomorphism by the short five lemma, so its common-refinement equivalence is
exactly the endpoint-fixed isomorphism relation in this node. No statement
correction, new definition node, or dependency module is present or needed.

Object/hypothesis/conclusion checklist, with verdicts:

1. An arbitrary abelian category with a derived category: `{C : Type u}`,
   `[Category.{v} C]`, `[Abelian C]`, `[HasDerivedCategory.{t} C]`. Matches.
   Read the recorded dependency signatures in Abelian.Basic and
   DerivedCategory.Basic: the latter is localization of integer cochain complexes
   at quasi-isomorphisms. These are the dependency objects, not specializations.
2. Fixed endpoints P and Q: `(P Q : C)`, outside all three conjuncts. Matches.
3. The degree-one derived Ext group: `Abelian.Ext Q P 1`, with `[HasExt.{w} C]`.
   Read def-pc-ext and Ext.Basic: `Ext` is SmallShiftedHom and `homAddEquiv`
   identifies it with the derived Hom in the node. `HasExt.standard` exists
   at `max u v`; the size parameter does not require injectives/projectives
   or exclude any category with the node's chosen size convention. Matches.
4. An arbitrary short exact sequence with these endpoints: middle object B,
   `a : P ⟶ B`, `b : B ⟶ Q`, `z : a ≫ b = 0`, and
   `h : (ShortComplex.mk a b z).ShortExact`. Read the exact-sequence dependency
   and ShortComplex.ShortExact: its fields are Exact, Mono f and Epi g.
   This is exactly exactness of the displayed sequence with zero endpoints.
   No arbitrary complexes or extra hypotheses are substituted. Matches.
5. The assigned class is the connecting arrow, not an arbitrary bijection:
   `h.extClass`. Read its construction in Ext.ExtClass, `extClass_hom`, and
   `singleδ`/`singleTriangle` in DerivedCategory.SingleTriangle. It is the
   canonical short-exact-triangle boundary under `homAddEquiv`. Matches.
6. Every class has a representative: first conjunct `∀ ξ, ∃ B a b z h,
   h.extClass = ξ`. No chosen B is fixed before ξ. Matches surjectivity.
7. Equal classes precisely for isomorphic sequences: second conjunct quantifies
   over both arbitrary sequences and says `h.extClass = h'.extClass ↔ ∃ e : B ≅ B',
   a ≫ e.hom = a' ∧ e.hom ≫ b' = b`. These are exactly the node's two squares
   with identity endpoint maps. Both directions are included, so the map descends
   to isomorphism classes and is injective there. With clause 6 this is exactly
   the claimed bijection; no quotient representation needs a new definition.
8. Every exact additive functor to another abelian category with derived category:
   third conjunct quantifies over D and F, `[F.Additive]`,
   `[PreservesFiniteLimits F]`, `[PreservesFiniteColimits F]`. Read
   ShortComplex.ExactFunctor: `Functor.exact_tfae` equates the latter pair with
   preservation of short exact sequences for additive functors between abelian
   categories. Thus no stronger exactness condition has been introduced.
   D's universes u', v', t', w' are independent of C's. Matches.
9. Compatibility with D(F): `h.extClass.mapExactFunctor F =
   (h.map_of_exact F).extClass`. Read the definition of mapExactFunctor and
   mapExactFunctor_hom in Ext.Map. On derived Hom it first uses the inverse
   source single comparison, maps the shifted Hom (including shift comparison),
   then uses the shifted target single comparison. This is precisely termwise
   D(F), and `map_of_exact` is the image short exact sequence. Matches.

Edge cases: zero P, zero Q, both zero and the zero class are all included;
there is no Nonzero or Nontrivial binder. B may be any object. The witnesses z
and h are propositions and introduce no spurious distinction of extensions.
The category may be the zero category; an empty abelian category is already
excluded by the source's zero-object axiom, not by a new restriction. There is
no index set, scheme, characteristic or variable degree in this statement;
it concerns degree one, not a family that should include n = 0. All eight
universe parameters and every binder are explicitly declared; no relation
between the source and destination category sizes is imposed.

Independent searches used different wording from the first reader:

- msearch.py leanfinder: "Every degree 1 derived Ext element is represented by a
  short exact sequence and equality means isomorphic extensions": eight hits,
  chiefly Ext.ext_iff/ext, ShortExact.extClass/extClass_hom and long exact
  sequence lemmas. Opened the actual sources: none states classification.
- msearch.py loogle: `ShortComplex.ShortExact, Abelian.Ext`: the service reported
  unknown identifier ShortComplex.ShortExact, so this query was inconclusive.
  LeanFinder supplies the working semantic search.
- rg in Mathlib's DerivedCategory/Ext and in both WeilConjectures and lean/Sheaf:
  `extension.{0,35}(classif|equiv|biject)|ext_one_extension_classification|extClass`.
  Mathlib has the canonical class, its naturality and mapExactFunctor_extClass,
  which proves only the final compatibility clause; no full classification.
  The source project's torsor uses are specialized to sheaves, and the project's
  ExtOneDirectSum module is about module Ext additivity, not this theorem.
  No declaration duplicates the whole statement. Existing notions are reused.

H5/H6/H8/H9: the module contains no new data definition, private copy, local
notation or local instance. Its only theorem has the whole proof `sorry`.
The module and theorem docstrings cite the source and blueprint id. The theorem
proof plan follows all five node steps: heart equivalence, SES boundary and
naturality, surjectivity by inverse rotation/heart closure, injectivity by TR3
and full faithfulness, then exact-functor compatibility. The first reader's
reported mismatch in the recorded generic-heart proof dependency is retained
as a stage-3 dependency warning; it is not a missing notion in this statement.
No statement mismatch was found; no Lean or node change was warranted.

Validation: checked the sandbox node's lean.statement equals verbatim the
module signature (from theorem through the type, before :=). scompile.py
independently compiled the only delivered module on the server in 1.9 seconds,
nice 19, two threads, 60-second per-file limit, with no diagnostics. The second
reading changes only this report, preserving the Worker report above.
