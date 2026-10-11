## Worker report

The module `Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated` states
`HomotopyCategory.quasiIso_saturated_triangulated`, with `sorry` as its only proof.
No definitions, new nodes, dependency replacements, or statement corrections are needed.
The conjunction packages results Mathlib provides separately, together with the explicit
MS5 and MS6 clauses. No existing declaration was found stating this whole conjunction.

Source checked: Stacks Lemma 05RT (https://stacks.math.columbia.edu/tag/05RT) and
Situation 05S8 (https://stacks.math.columbia.edu/tag/05S8). The local Stacks checkout is
absent on this machine, so these source pages were opened directly. Lemma 05RT identifies
the system associated with the acyclic triangulated subcategory as quasi-isomorphisms;
Situation 05S8 requires a saturated, triangulation-compatible system and an exact functor.
The final sentence of the node refers to its category/system hypotheses; the node also
provides the exact functor Qh, so no unspecified functor is introduced in Lean.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary abelian category A: `(A : Type u) [Category.{v} A] [Abelian A]`.
  Object and morphism universes are independent and explicitly declared.
- The chosen universe for D(A): `[HasDerivedCategory.{w} A]`, exactly the size convention
  in `def-weil-abstract-derived-category`'s recorded Mathlib match. This chooses a localization,
  rather than imposing a smallness or boundedness property: `HasDerivedCategory.standard A`
  always supplies the instance with w = max u v. The theorem works with any chosen universe w.
- K(A), the homotopy category of Z-indexed cochain complexes with its given triangulation:
  `HomotopyCategory A (ComplexShape.up ℤ)` (denoted K in this report). The canonical Mathlib instances provide
  precisely the triangulation recorded by `lem-pur-homotopy-category-triangulated`.
- S, represented quasi-isomorphisms: `quasiIso A (ComplexShape.up ℤ)` (denoted S in this report).
  `HomotopyCategory.quasiIso` requires every homology map to be an isomorphism;
  `HomotopyCategory.quotient_map_mem_quasiIso_iff` identifies it with represented
  quasi-isomorphisms of complexes. Every homotopy-category morphism has such a representative.
- MS1: both `S.HasLeftCalculusOfFractions` and `S.HasRightCalculusOfFractions` extend
  `S.IsMultiplicative`, whose fields are `id_mem` and `comp_mem`.
- MS2, first square: `HasLeftCalculusOfFractions.exists_leftFraction`, applied to the
  right fraction with denominator t and numerator g, gives s and f and `g ≫ s = t ≫ f`.
  Its auxiliary object is W. MS2, second square:
  `HasRightCalculusOfFractions.exists_rightFraction`, applied to the left fraction with
  numerator f and denominator s, gives t and g and `t ≫ f = g ≫ s`, with auxiliary object V.
- MS3, first cancellation: the `ext` field of the left calculus gives t with
  `f ≫ t = g ≫ t` from `s ≫ f = s ≫ g`. MS3, second cancellation: the `ext` field
  of the right calculus gives t with `t ≫ f = t ≫ g` from `f ≫ s = g ≫ s`.
  Thus the two class propositions express exactly MS1--MS3, without assuming a calculus
  as a hypothesis and without introducing a stronger fraction calculus.
- MS4: `S.IsCompatibleWithShift ℤ`. Its defining equality says membership is equivalent
  under every integer shift. This is equivalent to the node's forward closure for all n:
  the converse follows by shifting back by -n, since a multiplicative system respects
  isomorphisms and shift-by-n followed by shift-by-minus-n is naturally the identity.
- MS5: the universal quantifiers over `T T' : Triangle K` and their memberships in
  `distTriang K` supply exactly the two distinguished triangles. The maps s and s',
  their S-memberships, and `T.mor₁ ≫ s' = s ≫ T'.mor₁` supply the node's square.
  The existential s'' asserts its S-membership and both required equations:
  `T.mor₂ ≫ s'' = s' ≫ T'.mor₂` and
  `T.mor₃ ≫ s⟦(1 : ℤ)⟧' = s'' ≫ T'.mor₃`.
- MS6: for all W, X, Y, Z and f, g, h of exactly the indicated types,
  `S (f ≫ h) → S (g ≫ f) → S f`. Lean writes composition in diagrammatic order.
- Two-out-of-three: `S.HasTwoOutOfThreeProperty`, whose three inherited fields give
  composition closure and both cancellation implications.
- Closure under retracts: `S.IsStableUnderRetracts`; this is closure under retracts of
  arrows (`RetractArrow`), rather than retracts of only source or target objects.
- Cone criterion: for every distinguished triangle T,
  `S T.mor₁ ↔ subcategoryAcyclic A T.obj₃`. This covers any cone of any homotopy-category
  morphism; mapping-cone triangles are the defining distinguished triangles in K(A),
  and all distinguished cones of a fixed morphism are isomorphic. Acyclicity is invariant
  under isomorphism, so using any distinguished cone does not strengthen the assertion.
  `HomotopyCategory.mem_subcategoryAcyclic_iff` says explicitly that every homology object
  vanishes. No private predicate for a cone or for acyclicity is used.
- The specified Q:K(A)→D(A) is the localization:
  `(DerivedCategory.Qh (C := A)).IsLocalization S` asserts precisely this universal property.
  `Qh`, rather than the complexes functor `Q`, has the domain specified by this node.
- Exactness of Q: `(DerivedCategory.Qh (C := A)).IsTriangulated` means it carries every
  distinguished triangle to a distinguished triangle, with the canonical `Qh.CommShift ℤ`
  from Basic.lean. This is the node's exact functor of triangulated categories.
- The concluding Situation 05S8 assertion restates the already enumerated properties,
  and needs no extra predicate: K(A) is triangulated, S satisfies MS1--MS6, and Qh is exact.

Dependency declarations read and used (including their full signatures and surrounding docs):

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, a Mathlib leaf (no lean record needed).
- `def-weil-abstract-derived-category`: `DerivedCategory`, `DerivedCategory.Qh`,
  and `HasDerivedCategory`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  Its imports provide `HomotopyCategory.quasiIso` from `Mathlib.Algebra.Homology.Localization`
  and `HomotopyCategory.subcategoryAcyclic` from
  `Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated`, its distinguished
  triangles and triangle-morphism completion field, `CategoryTheory.IsTriangulated`,
  and `CategoryTheory.Functor.IsTriangulated`, from
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, and `.Functor`.
  All are imported through DerivedCategory.Basic.
- `lem-pur-homotopy-category-triangulated`: the anonymous `IsTriangulated` instance in
  `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated` at line 208, and the anonymous
  `Qh.IsTriangulated` instance in `Mathlib.Algebra.Homology.DerivedCategory.Basic` at line 173.
  The recorded match is a descriptive composite, and both actual declarations were read;
  their types and imports are usable without a dependency replacement.
- The two calculus classes and their LeftFraction/RightFraction fields are from
  `Mathlib.CategoryTheory.Localization.CalculusOfFractions`. Retract closure is from
  `Mathlib.CategoryTheory.MorphismProperty.Retract`. These are Mathlib notions, not copies.

Edge cases checked before writing: the zero category and zero complexes are allowed;
identities and zero maps that are quasi-isomorphisms are included; shifts include zero,
positive and negative integers; unbounded complexes are included (no boundedness binder);
cones are not chosen noncanonically in a new definition; arbitrary distinguished triangles
and arbitrary retract diagrams are quantified over; no enough-injectives, enough-projectives,
Grothendieck, field, ring, or smallness assumption is imposed. All universes and variables
are explicitly bound, with no auto-implicit parameter. No statement dispute was found.

Searches (2026-10-11):

- `msearch.py ... leanfinder "Quasi-isomorphisms in the homotopy category form a saturated
  multiplicative system compatible with distinguished triangles and shifts"`: eight hits,
  including left/right calculus instances in DerivedCategory.Fractions, localization
  instances in DerivedCategory.Basic, and the cone criterion in HomotopyCategory.Acyclic;
  none states the entire conjunction.
- `msearch.py ... loogle "HomotopyCategory.quasiIso, MorphismProperty.HasLeftCalculusOfFractions"`:
  no hits; the server reports the second identifier unknown.
- `msearch.py ... leansearch "quasi-isomorphisms homotopy category saturated multiplicative
  system triangulated"`: service unavailable, Internal Server Error; no mathematical verdict
  inferred from that failure.
- `msearch.py ... grep "quasiIso|HasTwoOutOfThreeProperty|IsStableUnderRetracts"
  Algebra/Homology/HomotopyCategory`: 18 hits, including the cone criterion and shifts;
  no combined theorem.
- `rg` of quasiIso, saturation, compatibility, multiplicativity and retract closure in
  Mathlib's DerivedCategory, HomotopyCategory, Triangulated and CategoryTheory sources:
  the separate classes and results listed above, no combined statement.
- `rg` of quasiIso and saturation/triangulation patterns throughout
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf`: related derived
  constructions and K-flat results, no declaration stating this node.
- `grep -rn "lem-pur-quasi-isos-saturated-triangulated"` in the source project: no hits.
- `rg "quasiIso_saturated_triangulated"` in Mathlib, the source project, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no existing declaration with the proposed full name.

Validation: `scompile.py J1 lem-pur-quasi-isos-saturated-triangulated` on the module completed
with exit code 0, compiled in 1.3 seconds, with no warnings. The only proof is `by sorry`.

Preflight compatibility: the file spells out K and S in full rather than using let-bindings,
because the delivery signature reader interprets the first `:=` as the proof separator.
The K and S abbreviations in this report are purely expository.

## Second reading by J1

Independent second reader, 2026-10-11. I read the node, the complete delivered module,
all four statement-dependency nodes, and the Mathlib declarations realizing them.
I also read the raw Stacks `derived.tex` at `section-derived-categories`,
`lemma-acyclic`, `definition-localization`, and `situation-derived-functor`, fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex because the
local literature checkout is absent. The corresponding source pages are
https://stacks.math.columbia.edu/tag/05RT and https://stacks.math.columbia.edu/tag/05S8.
The section and lemma require an arbitrary abelian category, with no injectives,
projectives, boundedness, field, or geometric hypothesis. Situation 05S8 additionally
specifies an exact functor; here the node supplies Qh and concludes its exactness.
The final assertion concerns the category/system requirements, as the node's own last
proof step explicitly explains. It does not require an additional unspecified functor.

My checklist, transcribed from the node before matching the Lean, is as follows.
In this section K and S abbreviate the displayed homotopy category and quasiIso property
only in prose; the Lean spells them out.

1. Object A, an arbitrary abelian category: `(A : Type u) [Category.{v} A] [Abelian A]`.
   Pass. I checked `CategoryTheory.Abelian` at Abelian/Basic.lean:112: preadditivity,
   finite products, kernels, cokernels and normal monos/epis, giving the node's zero
   object and biproducts. Object and morphism sizes are separately polymorphic.
2. Object K(A), unbounded integer cochain complexes modulo homotopy, with its standard
   triangulation: `HomotopyCategory A (ComplexShape.up ℤ)` and its inferred instances.
   Pass. HomotopyCategory/Pretriangulated.lean:479 defines distinguished triangles as
   those isomorphic to `CochainComplex.mappingCone.triangleh`; its instance at 579 uses
   that exact class. HomotopyCategory/Triangulated.lean:208 provides the octahedral
   axiom. These are the actual declarations behind the dependency's descriptive match,
   and require no additional assumptions beyond those supplied by Abelian A.
3. Object S, homotopy-category maps represented by quasi-isomorphisms:
   `quasiIso A (ComplexShape.up ℤ)`. Pass. Localization.lean:104 defines it by invertible
   maps on every homology object. `quotient_map_mem_quasiIso_iff` identifies it with
   complex quasi-isomorphisms; the quotient's `map_surjective` gives representatives.
   Thus it uses the abstract-derived-category dependency's notion, not a private copy.
4. MS1, identities and composition: the inherited `IsMultiplicative` of each of
   `S.HasLeftCalculusOfFractions` and `S.HasRightCalculusOfFractions`. Pass: its parents
   are precisely ContainsIdentities and IsStableUnderComposition.
5. MS2, both Ore squares: the `exists_leftFraction` and `exists_rightFraction` fields.
   Pass. For the first, RightFraction has denominator t:X→Z and numerator g:X→Y;
   the resulting LeftFraction gives s:Y→W in S, f:Z→W and `g ≫ s = t ≫ f`.
   For the second, input LeftFraction has numerator f:Z→W and denominator s:Y→W;
   output RightFraction gives t:V→Z in S, g:V→Y and `t ≫ f = g ≫ s`.
   Auxiliary objects are existential, with no extra restriction on either square.
6. MS3, both cancellation directions: the two calculus classes' `ext` fields.
   Pass. The left field takes `s ≫ f = s ≫ g`, with s in S, and gives t in S
   with `f ≫ t = g ≫ t`; the right field takes `f ≫ s = g ≫ s` and gives
   `t ≫ f = t ≫ g`. These are exactly the node's two directions.
7. MS4, closure under every integer shift: `S.IsCompatibleWithShift ℤ`. Pass.
   Shift/Localization.lean:39 defines equality with the inverse image under each
   shift, equivalently membership iff shifted membership. This is equivalent here
   to forward closure for every integer: shift back by -n and use the shift
   isomorphisms and `respectsIso_quasiIso`. It does not add a stronger hypothesis.
8. MS5, completion between two distinguished triangles: the universal binders T,T',
   their two distTriang memberships, s,s', their two S-memberships, and the first
   square `T.mor₁ ≫ s' = s ≫ T'.mor₁`. The existential s'' has S-membership and
   both `T.mor₂ ≫ s'' = s' ≫ T'.mor₂` and
   `T.mor₃ ≫ s⟦(1 : ℤ)⟧' = s'' ≫ T'.mor₃`. Pass: all three squares have the
   correct orientation and all quantifiers have the required dependencies.
9. MS6, saturation implication: universal W,X,Y,Z and f:X→Y,g:W→X,h:Y→Z, followed
   by `S (f ≫ h) → S (g ≫ f) → S f`. Pass. Neither g nor h is assumed in S.
10. Two-out-of-three: `S.HasTwoOutOfThreeProperty`. Pass. Composition.lean:380
    inherits composition closure, HasOfPostcompProperty S S, and
    HasOfPrecompProperty S S, exactly the three implications.
11. Closure under retracts: `S.IsStableUnderRetracts`. Pass. Retract.lean:32 uses
    `RetractArrow f g` and S g to conclude S f, the full arrow-retract notion.
12. Cone criterion: for every T in distTriang K,
    `S T.mor₁ ↔ subcategoryAcyclic A T.obj₃`. Pass. Acyclic.lean:51 identifies this
    subcategory with vanishing of every integer homology object. A distinguished
    triangle supplies a cone of its first arrow; every arrow has such a triangle,
    and cones are isomorphic. Consequently this is exactly the node's mapping-cone
    criterion, independent of representative or choice, not a selected special cone.
13. Object D(A) and localization Q: `(DerivedCategory.Qh (C := A)).IsLocalization S`.
    Pass. I read DerivedCategory/Basic.lean:73–112 and 138–177: HasDerivedCategory
    chooses a localization in morphism universe w, DerivedCategory is that category,
    Qh has domain K(A), and Qh commutes with shifts. The binder
    `[HasDerivedCategory.{w} A]` implements the dependency's chosen size convention;
    `HasDerivedCategory.standard A` always gives w=max u v. It neither assumes
    small derived Hom sets in v nor excludes an arbitrary abelian category.
14. Exactness and the consequent Situation 05S8 requirements:
    `(DerivedCategory.Qh (C := A)).IsTriangulated`, with the canonical CommShift ℤ
    instance, and clauses 4–9 on the canonical triangulated K. Pass.
    Triangulated/Functor.lean:186 says every distinguished triangle is preserved;
    its Additive instance gives additivity. The actual Qh.IsTriangulated instance
    at Basic.lean:173 is the second declaration of the triangulation dependency.

The source numbers shift compatibility MS5 and triangle completion MS6, whereas the
node calls them MS4 and MS5 and calls the saturation implication MS6. I checked the
actual formulas, not their numbers: the mathematical conditions agree. There is no
statement correction and no need to alter the node for this labeling convention.

Edge cases: the zero abelian category and zero complexes are included. A genuinely
empty category is not abelian (no zero object), already excluded by the node itself.
The degree index is ℤ in the node, so it is not an arbitrary potentially empty index
set; all integer degrees and unbounded complexes are included. Shifts by zero and
negative integers are included. Empty schemes, n=0 coefficient conditions and
characteristic restrictions do not occur in this abstract categorical statement;
abelian categories of sheaves on the empty scheme and modules in every characteristic
are included. There are no field, Noetherian, finiteness or enough-injectives binders.
The universes w,v,u are explicitly declared and all local variables are bound.

Independent searches, using words beyond the first report's query (2026-10-11):

- LeanFinder via msearch: `Ore conditions quasiisomorphisms homotopy category cone zero
  retract localization exact functor`, eight hits. They include the individual
  calculus instances in DerivedCategory/Fractions, Qh and its localization instances,
  and Qh_inverts_quasiIso; none states the conjunction of this node.
- Loogle via msearch: `HomotopyCategory.quasiIso`, twelve hits, including the definition,
  multiplicativity, represented-map criterion, iso invariance, shift compatibility,
  and the acyclic-subcategory trW criterion. No full combined statement.
- LeanSearch via msearch: `quasi-isomorphisms closed under retracts and shifts and calculus
  of fractions`, unavailable with Internal Server Error; this is not a no-match verdict.
- Direct rg of Mathlib Localization/CalculusOfFractions, MorphismProperty, homological
  Localization, homotopy/derived category and triangulated sources for the classes,
  Ore/fraction conditions, acyclicity and retracts: the separate definitions and
  declarations checked above; no single declaration for the entire node.
- Direct rg of the source WeilConjectures and repository lean/Sheaf for quasi-isomorphisms,
  saturation, fraction calculi and two-out-of-three: derivability structures, related
  K-flat and derived constructions, and unrelated saturation results, not this statement.
  Searching the proposed name and saturation/triangulation combinations in those trees,
  Mathlib/Algebra/Homology and dag/lean_names_upstream.json found no existing full theorem.

H12/H13: there are no new nodes or dependency modules in this delivery. Each dependency
already has usable Mathlib declarations with the exact notions above, so no private
replacement or missing-definition repair is needed. H5/H6/H8/H9: the module has no new
definition and one theorem with only `by sorry`; the source/blueprint docstrings and
seven-step proof outline follow all seven node proof steps, including the long-exact
cohomology ladder and five lemma for MS5. Imports supply declarations used in the type;
namespace and explicit universes are correct; maximum line length is 98.

Mismatches found: none. Changes: appended this independent review only; kept the Lean,
node statement, dependencies and recorded signature unchanged. I compared the signature
from `theorem` up to `:=` with lean.statement byte-for-byte: equal.
Validation: independent scompile.py run completed with exit code 0 in 1.4 seconds,
without errors or warnings. The required delivery dry run is recorded below after it runs.
The required `deliver2.py J1 lem-pur-quasi-isos-saturated-triangulated --no-push`
printed OK: the delivery passes the preflight and compiles.

## Reviewer fix (R-qst0940, 2026-10-11)

The MS4 clause `IsCompatibleWithShift ℤ` and the spelled-out MS5 triangle-completion clause
are replaced by the single Mathlib class `(quasiIso A (ComplexShape.up ℤ)).IsCompatibleWithTriangulation`
(Mathlib.CategoryTheory.Localization.Triangulated, now imported explicitly). That class extends
`IsCompatibleWithShift ℤ` and its one field `compatible_with_triangulation` is literally the former
MS5 clause, so the content is unchanged; downstream nodes get it in Mathlib's phrasing. The docstring
sentence on MS4/MS5 is adjusted accordingly. Recompiled clean. `existing` stays false: Mathlib
has MS1--MS5, the cone criterion (`quasiIso_eq_trW_subcategoryAcyclic`), `Qh.IsLocalization` and
`Qh.IsTriangulated`, but no saturation (MS6), two-out-of-three or retract-closure statement for
`HomotopyCategory.quasiIso`, nor the conjunction.
