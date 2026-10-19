## Worker report

The delivery states `CategoryTheory.isZero_rightDerived_evaluation_pullback_injective`
in `Sheaf.CategoryTheory.Sites.PullbackInjectiveEvaluationAcyclic`. Its only proof is
`sorry`. No definition, helper theorem, new node, dependency repair or statement
correction is needed. The original node's statement, dependencies and proof remain
unchanged. No repair note exists for this item in `coord/repair-notes/`.

Source read: `literature/stacks-project/sites-cohomology.tex`, lines 9277–9306,
Tag 0D6X, `lemma-pullback-injective-pre-limp`. The source allows a ring sheaf and
an injective module; the node is exactly its abelian-sheaf (integer-ring)
specialization. Also read `sites.tex`, lines 4577–4608, Tag 00XR,
`lemma-when-shriek`: the inverse image associated with the cocontinuous functor
is `(u^p -)^#`, and continuity makes sheafification redundant. Consequently the
explicit expression used here is the canonical inverse image on abelian sheaves,
not an arbitrary functor that is assumed to satisfy a comparison property.

Every hypothesis and clause has the following rendering:

| Node text | Lean rendering |
| --- | --- |
| Two small sites in a common universe | `{C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]`, precoverages `J`, `K`, and `_hJ : J.IsSiteForCoverings`, `_hK : K.IsSiteForCoverings` |
| A functor u from C to D | `(f : C ⥤ D)` |
| Continuous, clause (a), sends covering families to coverings | `_hcover`, mapping each covering presieve `S` to `S.map f` |
| Continuous, clause (b), preserves pullbacks of covering arrows | `_hpullback`, the `PreservesLimit (cospan a b) f` assertion whenever the covering contains `a` |
| Cocontinuous, part (1), with no special-cocontinuity conditions | `[f.IsCocontinuous J.toGrothendieck K.toGrothendieck]` |
| Associated geometric morphism and its inverse image g^-1 I | `((presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}).obj (f.op ⋙ I.obj))`, the canonical sheafification-of-restriction construction in Sites 00XO/00XR |
| I an injective abelian sheaf on D | `(I : Sheaf K.toGrothendieck AddCommGrpCat.{u}) [Injective I]` |
| Every object U of C | `(U : C)`, with no terminal-object assumption |
| Every positive integer p | `(p : ℕ) (_hp : 0 < p)`; every positive integer is a unique positive natural degree, and rightDerived is naturally indexed by ℕ |
| Ordinary R^p Gamma(U,-), with Gamma the evaluation functor | `((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj` |
| Vanishing, H^p = 0 | `IsZero` of this abelian group object |

The associated morphism `g` is determined by `f`; it is expanded to its canonical
inverse-image construction rather than introduced as independent geometric-morphism
data with an unspecified association. Both sites and all group values are in the
common universe `u`. Small sites in that bound have objects and homs of that size.
There is no assumption of nonemptiness, all pullbacks, finite limits, terminal
objects, local fullness/faithfulness, density, or injectivity after inverse image.
The Grothendieck abelian and enough-injectives instances are inferred from Mathlib,
not extra mathematical hypotheses.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, the recorded site predicate.
  The cohomology portion of its node is rendered directly using Mathlib's
  ordinary `CategoryTheory.Functor.rightDerived`, as the item's statement requires.
- `def-weil-size-convention` is recorded as a metatheoretic convention with no
  declaration; the explicit common universe `u` renders it here.
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`:
  `CategoryTheory.Functor.IsSpecialCocontinuousForCoverings` was read in full.
  Its docstring identifies clause (1) as Mathlib `Functor.IsCocontinuous` for the
  generated topologies. Only that clause is assumed; its continuity conjuncts
  are reproduced as the node's separately required continuity hypotheses, without
  the additional local equality/lifting and density conjuncts.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism` and its `inverse`, `direct`, `adj`,
  `leftExact` fields were read. The associated inverse image is expanded to its
  canonical presheaf/sheafification construction as above; this dependency's
  module is publicly imported, with no second geometric-morphism definition.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.Injective`, read at lines 28–34; `InjectiveResolution` was
  read in `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`, lines 37–55.
  `Injective I` is exactly the injectivity hypothesis.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `sheafificationAdjunction`, read at lines 72–81. These give genuine canonical
  data with no use of a sorried existence choice.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived`,
  the ordinary injective-resolution-derived functor, and the standard evaluation
  and sheaf-forgetful functors. `Mathlib.Algebra.Category.Grp.AB`,
  `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`, and
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives` supply
  the inferred existence of injective resolutions.

All recorded proof-dependency modules are imported, without public visibility:
`Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings`,
`WeilConjectures.CategoryTheory.SiteCechComplex`,
`WeilConjectures.CategoryTheory.SiteInjectiveCechAcyclic`, and
`WeilConjectures.CategoryTheory.SiteCechVanishingCriterion` (the site-definition
module is already publicly imported). Read the two latter current upstream
sources through `scompile.py --source`; their declarations are respectively
`CategoryTheory.site_injective_cech_acyclic` and
`CategoryTheory.Sheaf.isZero_H'_of_siteCech_vanishing`. The proof docstring
retains all four steps from this item's node, including nerve-projection
compatibility and the all-coverings specialization of the vanishing criterion.
The current proof-only criterion uses Ext-valued `H'` and older precoverage
instances; stage 3 must bridge it to ordinary evaluation-derived cohomology and
the weaker recorded site interface. This delivery does not impose those stronger
proof-interface hypotheses on the item's statement.

Edge cases checked against the source: an empty source category makes the
universal object assertion vacuous, without excluding the site; an empty cover
is allowed by the presieve site predicate and by the continuity hypothesis;
a zero injective sheaf has the asserted vanishing; `p = 0` is deliberately
excluded (its sections need not vanish), while `p = 1` is included; `U` need
not be terminal; finite-cover sites are allowed because no strict indexed
`IsStableUnderComposition` is assumed. No disputed statement was found.

Searches actually run for this item:

- `msearch.py ... leanfinder`:
  `Inverse image under a continuous cocontinuous functor of sites of an injective abelian sheaf is acyclic for evaluation at every object`.
  Eight hits, including `Presheaf.isLocallyInjective_of_whisker`,
  `Presheaf.isLocallyInjective_whisker_iff`, sheaf Grothendieck abelianity,
  and `Functor.isZero_rightDerived_obj_injective_succ`. None asserts this
  statement: locally injective morphisms are a different notion, and the last
  theorem needs injectivity of the object after applying inverse image.
- `msearch.py ... loogle`: `"Sheaf", "Injective", "rightDerived"`.
  Successful query, zero hits.
- `msearch.py ... grep` over `CategoryTheory`:
  `(cocontinuous|Cocontinuous).*(Injective|acyclic)|pre.?limp`.
  One hit: `PreservesLocallyBijective.lean:35`,
  `Presheaf.isLocallyInjective_whisker`; not a cohomological acyclicity result.
- `msearch.py ... leansearch`:
  `Pullback of injective abelian sheaf along continuous cocontinuous functor has zero higher derived evaluation cohomology`.
  Eight hits on sheaf pullbacks and their adjunctions; no acyclicity theorem.
- Direct `rg` in the project's `lean/Sheaf` and upstream `WeilConjectures`
  for the item id and injective/acyclic/cocontinuous terminology: no exact
  statement. Results include injective Cech vanishing and special geometric
  situations such as pro-etale comparison, not this general site theorem.
  `grep -rn` for the exact item id in upstream `WeilConjectures`: no hits.
- Direct `rg` for the proposed full declaration name in Mathlib,
  upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no duplicate declaration.

Validation: `scompile.py Q48 lem-trf-site-pullback-injective-evaluation-acyclic`
compiles the module separately in sandbox and library position. The initial
attempt lacked the Mathlib Grothendieck-category enough-injectives imports;
adding those imports repaired it without adding a hypothesis. The final run
returned exit code 0, with no errors and no warnings (sandbox 3.3 seconds,
library 3.7 seconds). Every variable/universe is explicit and `autoImplicit`
is disabled. The only theorem proof is `by sorry`. All Lean lines are at most
100 characters. The JSON changes only `lean`, with indent 1 and a final newline.

## Second reading by Q48

Author's second pass under direct-delivery policy; independent review belongs
to the maintainer. I compared the unchanged node and Stacks 0D6X/00XR with the
finished signature. The two actual-covering continuity requirements, cocontinuity,
injective target sheaf, arbitrary source object and positive degree all appear.
I specifically checked the variance: `f.op ⋙ I.obj` is a presheaf on C, and its
sheafification is on J, whereas I is on K. The outer derived functor is evaluation
on J-sheaves, not evaluation on K-sheaves and not the derived composite on K.
Thus target injectivity is not inadvertently used to trivialize the conclusion.
I checked that no full-special-cocontinuity, global-pullback, terminal-object,
HasExt or extra size hypothesis entered the signature. No statement mismatch
was found. The compile fix changed only imports. The imported proof criterion's
old interface is a future proof obligation, not an assumption silently added
here. There are no new or repaired dependency nodes to review.
