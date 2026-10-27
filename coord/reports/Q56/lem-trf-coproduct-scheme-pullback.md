## Worker report

The module `Sheaf.AlgebraicGeometry.CoproductSchemePullback` states
`AlgebraicGeometry.Scheme.fppfSheaf_coproduct_scheme_pullback`, with its proof
postponed by `sorry`. No Lean definition or other theorem is introduced. This repair reuses the landed Q75 definition-ownership node without delivering or modifying that node. The statement
and five-step proof were read in the node and checked against `spaces.tex`,
Tags 02WQ, 0F15 and 02WO (the local source, lines 987--1080). No statement
correction, disputed statement or unusable dependency was found.

The previous worker's refusal concerned a completed stage-1 split. This packet
preserves that split and its independent review; it supplies its stage-2 Lean
statement. The sandbox initially held only dispatcher marker files.

Every hypothesis and clause has the following rendering:

- The base scheme is `{S : Scheme.{u}}`; the big fppf site is exactly
  `fppfTopology.over S`, on `Over S`. Schemes, including `Ucop` and test objects,
  therefore belong to the fixed site. All arrows in `Over S` are S-morphisms.
- The small index set is `I : Type (max u v)` and set-valued sheaves are
  `Sheaf (fppfTopology.over S) (Type (max u v))`. The common universe contains
  the scheme morphism universe. No `Small.{u} I` or nonemptiness is assumed;
  the specified scheme coproduct is an object of the site, as required by the
  node. The universe convention is metatheoretic, with no additional object.
- The sheaves, their coproduct and its coprojections are `G`, `C`, `c` and
  `hc : IsColimit (Cofan.mk C c)`. No global sheafification or colimit
  instance is added as a hypothesis.
- The schemes over S are `U : I → Over S`. Their chosen scheme coproduct,
  its inclusions, and its mapping property are `Ucop`, `ιU`, and
  `hU : IsColimit (Cofan.mk Ucop.left (fun i ↦ (ιU i).left))`. Since the
  inclusions are over S, the structural map is the prescribed coproduct map.
- `uliftYoneda.{v}.obj X` is h_X with its Hom sets lifted into the common
  coefficient universe. `pᵢ` and `p` are the given natural transformations;
  `hp` is exactly their restriction equation `h_(ιU i) ≫ p = pᵢ i ≫ (c i).hom`.
  The lift is the canonical Mathlib ULift construction, an equivalence of sets,
  and adds no condition on a test object or a natural transformation.
- The test scheme and section are `T` and `a`. The already landed
  `d : FppfCoproductPartition G T` packages exactly the opens T_i, their
  closedness, pairwise disjointness, covering property, and component sections.
  `hd : d.MapsTo c a` is precisely `c_i(a_i) = a|_(T_i)`. The open subschemes
  and their inclusions are `fppfPartitionOpen T (d.opens i)` and
  `fppfPartitionInclusion T (d.opens i)`.
- The component representing schemes and projections are `V`, `q`, `r`.
  `hV` says their lifted representables are pullbacks of the natural
  transformation associated to `d.sections i` and `pᵢ i`. An `IsPullback`
  includes commutativity and the full universal property, so this is the
  assumed natural representing correspondence, rather than just its equation.
- The conclusion constructs `Vcop : Over S` with inclusions `ιV` and
  `Nonempty (IsColimit (Cofan.mk Vcop.left ...))`: this is the scheme
  coproduct V = coproduct_i V_i. It constructs `Q : Vcop ⟶ T` and
  `R : Vcop ⟶ Ucop`. The first two conjunctions give their restrictions
  `ιV i ≫ Q = q i ≫ inclusion` and `ιV i ≫ R = r i ≫ ιU i`.
- The next conjunction is
  `IsPullback (uliftYoneda.map Q) (uliftYoneda.map R)
    (uliftYonedaEquiv.symm a) p` in presheaves. Limits of presheaves are
  pointwise limits: for each Z this is exactly the bijection between
  Hom_S(Z,Vcop) and pairs (f,b) with af = pb. Its forward map is
  v mapped to (v followed by Q, v followed by R), so the projections are
  the ones just specified. The presheaf universal property includes
  naturality for every test morphism. Removing ULift gives the displayed
  unlifted bijection in the node. This is also precisely the representing
  square used in the dependency's definition of representability; the
  statement makes no algebraic-space claim about G_i.
- Finally the quantifiers over `Z`, `f`, `b`, and their natural-transformation
  equality give, for every compatible pair, equality in `Z.left.Opens`:
  `b.left ⁻¹ᵁ (ιU i).left.opensRange = f.left ⁻¹ᵁ d.opens i`.
  These are actual open subscheme indices, so their associated open subschemes
  coincide, not merely their point sets. To type `opensRange`, the conclusion
  supplies `hιU : ∀ i, IsOpenImmersion (ιU i).left`, already a consequence
  of the scheme coproduct property in the named dependency. This is not an
  additional assumption. No sectionwise monicity, etaleness, surjectivity,
  representable diagonal, or algebraic-space hypothesis is added.

Dependency declarations and imports read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, the schemes and their morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over`. These give exactly the recorded site.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the recorded
  `Precoverage.IsSiteForCoverings` concerns the general site component.
  Its module publicly imports the Mathlib sheaf interfaces used here:
  `Sheaf` is the full subcategory of sheaf presheaves, with natural
  transformations as morphisms. No site axioms are duplicated.
- `Mathlib.CategoryTheory.Limits.HasLimits` and `.Shapes.Products`:
  `Cofan.mk`, `IsColimit`, and the recorded chosen-colimit universal property.
  `IsColimit` is used on the specified coproduct objects instead of choosing
  a second colimit.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and
  `Scheme.Hom.opensRange` give the same open immersion and open subscheme
  notions as `def-weil-open-immersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: the recorded `AlgebraicSpace`
  and `AlgebraicSpace.IsRepresentableWith` define representability by
  scheme-valued `IsPullback` squares. The present theorem uses that exact
  square criterion for the specified test object, with the standard
  Mathlib lifted representables for the larger set universe.
- `Mathlib.AlgebraicGeometry.Limits`: the recorded scheme coproduct
  instance, `sigmaOpenCover`, and `disjoint_opensRange_sigmaι` give the
  coproduct mapping property and its open/disjoint geometry. The theorem
  uses the invariant cofan universal property to retain arbitrary chosen
  coproducts and potentially many empty summands.
- `Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition`:
  `FppfCoproductPartition`, its `MapsTo`, `fppfPartitionOpen`, and
  `fppfPartitionInclusion` are used directly. Its theorem
  `fppfSheaf_coproduct_partition` is the existing proof dependency. The landed Q75
  definition node `def-trf-fppf-coproduct-partition-data` owns the four existing
  definitions and is cited in `stmt_deps`. The theorem stays in `proof_deps`
  only; no copy of its definitions is made.
- `Mathlib.AlgebraicGeometry.Gluing`: `Scheme.Cover.glueMorphisms`,
  `ι_glueMorphisms`, and `hom_ext`, the recorded morphism-gluing proof
  dependency. This import is private because only the future proof needs it.
- `Mathlib.CategoryTheory.Yoneda`: `uliftYoneda` and
  `uliftYonedaEquiv`; `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`:
  `CategoryTheory.IsPullback`. The recorded dependency modules export these.

Edge cases checked before drafting:

- I empty: the assumed coproduct forces Ucop to be empty and the covering
  in d forces T to be empty. Vcop is empty. Hom from an empty test scheme
  has one element on both sides; from a nonempty test scheme both sides
  are empty. The open-equality and summand formulas are vacuous.
- An empty T_i: representability forces V_i to be empty, and compatible
  pairs have empty inverse image of U_i. Empty U_i similarly forces an
  empty V_i. No individual summand is required to be nonempty.
- A singleton family reduces to the assumed representing pullback square.
  For two summands a disconnected test scheme may meet both; `IsPullback`
  quantifies all test schemes and does not require a global choice of label.
- T empty works independently of I. No connectedness, quasi-compactness,
  algebraic-space, etaleness, or surjectivity assumption is present.
- The index type may have more elements than the scheme universe permits
  for unrestricted coproducts. The existing Ucop is assumed, and the Vcop
  coproduct is asserted for this family only. A nonempty V_i maps to T_i,
  so the indices supporting a nonempty V_i inject, after choice, into the
  points of T. The remaining V_i are empty; thus this assertion does not
  require a coproduct of an arbitrary large family of nonempty schemes.

Searches for an existing statement (2026-10-22):

- `msearch.py ... leanfinder`: "Pullback of a map from a scheme coproduct
  to a coproduct of fppf sheaves is represented by the coproduct of component
  scheme pullbacks". Eight hits, including `isPullback_inl_inl_coprodMap`,
  `isPullback_inr_inr_coprodMap`, scheme-pullback gluing declarations, and
  `Scheme.LocalRepresentability.glueData_V`. None states the arbitrary
  fppf-sheaf comparison. The binary scheme coproduct square and Zariski
  local-representability sources were examined.
- `msearch.py ... loogle`: `CategoryTheory.Sheaf, CategoryTheory.Limits.IsPullback`.
  The service reported an unknown identifier for the incorrectly qualified
  IsPullback; this result is not evidence of absence. The actual declaration
  is `CategoryTheory.IsPullback`, read in Mathlib's IsPullback/Defs module.
  Retrying with `CategoryTheory.Sheaf, CategoryTheory.IsPullback` returned two
  hits, `Sheaf.isPullback_χ_truth` and `Sheaf.χ_unique`; both concern the
  subobject classifier, rather than coproduct scheme pullbacks.
- `msearch.py ... leansearch`: "A scheme coproduct represents the fibre
  product of a coproduct of fppf sheaves with a test scheme with its clopen
  partition". Eight hits: scheme coproduct existence, `sigmaMk`, binary
  coproduct geometry, and `Scheme.coprodPresheafObjIso`. The last concerns
  structure-sheaf sections on a scheme coproduct, not this comparison.
- `msearch.py ... grep`, query
  `coproduct.*pullback|pullback.*coproduct|coprodPresheafObjIso`, restricted
  to Mathlib `AlgebraicGeometry`: eight hits in scheme coproduct geometry,
  structure-sheaf sections and the big Zariski site; none is the item.
- `rg -n` in `lean/WeilConjectures` and `lean/Sheaf`, query
  `lem-trf-coproduct-scheme-pullback|coproduct.*pullback|coproduct.*Pullback`:
  nearby finite-etale, module, derived-category and algebraic-space gluing
  material, but no exact statement. Direct searches for the chosen declaration
  and item id in both trees and `dag/lean_names_upstream.json` found no match.
- The statement dependencies were read from their node records and their
  source declarations. The landed clopen-partition record is reusable;
  the landed Q75 definition node now provides its ownership. The prescribed compact-object
  example currently contains only a withdrawn-module notice, so the live
  partition module supplied the project header and module-mode example.

Validation: `scompile.py Q56 lem-trf-coproduct-scheme-pullback` compiled
the single delivered file in both its sandbox and module-path checks, each
in 2.1 seconds, with no errors or unexpected warnings. The initial parser
error from a Sigma symbol in an identifier was repaired before this clean run.
All universes are explicit and `autoImplicit` is disabled.


## Repair of return L

The independent review of immutable head `df76bded9df5` returned this packet
because `def-trf-fppf-coproduct-partition-data` now exists on `sheaf-dag` from
another delivery. The required initial dry run confirmed that the saved copy
would modify the landed node's `lean` record, rather than add a new node, and
rejected that dependency edit for lacking a dependency-modules report.

I compared both copies and the published source. The live Q75 node owns exactly
the four definitions this theorem uses: `fppfPartitionOpen`,
`fppfPartitionInclusion`, `FppfCoproductPartition`, and
`FppfCoproductPartition.MapsTo`, all in the published module
`Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition`. Its primary signature is
identical to the saved ownership signature. Its statement gives precisely the
clopen-cover data, component sections and component-image predicate; it adds no
partition-existence or uniqueness assertion. Its interface is usable unchanged.

I removed the duplicate definition-node JSON from the sandbox delivery. The item
retains `def-trf-fppf-coproduct-partition-data` in `stmt_deps`, now referring to
that landed node. The item module and mathematical statement are retained.
The item node differs from the live node only in `lean` and the addition of this
landed definition to `stmt_deps`. No new node or dependency repair is delivered;
no other group's node or attribution is overwritten. `deliver2.py` constructs
the repaired commit on the current server base.

## Second reading by Q56

I performed the required self-check without starting another agent. I reread
the retained theorem, its node statement, the live Q75 ownership node and the
four full published definitions. The partition data and `MapsTo` equation are
identical to those used in the saved statement. The imports already use their
published module. Only the ownership attachment has changed; the theorem's
hypotheses and conclusions retain the clause-by-clause correspondence above.
In particular `hV` gives each component representing pullback; the existential
cofan gives the scheme coproduct; `Q` and `R` have the specified restrictions;
the concluding `IsPullback` is the natural representing bijection; and the final
open equality applies to every compatible pair. The empty-index, empty-piece,
singleton and large-index checks above remain applicable. There is no statement
correction or disputed statement.

Repair validation: `scompile.py` compiled the retained single module in sandbox
mode (2.4 s) and module-path mode (2.0 s), with no errors or unexpected warnings.
The saved JSON signature matches the source verbatim. The self-check confirmed
that only the item's `lean` and `stmt_deps` differ from the live node, the only
added dependency is the landed partition-data node, and that node is absent
from this delivery. All Lean lines satisfy the 100-character limit.
