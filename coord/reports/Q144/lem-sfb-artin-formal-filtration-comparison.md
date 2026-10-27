## Worker report

The item is stated as `AlgebraicGeometry.ArtinDeformation.formal_filtration_comparison`
in `Sheaf.AlgebraicGeometry.ArtinFormalFiltrationComparison`. Every theorem is
postponed with `sorry`; all definition data are explicit. The original item statement,
proof and proof dependencies are unchanged. Its statement dependencies gain exactly
one new definition node, `def-sfb-artin-cofinal-filtration-system`.

Hypothesis and clause correspondence:

- The commutative Noetherian base is `{R : Type u} [CommRing R]
  [IsNoetherianRing R]`. The field of finite type over it is `{k : Type u}
  [Field k] [Algebra R k] [Algebra.FiniteType R k]`. This is the ring-algebra
  specialization of the finite-type notion, using the same spelling as the
  recorded deformation-test interface. It does not require R to be local.
- The marked Artinian category is the recorded `TestCategory R k`. Its underlying
  objects are augmented Artinian local algebras with maximal augmentation kernel;
  its arrows preserve the augmentation and hence are precisely local R-maps
  inducing the identity on the specified residue field. The category cofibred in
  groupoids is `F : CofibredGroupoids.{u, v, w} R k`: the recorded coherent
  pseudofunctor with `IsGroupoid` fibres. No predeformation, RS, descent, smoothness
  or nonemptiness assumption is added.
- `C : CompleteLocalAlgebra R k` is exactly the recorded complete marked
  Noetherian local algebra: it has a `CommAlgCat R` ring, local and Noetherian
  instances, `IsAdicComplete` for its maximal ideal, and the specified residue
  algebra equivalence to k.
- `I : CofinalIdealFiltration C` packages just the filtration assumptions.
  Its `ideal`, `decreasing`, `proper`, `small` and `large` fields encode the
  ideals, decreasing property, properness, and both cofinality directions.
  Index n denotes I_{n+1}; the exponent in `small` and `large` is r+1.
  Properness excludes the zero-ring quotient and makes the residue marking
  meaningful. A cofinality witness with exponent zero could only force the
  ideal to be the whole ring, so positive exponents lose no cases.
- `filtrationTest I n` is the literal C/I_{n+1} with its canonical residue map.
  `filtrationMap I h` is the actual canonical quotient transition. These are
  constructed with `Ideal.Quotient.factorₐ`, not arbitrary choices of test
  algebras or maps. The named theorem `filtration_isTestAlgebra` supplies only
  proof fields for this specified quotient, justified by the proper ideal
  containing a positive maximal-ideal power.
- The source groupoid is `FiltrationSystem I F`. Its `obj` field is u_n, and
  `transition` gives invertible transport comparisons for every n ≤ m.
  `transition_id` is the unit constraint and `transition_comp` is exactly the
  cocycle with the recorded pseudofunctor `compIso` inserted. This is equivalent
  to specifying successive transitions and taking composites; it adds no
  restriction. Arrows are the actual compatible `FiltrationHom` families, with
  the displayed `comm` square and componentwise category operations.
- The target groupoid is the dependency's original `FormalObject F C`, with
  its original `FormalHom` families as arrows. The new filtration-system module
  supplies the componentwise category and groupoid instances as helpers owned
  by the new definition node. The landed dependency record stays byte-identical
  to sheaf-dag. There is no copy of the formal-object notion.
- `∃ E : FiltrationSystem I F ≌ FormalObject F C` asserts the groupoid
  equivalence, including a functor on all compatible arrows, inverse functor,
  and natural unit/counit isomorphisms, rather than a bijection on iso classes.
- The family `e s n A f` asserts that evaluation of the corresponding formal
  object at C → C/I_{n+1} → A is isomorphic to `push F f` of `s.obj n`.
  Evaluation is exactly the dependency's `evaluate`, using the least positive
  nilpotence exponent of A, and not a newly chosen evaluation. The map out of C
  is `filtrationLocalMap I n f`, whose underlying algebra map is literally the
  composite of f and `Ideal.Quotient.mkₐ`.
- In particular, take `A = filtrationTest I n` and `f = 𝟙 _`. Then
  `filtrationLocalMap I n f` is the quotient projection, and `e`, followed by
  the recorded `unitIso`, gives exactly the claimed isomorphism to u_n.
  This case is included in the quantified family, rather than asserted only
  for nonidentity factor maps.
- The first conjunct after `e` states naturality for every compatible arrow
  `a : s ⟶ t`. Its left arrow is evaluation of `E.functor.map a` at the
  nilpotence index of A; its right arrow is transport of `a.app n`. Thus the
  comparisons retain compatibility with all arrows of systems.
- The final conjunct treats every n,m with m ≤ n, every factorization f at n
  and f' at m, and every further test arrow g satisfying
  `f ≫ g = filtrationMap I h ≫ f'`. The right side uses exactly the recorded
  `evaluationRestriction` for the equal composite maps out of C, with equality
  supplied by `filtrationLocalMap_comp`. The left side uses the explicitly
  constructed `filtrationTransportComparison`, namely `compIso`, the square
  equality, inverse `compIso`, and the transported system transition.
  Equality of these arrows is the full transport compatibility, not just the
  existence of unrelated component isomorphisms. Equal indices give further
  transport; identities give change-of-truncation comparisons; setting f and f'
  to identities gives quotient-transition compatibility. Two incomparable
  factorization indices compare through their common larger index. Any local
  marked map a factoring through C/I_n is one of the displayed composites
  (the quotient is surjective, so its factor is unique); equality of underlying
  algebra maps determines `LocalMap`, since locality and marking are Props.
  Finally, a different formal object isomorphic to `E.functor.obj s` inherits
  these comparisons by evaluating that isomorphism.

Dependency declarations opened and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, whose definition
  is `IsNoetherian R R`, and its docstring identifying finitely generated ideals.
- `Mathlib.Algebra.Field.Defs`: `Field` and its full signature/docstring.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  its affine-ring-map signature and finite-type module explanation. For the
  ring-algebra formulation, the existing dependency already imports
  `Mathlib.RingTheory.FiniteType` and uses `Algebra.FiniteType R k`.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`: `TestCategory`,
  `CofibredGroupoids`, `fibre`, `push`, `compIso`, `unitIso`,
  `CompleteLocalAlgebra`, `FormalObject`, `FormalHom`, `LocalMap`,
  `nilpotenceIndex`, `evaluationMap`, `evaluate`, `evaluationFromHigher`,
  `evaluationAtMap_comp`, and `evaluationRestriction`. Their complete source
  signatures and documentation were read; the exact recorded definitions are
  reused. The module is publicly imported by `ArtinCofinalFiltrationSystem`.
- The item's proof leaf is
  `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing` in
  `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`. Its full signature was opened;
  the item imports this module nonpublicly as a proof dependency. Supporting
  quotient-test proof obligations are documented in their owning definition node.

Sources read: the full Tag 06H6 and the preceding definition of the compatible
system category, Tag 06H3, and the recorded dependency source. The current latest
blueprint direct-images proof (3) was read for context. The inherited provenance
has `from.node = null`; `tools/blueprint_refs.py ancestor` returns no ancestor.
The new definition retains this computed value and the inherited explicit place
and via chain, adding this item at the front, without changing the unit route.

Edge cases checked before writing:

- n=0 and r=0 encode positive levels and exponent one; no C/m^0 zero-ring test
  is introduced. `C=k` is valid, with the constant zero ideal filtration.
- Filtrations may repeat or have a zero ideal. No strict descent or nonzero-ideal
  condition is imposed. Constant nonzero ideals in a non-Artinian complete ring
  are correctly excluded by cofinality, not by a stronger condition.
- Empty fibres and an empty system groupoid are allowed. No global object or
  chosen initial deformation is assumed. Arbitrary groupoid fibre universes v,w
  are retained; the base and test-ring size is the dependency's universe u.
- Equal-index and identity-map cases are included in the compatibility equation.
  Identity factorization at the quotient is included. Arbitrary non-surjective
  test arrows f and g are included; only ring quotient projections are used as
  surjections in the constructions.
- For the usual maximal-ideal filtration, the two groupoids have the same
  compatible systems up to the same transport constraints. For a faster or
  repeated cofinal filtration, cofinal reindexing gives the comparisons in the
  proof docstring. No completeness of an arbitrary unrelated diagram is assumed.

Searches made before writing:

- msearch leanfinder: `Compatible systems in groupoids over cofinal ideal
  filtrations equivalent formal objects` returned eight hits on
  `InverseSystem.globalEquiv`, its compatibility, and `Ideal.Filtration`.
  These concern Type-valued systems or ideal filtrations, not the groupoid
  transport equivalence or its evaluation comparisons.
- msearch leansearch: `Equivalence of compatible groupoid systems on cofinal
  ideal filtrations` returned eight hits including `Ideal.Filtration`, direct
  limit congruence, `IsCofiltered.of_equivalence` and eventual-range sections;
  none states this theorem.
- msearch loogle: `"cofinal", "equivalence"` returned zero hits.
- msearch grep: `formalObject|formal_object|[Cc]ofinal.*[Ff]iltration`
  returned zero Mathlib hits.
- The new definition searches are recorded verbatim in its `mathlib_searches`:
  leansearch on compatible deformation objects over cofinal quotients returns
  generic groupoid and local-cohomology module constructions; loogle on
  `"FiltrationSystem"` and grep on
  `FiltrationSystem|CofinalIdealFiltration|filtrationLocalMap` return zero hits.
- rg of `lean/Sheaf` and `lean/WeilConjectures` for these proposed names returns
  zero hits. Searches for the existing formal-object terminology find the exact
  dependency and unrelated representable-diagonal effectivity declarations;
  those were not duplicated. Searching the upstream source for this item's id
  returns no declaration. DAG searches find this comparison theorem and its
  consumers but no node defining cofinal-filtration systems.
  `tools/blueprint_refs.py search filtration-system` returns zero nodes.

Both repaired delivery modules compiled separately through scompile.py against
the published live library, with only the permitted postponed theorem proofs.
The final repair compile reported no errors or warnings (3.6 and 1.5 seconds).
The comparison theorem signature remains exactly the accepted signature from
the returned delivery. No statement correction or disputed clause is needed.

## New nodes

`def-sfb-artin-cofinal-filtration-system` defines the missing source groupoid of
Tag 06H6. Its module `ArtinCofinalFiltrationSystem` contains the cofinal proper
ideal-filtration datum, literal quotient tests and canonical reductions, compatible
objects and arrows, componentwise category/groupoid structure, maps out of C
associated to factorizations, and the comparison for commuting factorization
squares. It cites the existing deformation-test category definition. Its auxiliary
named theorem obligations justify only properties of these explicit constructions;
they carry the same node tag and full proof explanations. The source is the
paragraph immediately preceding Tag 06H6, not a new mathematical assumption.
It also owns the six formal-object category helpers listed in the repair section;
they use the existing formal-object data without modifying its landed node record.
The recorded searches above and in its JSON distinguish it from ideal module
filtrations, generic groupoid constructions, and the existing maximal-ideal formal
object definition.

## Repair of returned delivery cb8c0aa3c89c

H13 is repaired by moving `formalHom_id_comm`, `formalHom_comp_comm`,
`formalObjectCategoryStruct`, `formalObject_category_laws`,
`formalObjectCategory`, and `formalObject_isGroupoid` into
`Sheaf.AlgebraicGeometry.ArtinCofinalFiltrationSystem`. Their signatures and
bodies are unchanged; their blueprint ownership tags now name
`def-sfb-artin-cofinal-filtration-system`. All six are listed in that node's
`lean.declarations`. This is the maintainer-requested placement of the supporting
category structure on the original `FormalObject` and `FormalHom` notions.

`ArtinFormalObjectGroupoid.lean` and its import have been removed from the
sandbox. The sandbox copy of `def-sfb-artin-deformation-test-category.json` was
restored from current sheaf-dag byte for byte, including Q74's author, original
module/file/declaration/signature, reviewer note and `fixed_by`. No dependency
record is rebound or edited by this repair. The dry run builds the repaired
packet on current main through the prescribed delivery wrapper.

The KrullsHeightTheorem import remains a nonpublic proof-dependency import:
its lemma is the recorded Mathlib match of the item's Artinian-quotient proof
leaf. Stage 2 requires these imports even when the postponed proof does not
use them yet (stages/2-statements.md §3, rule 7). It adds no hypothesis or clause.

The maintainer accepted the theorem's mathematical clauses and new definition.
This repair changes declaration placement and metadata ownership only; the
statement and its evaluation/naturality compatibility equations are preserved.

## Second reading by Q144

This section was written by the maintainer's independent stage-2 reviewer (FIX, H11). It replaces the
delivered paragraph, which said that no independent reading had been done. The reading was done against
the node, against Stacks formal-defos.tex (the paragraph defining \hat F_I(R) before Tag 06H6, Tag 06H6
itself, and Tag 06H3), and against the recorded module
Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory as it stands in live/side-live.

Node clauses and their Lean renderings:

1. R is a commutative Noetherian ring, and k is a field of finite type over R. Lean:
   `{R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k] [Algebra.FiniteType R k]`.
   These are the dependency's own binders. R is not assumed to be local. OK.
2. The category C_{R,k}. Lean: the recorded `TestCategory R k`. OK.
3. F is any category cofibred in groupoids. Lean: `F : CofibredGroupoids.{u,v,w} R k`. No
   predeformation, RS or nonemptiness hypothesis is added. OK.
4. C is a complete Noetherian local R-algebra with residue field k. Lean: the recorded
   `CompleteLocalAlgebra R k`. OK.
5. I_1 ⊇ I_2 ⊇ … are proper ideals, cofinal with the powers of m_C in both directions. Lean:
   `CofinalIdealFiltration C` with `Antitone`, `≠ ⊤`, `small` and `large` at exponent r+1, where index n
   means I_{n+1}. An exponent-0 witness would force an ideal to be ⊤, so no case is lost. OK.
6. The groupoid of compatible systems u_n ∈ F(C/I_n), with transitions and compatible arrows. Lean:
   `FiltrationSystem I F` and `FiltrationHom`, with the componentwise category and the IsGroupoid
   instance. This mirrors the recorded `FormalObject` exactly, with `filtrationTest`/`filtrationMap` in
   place of `levelTest`/`levelMap`. The quotients are the literal `Ideal.Quotient.factorₐ`
   constructions. OK.
7. Equivalent to the groupoid of formal objects. Lean: `∃ E : FiltrationSystem I F ≌ FormalObject F C`.
   The category on `FormalObject` is built componentwise from the recorded `FormalHom`; it is now
   placed in the new node's module. OK.
8. The value at C → C/I_n is compatibly isomorphic to u_n. Lean: the case A = filtrationTest I n,
   f = 𝟙 of `e`, composed with `unitIso`. OK.
9. For C → A factoring through C/I_n, ξ_A is compatibly isomorphic to the transport of u_n. Lean:
   `e s n A f`, its naturality in a : s ⟶ t, and the transport-compatibility equation. I checked the
   argument order of `evaluationRestriction` (f : B ⟶ A, a : LocalMap C A, b : LocalMap C B). In the
   item, g : A ⟶ B, a = filtrationLocalMap I m f', b = filtrationLocalMap I n f, and
   hab = filtrationLocalMap_comp. Both sides are arrows
   push g (evaluate ξ (lf n f)) → push f' (s.obj m). Every marked local map factoring through C/I_n
   is some `filtrationLocalMap I n f`: the quotient map is surjective, and `LocalMap` is determined by
   `hom`. OK.

Edge cases checked:
- n = 0 and exponent r+1 (no zero ring).
- The constant zero filtration when C = k.
- Repeated ideals.
- Empty fibres and an empty system groupoid.
- Equal indices and identity f, f', g inside the equation.
- Universes: the rings live in u and the fibres in v, w; nothing is collapsed.

Records:
- The def-sfb-artin-deformation-test-category record is byte-identical to live and side-live. The H13
  of cb8c0aa3 is repaired.
- The six formal-object helpers were moved verbatim; only their blueprint tag changed, to
  def-sfb-artin-cofinal-filtration-system. They are listed in that node's lean.declarations.
- The item's `lean.statement` is a verbatim substring of the module. Its stmt_deps add only the new
  node.
- rg in live/side-live finds no other `Category (FormalObject …)`, `CofinalIdealFiltration` or
  `FiltrationSystem`.

Mismatches: none in the Lean. The only change is this section.
