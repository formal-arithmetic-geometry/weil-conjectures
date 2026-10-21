## Worker report

This delivery states the derived restriction calculus for arbitrary topological groups,
commutative internal condensed coefficient rings, and ordinary unbounded derived categories.
The primary module is `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`.
Five supporting definition nodes supply the previously absent normalized constructions;
there is no change to the item's statement or proof. All mathematical proof obligations
remain named theorems with `sorry`, source references, and natural-language proof docstrings.
Definitions have actual data or use a universal property fixing the object up to the
specified unique comparison; no unconstrained map or tensor structure is substituted.

Hypotheses and clauses, in the order of the node:

- The coefficient `A : CondensedBar.Ring.{u}` is the existing `CommMon` bundle on
  `Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1}`. Its underlying monoid is
  exactly `A.toMon : Profinite.CondensedRing`; its bundled commutativity is the existing
  `CondensedBar.ringComm`. Thus this is every commutative condensed ring, including the zero
  ring. `CondensedBar.Modules` is the recorded internal module category, not a separate
  sectionwise replacement. Universe `u+1` for derived morphisms is supplied by the
  Grothendieck category size convention; no site universes are identified.
- `G H : Type u` carry only `Group`, `TopologicalSpace`, `IsTopologicalGroup`. There is no
  compactness, Hausdorffness, discreteness, profiniteness, or torsion assumption. Existing
  `Profinite.CondensedAction.ActionModule` uses all sections `C(S,G)` and every profinite
  base change, exactly the action notion of the dependency. `invariants` chooses the
  existing normalized `Invariants` specification; its injectivity, image `FixedAll`,
  transpose and inverse transpose fields fix the required invariant inclusion.
- `actionAbelianData`, `actionGrothendieck`, and `forgetExact` give the abelian and
  Grothendieck structures and exactness detection. The unchanged underlying kernels and
  cokernels with their induced actions render the finite limit/colimit preservation in
  `forgetExact`. `trivialAdditive`, `trivialLimits`, `trivialColimits` state exact trivial
  inflation. Its adjunction is the recorded normalized invariant-inclusion adjunction.
- `derived` is the generic ordinary total `Functor.rightDerivedFunctor`, not continuous
  cochains. `adjunction` is the generic derived adjunction of that very underived
  adjunction. `boundedBelowComputation` states invertibility of the actual computation
  unit on bounded-below equivariant injective complexes; any injective resolution then
  computes by quasi-isomorphism. `derivedProperties`, `derivedShift`, `derivedTriangulated`
  retain additivity, canonical integer shifts and distinguished triangles.
- For `v : H →ₜ* G`, `inflate` is the recorded exact restriction. Its additivity and exactness
  are stated explicitly. `invariantRestrictionExist` fixes the ordinary map uniquely by
  composition with the invariant inclusions. `restriction` uses the existing canonical
  `Functor.rightDerivedPullback`. `groupMapNormalization` is its computation-unit equation
  on every complex. Natural transformation types give naturality for every equivariant
  morphism. `groupMapShift` is `NatTrans.CommShift`; together with triangulated functors
  and naturality at the triangle's last arrow this includes connecting morphisms.
  `degreeZero` and `degreeZeroIso` fix the single/H0 identification through the computation
  unit; `restrictionDegreeZero` explicitly identifies H0 of the restriction arrow with
  the ordinary invariant inclusion.
  `identityRestriction` uses the normalized exact-localization identity comparison and
  has `[Subsingleton G]`, giving precisely the two trivial groups with the identity homomorphism.
- For arbitrary `φ : A ⟶ A'`, `scalarAction` is the existing scalar-action specification,
  including its underlying internal-module scalar restriction and its action equation.
  `scalarExact`, `scalarLimits`, `scalarColimits` give exactness. `scalarInvariants` is
  fixed by the invariant inclusions. `scalarComparison` is the unique derived
  isomorphism with that underived comparison's computation-unit equation on every
  complex. `coefficientMap φ f` is derived invariants of `f` followed by this isomorphism.
  The hypothesis `f : N ⟶ (scalarDerived φ G).obj N'` permits all derived equivariant maps,
  including modules in degree zero. `coefficientSquare` is the actual equality of arrows
  in the ordinary derived category, using the normalized scalar/group commutation
  isomorphism. No flatness or injective-preservation hypothesis is present.
- `coefficient` is the actual trivial regular module in degree zero; `cohomology` is its
  ordinary derived invariant object. The diagonal tensor has the ordinary underlying
  relative module tensor, the actual diagonal section action and normalized symmetry.
  The ordinary trivial-action tensor comparison is identity on underlying modules.
  Its derived tensorator uses the existing generic flat-term K-flat normalization
  `Functor.rightExactTensorModelNormalization`, and its unit is fixed by localization
  of the ordinary regular unit. `derivedLax` is the actual adjoint-mate lax structure.
  `coefficientMultiply`, `cup`, `cupUnit` therefore give precisely multiplication in R
  followed by that lax pairing. `cupLaws` states associativity and both unit laws.
- `Character` is exactly an additive condensed-group map: its section values, identity,
  product-to-sum law, and naturality quantify over every profinite test object. Its
  restriction and coefficient compositions are fixed uniquely by their actual section
  values. `UnipotentAction` is on the fixed actual biproduct R ⊞ R; the two coordinate
  equations fix its linear action uniquely. `extensionInclusion` and `extensionProjection` give the typed first inclusion
  and second projection; `extensionSequence` uses them with trivial endpoints; `extensionExact` gives short exactness.
  `extensionPositive` states j(0,1) - (0,1) = (a(j),0) on every test object, fixing the
  requested positive inhomogeneous cocycle. `classShifted` applies the cup/invariant
  unit to the canonical `ShortComplex.ShortExact.singleδ`, then the canonical shift
  comparison; `characterClass` shifts this down, so its source is exactly R[0][-1].
- `restrictionClass` sends this class to the actual precomposed character. `restrictionCup`
  preserves the binary pairing and unit. `restrictionOrderedProducts` retains the ordered
  right-associated tensor-power multiplication for every natural length, including zero.
  Tensoring any list of shifted class maps into these powers gives all ordered graded
  cup products, without permuting factors.
- `regularScalar`, `coefficientArrow` and `coefficientCupMap` retain the original ring map
  φ as the coefficient map. Scalar tensor comparison is normalized on actual balanced
  pure tensors and the derived localization equation; it uses K-flat representatives
  over R', never assumes scalar restrictions remain R-flat. `restrictedCup` and
  `restrictedCupUnit` are the canonical lax scalar product and unit. `coefficientCup`
  gives their preservation, and `coefficientOrderedProducts` gives all finite ordered
  products including length zero. `coefficientClass` includes the shifted original
  regular scalar arrow and inverse scalar shift comparison in its domain; thus it says
  exactly that the class goes to φ composed with a, without silently identifying R and R'.
- No continuous-cochain acyclicity assertion occurs.

Recorded dependencies used: `Mathlib.CategoryTheory.Monoidal.Mod` (`CategoryTheory.Mod`);
`Sheaf.Topology.ProfiniteCondensedRing`/the recorded condensed ring bundle;
`Sheaf.CategoryTheory.CondensedActionModule` (`ActionModule`, `inflate`, `trivial`,
`Invariants`, `FixedAll`, normalized inclusion and transpose fields);
`Sheaf.CategoryTheory.CondensedEquivariantBarData` (`Ring`, `Modules`, `sections`,
`sectionRing`, `ActionAbelian`, `ScalarAction` only, with no profinite bar model assumed);
`Mathlib.Algebra.Homology.DerivedCategory.Basic` (`DerivedCategory`, `HasDerivedCategory`);
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` (`IsGrothendieckAbelian`);
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`
(`rightDerivedPullback`, `rightDerivedFunctorUnitQ`);
`RightDerivedFunctor.AdjunctionShift` (canonical derived adjunction);
`RightDerivedFunctor.Additive` and `.Triangulated` (canonical properties);
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory` (ordinary derived tensor);
`Sheaf.CategoryTheory.DerivedTensorRightExact`
(`Functor.rightExactTensorModelNormalization`, existing node
`lem-derived-right-exact-tensor-comparison`);
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Map` (`ShortComplex.ShortExact.singleδ`).
All signatures and docstrings of the recorded statement dependencies were read.

Edge cases checked mathematically: the zero ring and zero modules; zero character
(the split sequence gives zero connecting class); trivial groups and identity
homomorphism; noncompact and non-Hausdorff topological groups; the empty profinite test
object; arbitrary nonflat coefficient quotient (e.g. Z to Z/n); noninjective group maps;
length zero products; and the genuinely different source rings in coefficient-class
change. No edge case requires an extra hypothesis. The action-site descent only uses
that the finite profinite covering map is a quotient map between compact Hausdorff
spaces; it does not impose separation on the target group.

Searches: `msearch.py` LeanSearch on normalized derived internal invariants returned
ordinary module/presheaf/sheaf scalar restriction and unrelated analytic scalar maps;
LeanFinder on derived tensor cup products returned light-condensed constant-ring tensor
instances, not arbitrary internal rings and actions; Loogle on expected unipotent/cup
names returned zero hits; Mathlib grep on `(UnipotentAction|CondensedDerived|condensed.*cup)`
returned zero. Local `rg` over both WeilConjectures and Sheaf found the recorded action
and bar-data APIs and unrelated derived-tensor imports. DAG searches and
`blueprint_refs.py search` found consumers and geometric cup notions, not these
constructions. All actual msearch outcomes, queries and digests are copied to the
new nodes' `mathlib_searches`. The generic right-exact tensor normalization was found
and reused instead of a private copy. There is no exact existing declaration for the
whole item. No `STATEMENT-DISPUTED` finding and no statement correction.

## New nodes

`def-sfb-condensed-derived-invariants`: the canonical fixed-section total derived functors,
exact group/scalar restrictions, their normalized comparisons and coefficient arrows.
Source: the item's paragraph (3) formal-infrastructure expansion and its detailed proof.
The ordinary action and generic derived nodes give the ingredients but no such
normalized internal-action construction. Uses those recorded declarations.

`def-sfb-condensed-derived-cup`: the K-flat derived comparison of strong
trivial-action tensor, actual regular coefficient algebra,
adjoint-mate cup pairing, unit, restriction arrow, and ordered tensor-power products.
Source: paragraph (3), expanded proof steps 8–10. Search results above distinguish the
constant-ring light-condensed and geometric cup constructions. The existing generic
right-exact tensor comparison predicate is reused through `exactTensorNormalization`,
which shares its generic elaboration before specialization to condensed modules.

`def-sfb-condensed-scalar-tensor`: the balanced ordinary scalar tensor, its normalized
complex and derived lax comparisons, and the actual regular coefficient map. Source:
paragraph (3), expanded proof steps 6 and 10. General `Mod.comap` is reused; the missing
lax comparisons retain nonflat coefficient maps and actual section formulas.

`def-sfb-condensed-unipotent-class`: additive condensed characters, actual precomposition
and coefficient composition, the uniquely specified action on R ⊞ R, the exact sequence,
positive splitting normalization, and its shifted connecting class. Source: paragraph
(3), expanded proof steps 11–12. Searches found no such internal arbitrary-group
unipotent class. This is a definition of the source-specified extension, not a bare
choice of a cohomology class or an unconstrained connecting map.

The localized regular-unit comparison reuses
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit`,
`DerivedCategory.isIso_ε_Qh`, through an abstract-category helper. Small coproducts for
total tensor are the existing Grothendieck category colimits shrunk to size zero; they
are explicitly exposed for both base modules and actions.

The ordinary diagonal action tensor is owned by the additional definition node
`def-sfb-condensed-action-tensor`, module
`Sheaf.CategoryTheory.CondensedActionTensor`. It specifies the existing relative
internal-module tensor under the forgetful comparison, its diagonal generalized
pure-tensor action, its ordinary symmetry and unit, and the canonical trivial
inflation tensor comparison. This notion is distinct from the derived cup product
built from its adjoint mate. The searches above found no existing node or public
project declaration providing this normalized action tensor.

Additional `msearch.py grep` query
`ActionTensorData|CondensedAction.*[Mm]onoidal|action.*diagonal.*tensor` returned three
ordinary representation-theory hits in `Homological/Resolution.lean` and `Rep/Iso.lean`;
none defines a tensor on internal condensed action modules.

Validation: all six delivered modules compiled separately, in dependency order,
through the prescribed `scompile.py` server wrapper against the published live library.
The successful run had no errors or unexpected warnings. The primary calculus module
compiled in 46.0 seconds; supporting library modules compiled in 10.4–30.2 seconds.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
